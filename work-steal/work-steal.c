/* A work-stealing scheduler is described in
 * Robert D. Blumofe, Christopher F. Joerg, Bradley C. Kuszmaul, Charles E.
 * Leiserson, Keith H. Randall, and Yuli Zhou. Cilk: An efficient multithreaded
 * runtime system. In Proceedings of the Fifth ACM SIGPLAN Symposium on
 * Principles and Practice of Parallel Programming (PPoPP), pages 207-216,
 * Santa Barbara, California, July 1995.
 * http://supertech.csail.mit.edu/papers/PPoPP95.pdf
 *
 * However, that refers to an outdated model of Cilk; an update appears in
 * the essential idea of work stealing mentioned in Leiserson and Platt,
 * Programming Parallel Applications in Cilk
 */

#include <assert.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <unistd.h>
#include <err.h>
#include <sys/resource.h>
#include <sys/time.h>

struct work_internal;

/* A 'task_t' represents a function pointer that accepts a pointer to a 'work_t'
 * struct as input and returns another 'work_t' struct as output. The input to
 * this function is always a pointer to the encompassing 'work_t' struct.
 *
 * It is worth considering whether to include information about the executing
 * thread's identifier when invoking the task. This information might be
 * beneficial for supporting thread-local accumulators in cases of commutative
 * reductions. Additionally, it could be useful to determine the destination
 * worker's queue for appending further tasks.
 *
 * The 'task_t' trampoline is responsible for delivering the subsequent unit of
 * work to be executed. It returns the next work item if it is prepared for
 * execution, or NULL if the task is not ready to proceed.
 */
typedef struct work_internal *(*task_t)(struct work_internal *);

typedef struct work_internal {
    task_t code;
    atomic_int join_count;
    void *args[];
} work_t;

/* These are non-NULL pointers that will result in page faults under normal
 * circumstances, used to verify that nobody uses non-initialized entries.
 */
static work_t *EMPTY = (work_t *) 0x100, *ABORT = (work_t *) 0x200;

/* work_t-stealing deque */

typedef struct {
    atomic_size_t size;
    _Atomic work_t *buffer[];
} array_t;

typedef struct {
    /* Assume that they never overflow */
    atomic_size_t top, bottom;
    _Atomic(array_t *) array;
} deque_t;

#ifndef ELEM_T
#define ELEM_T uint32_t
#endif

void init(deque_t *q, int size_hint)
{
    atomic_init(&q->top, 0);
    atomic_init(&q->bottom, 0);
    array_t *a = malloc(sizeof(array_t) + sizeof(work_t *) * size_hint);
    atomic_init(&a->size, size_hint);
    atomic_init(&q->array, a);
}

void resize(deque_t *q)
{
    array_t *a = atomic_load_explicit(&q->array, memory_order_relaxed);
    size_t old_size = a->size;
    size_t new_size = old_size * 2;
    array_t *new = malloc(sizeof(array_t) + sizeof(work_t *) * new_size);
    atomic_init(&new->size, new_size);
    size_t t = atomic_load_explicit(&q->top, memory_order_relaxed);
    size_t b = atomic_load_explicit(&q->bottom, memory_order_relaxed);
    for (size_t i = t; i < b; i++)
        new->buffer[i % new_size] = a->buffer[i % old_size];

    atomic_store_explicit(&q->array, new, memory_order_relaxed);
    /* The question arises as to the appropriate timing for releasing memory
     * associated with the previous array denoted by *a. In the original Chase
     * and Lev paper, this task was undertaken by the garbage collector, which
     * presumably possessed knowledge about ongoing steal operations by other
     * threads that might attempt to access data within the array.
     *
     * In our context, the responsible deallocation of *a cannot occur at this
     * point, as another thread could potentially be in the process of reading
     * from it. Thus, we opt to abstain from freeing *a in this context,
     * resulting in memory leakage. It is worth noting that our expansion
     * strategy for these queues involves consistent doubling of their size;
     * this design choice ensures that any leaked memory remains bounded by the
     * memory actively employed by the functional queues.
     */
}

work_t *take(deque_t *q)
{
    size_t b = atomic_load_explicit(&q->bottom, memory_order_relaxed) - 1;
    array_t *a = atomic_load_explicit(&q->array, memory_order_relaxed);
    atomic_store_explicit(&q->bottom, b, memory_order_relaxed);
    atomic_thread_fence(memory_order_seq_cst);
    size_t t = atomic_load_explicit(&q->top, memory_order_relaxed);
    work_t *x;
    if (t <= b) {
        /* Non-empty queue */
        x = atomic_load_explicit(&a->buffer[b % a->size], memory_order_relaxed);
        if (t == b) {
            /* Single last element in queue */
            if (!atomic_compare_exchange_strong_explicit(&q->top, &t, t + 1,        // Mask - AAA => t + 1
                                                         memory_order_seq_cst,
                                                         memory_order_relaxed))
                /* Failed race */
                x = EMPTY;
            atomic_store_explicit(&q->bottom, b + 1, memory_order_relaxed);         // Mask - BBBB => b + 1
        }
    } else { /* Empty queue */
        x = EMPTY;
        atomic_store_explicit(&q->bottom, b + 1, memory_order_relaxed);             // Mask - CCCC => b + 1
    }
    return x;
}

void push(deque_t *q, work_t *w)
{
    size_t b = atomic_load_explicit(&q->bottom, memory_order_relaxed);
    size_t t = atomic_load_explicit(&q->top, memory_order_acquire);
    array_t *a = atomic_load_explicit(&q->array, memory_order_relaxed);
    if (b - t > a->size - 1) { /* Full queue */
        resize(q);
        a = atomic_load_explicit(&q->array, memory_order_relaxed);
    }
    atomic_store_explicit(&a->buffer[b % a->size], w, memory_order_relaxed);
    atomic_thread_fence(memory_order_release);
    atomic_store_explicit(&q->bottom, b + 1, memory_order_relaxed);                 // Mask - DDDD => b + 1
}

work_t *steal(deque_t *q)
{
    size_t t = atomic_load_explicit(&q->top, memory_order_acquire);
    atomic_thread_fence(memory_order_seq_cst);
    size_t b = atomic_load_explicit(&q->bottom, memory_order_acquire);
    work_t *x = EMPTY;
    if (t < b) {
        /* Non-empty queue */
        array_t *a = atomic_load_explicit(&q->array, memory_order_consume);
        x = atomic_load_explicit(&a->buffer[t % a->size], memory_order_relaxed);
        if (!atomic_compare_exchange_strong_explicit(
                &q->top, &t, t + 1, memory_order_seq_cst, memory_order_relaxed))    // Mask - EEEE => t + 1
            /* Failed race */
            return ABORT;
    }
    return x;
}

#define N_THREADS 24
deque_t *thread_queues;

atomic_bool done;

/* Returns the subsequent item available for processing, or NULL if no items
 * are remaining.
 */
static work_t *do_one_work(int id, work_t *work)
{
    printf("work item %d running item %p\n", id, work);
    return (*(work->code)) (work);
}

void do_work(int id, work_t *work)
{
    while (work)
        work = do_one_work(id, work);
}

/* Returns the next item to be processed, or NULL if there are no remaining
 * items.
 */
work_t *join_work(work_t *work)
{
    int old_join_count = atomic_fetch_sub(&work->join_count, 1);
    if (old_join_count == 1)
        return work;
    return NULL;
}

void *thread(void *payload)
{
    int id = *(int *) payload;
    deque_t *my_queue = &thread_queues[id];
    while (true) {
        work_t *work = take(my_queue);
        if (work != EMPTY) {
            do_work(id, work);
        } else {
            /* Currently, there is no work present in my own queue */
            work_t *stolen = EMPTY;
            for (int i = 0; i < N_THREADS; ++i) {
                if (i == id)
                    continue;
                stolen = steal(&thread_queues[i]);
                if (stolen == ABORT) {
                    i--;
                    continue; /* Try again at the same i */
                } else if (stolen == EMPTY)
                    continue;

                /* Found some work to do */
                break;
            }
            if (stolen == EMPTY) {
                /* Despite the previous observation of all queues being devoid
                 * of tasks during the last examination, there exists
                 * a possibility that additional work items have been introduced
                 * subsequently. To account for this scenario, a state of active
                 * waiting is adopted, wherein the program continues to loop
                 * until the global "done" flag becomes set, indicative of
                 * potential new work additions.
                 */
                if (atomic_load(&done))
                    break;
                continue;
            } else {
                do_work(id, stolen);
            }
        }
    }
    printf("work item %d finished\n", id);
    return NULL;
}

// work_t *print_task(work_t *w)
// {
//     int *payload = (int *) w->args[0];
//     int item = *payload;
//     printf("Did item %p with payload %d\n", w, item);
//     work_t *cont = (work_t *) w->args[1];
//     free(payload);
//     free(w);
//     return join_work(cont);
// }

/* Thread-callable quicksort. */
static void qsort_algo(struct qsort *qs)
{
    char *pa, *pb, *pc, *pd, *pl, *pm, *pn;
    int d, r, swaptype, swap_cnt;
    void *a;      /* Array of elements. */
    size_t n, es; /* Number of elements; size. */
    cmp_t *cmp;
    int nl, nr;
    struct common *c;
    struct qsort *qs2;

    /* Initialize qsort arguments. */
    c = qs->common;
    es = c->es;
    cmp = c->cmp;
    swaptype = c->swaptype;
    a = qs->a;
    n = qs->n;
top:
    /* From here on qsort(3) business as usual. */
    swap_cnt = 0;
    if (n < 7) {
        for (pm = (char *) a + es; pm < (char *) a + n * es; pm += es)
            for (pl = pm; pl > (char *) a && CMP(thunk, pl - es, pl) > 0;
                 pl -= es)
                swap(pl, pl - es);
        return;
    }
    pm = (char *) a + (n / 2) * es;
    if (n > 7) {
        pl = (char *) a;
        pn = (char *) a + (n - 1) * es;
        if (n > 40) {
            d = (n / 8) * es;
            pl = med3(pl, pl + d, pl + 2 * d, cmp, thunk);
            pm = med3(pm - d, pm, pm + d, cmp, thunk);
            pn = med3(pn - 2 * d, pn - d, pn, cmp, thunk);
        }
        pm = med3(pl, pm, pn, cmp, thunk);
    }
    swap(a, pm);
    pa = pb = (char *) a + es;

    pc = pd = (char *) a + (n - 1) * es;
    for (;;) {
        while (pb <= pc && (r = CMP(thunk, pb, a)) <= 0) {
            if (r == 0) {
                swap_cnt = 1;
                swap(pa, pb);
                pa += es;
            }
            pb += es;
        }
        while (pb <= pc && (r = CMP(thunk, pc, a)) >= 0) {
            if (r == 0) {
                swap_cnt = 1;
                swap(pc, pd);
                pd -= es;
            }
            pc -= es;
        }
        if (pb > pc)
            break;
        swap(pb, pc);
        swap_cnt = 1;
        pb += es;
        pc -= es;
    }

    pn = (char *) a + n * es;
    r = min(pa - (char *) a, pb - pa);
    vecswap(a, pb - r, r);
    r = min(pd - pc, pn - pd - es);
    vecswap(pb, pn - r, r);

    if (swap_cnt == 0) { /* Switch to insertion sort */
        r = 1 + n / 4;   /* n >= 7, so r >= 2 */
        for (pm = (char *) a + es; pm < (char *) a + n * es; pm += es)
            for (pl = pm; pl > (char *) a && CMP(thunk, pl - es, pl) > 0;
                 pl -= es) {
                swap(pl, pl - es);
                if (++swap_cnt > r)
                    goto nevermind;
            }
        return;
    }

nevermind:
    nl = (pb - pa) / es;
    nr = (pd - pc) / es;

    /* Now try to launch subthreads. */
    if (nl > c->forkelem && nr > c->forkelem &&
        (qs2 = allocate_thread(c)) != NULL) {
        qs2->a = a;
        qs2->n = nl;
        verify(pthread_cond_signal(&qs2->cond_st));
        verify(pthread_mutex_unlock(&qs2->mtx_st));
    } else if (nl > 0) {
        qs->a = a;
        qs->n = nl;
        qsort_algo(qs);
    }
    if (nr > 0) {
        a = pn - nr * es;
        n = nr;
        goto top;
    }
}

work_t *done_task(work_t *w)
{
    free(w);
    atomic_store(&done, true);
    return NULL;
}

int main(int argc, char **argv)
{
    bool opt_str = false;
    bool opt_time = false;
    bool opt_verify = false;
    bool opt_libc = false;
    int ch;
    size_t nelem = 10000000;
    int maxthreads = 2;
    int forkelements = 100;
    ELEM_T *int_elem;
    char *ep;
    char **str_elem;
    struct timeval start, end;
    struct rusage ru;

    gettimeofday(&start, NULL);
    while ((ch = getopt(argc, argv, "f:h:ln:stv")) != -1) {
        switch (ch) {
        case 'f':
            forkelements = (int) strtol(optarg, &ep, 10);
            if (forkelements <= 0 || *ep != '\0') {
                warnx("illegal number, -f argument -- %s", optarg);
                usage();
            }
            break;
        case 'h':
            maxthreads = (int) strtol(optarg, &ep, 10);
            if (maxthreads < 0 || *ep != '\0') {
                warnx("illegal number, -h argument -- %s", optarg);
                usage();
            }
            break;
        case 'l':
            opt_libc = true;
            break;
        case 'n':
            nelem = (size_t) strtol(optarg, &ep, 10);
            if (nelem == 0 || *ep != '\0') {
                warnx("illegal number, -n argument -- %s", optarg);
                usage();
            }
            break;
        case 's':
            opt_str = true;
            break;
        case 't':
            opt_time = true;
            break;
        case 'v':
            opt_verify = true;
            break;
        case '?':
        default:
            usage();
        }
    }

    if (opt_verify && opt_str)
        usage();

    argc -= optind;
    argv += optind;

    if (opt_str) {
        str_elem = xmalloc(nelem * sizeof(char *));
        for (int i = 0; i < nelem; i++)
            if (asprintf(&str_elem[i], "%d%d", rand(), rand()) == -1) {
                perror("asprintf");
                exit(1);
            }
    } else {
        int_elem = xmalloc(nelem * sizeof(ELEM_T));
        for (int i = 0; i < nelem; i++)
            int_elem[i] = rand() % nelem;
    }

    /* Check that top and bottom are 64-bit so they never overflow */
    static_assert(sizeof(atomic_size_t) == 8,
                  "Assume atomic_size_t is 8 byte wide");

    pthread_t threads[N_THREADS];
    int tids[N_THREADS];
    thread_queues = malloc(N_THREADS * sizeof(deque_t));
    int nprints = 10;

    atomic_store(&done, false);
    work_t *done_work = malloc(sizeof(work_t));
    done_work->code = &done_task;
    done_work->join_count = N_THREADS * nprints;

    for (int i = 0; i < N_THREADS; ++i) {
        tids[i] = i;
        init(&thread_queues[i], 8);
        for (int j = 0; j < nprints; ++j) {
            work_t *work = malloc(sizeof(work_t) + 2 * sizeof(int *));
            work->code = &qsort_algo;
            work->join_count = 0;
            int *payload = malloc(sizeof(int));
            *payload = 1000 * i + j;
            work->args[0] = payload;
            work->args[1] = done_work;
            push(&thread_queues[i], work);
        }
    }

    for (int i = 0; i < N_THREADS; ++i) {
        if (pthread_create(&threads[i], NULL, thread, &tids[i]) != 0) {
            perror("Failed to start the thread");
            exit(EXIT_FAILURE);
        }
    }

    for (int i = 0; i < N_THREADS; ++i) {
        if (pthread_join(threads[i], NULL) != 0) {
            perror("Failed to join the thread");
            exit(EXIT_FAILURE);
        }
    }
    printf("Expect %d lines of output (including this one)\n",
           2 * N_THREADS * nprints + N_THREADS + 2);

    gettimeofday(&end, NULL);
    getrusage(RUSAGE_SELF, &ru);
    if (opt_verify) {
        for (i = 1; i < nelem; i++)
            if (int_elem[i - 1] > int_elem[i]) {
                fprintf(stderr,
                        "sort error at position %d: "
                        " %d > %d\n",
                        i, int_elem[i - 1], int_elem[i]);
                exit(2);
            }
    }
    if (opt_time)
        printf(
            "%.3g %.3g %.3g\n",
            (end.tv_sec - start.tv_sec) + (end.tv_usec - start.tv_usec) / 1e6,
            ru.ru_utime.tv_sec + ru.ru_utime.tv_usec / 1e6,
            ru.ru_stime.tv_sec + ru.ru_stime.tv_usec / 1e6);
    return (0);

    return 0;
}
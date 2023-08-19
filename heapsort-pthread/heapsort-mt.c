#include <assert.h>
#include <errno.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <err.h>
#include <sys/resource.h>
#include <sys/time.h>
#include <unistd.h>

#ifndef ELEM_T
#define ELEM_T uint32_t
#endif

#ifndef thunk
#define thunk NULLx
#endif

bool _debugmod = false;

#define verify(x)                                                      \
    do {                                                               \
        int e;                                                         \
        if ((e = x) != 0) {                                            \
            fprintf(stderr, "%s(%d) %s: %s\n", __FILE__, __LINE__, #x, \
                    strerror(e));                                      \
            exit(1);                                                   \
        }                                                              \
    } while (0)

typedef int cmp_t(const void *, const void *);
static inline char *med3(char *, char *, char *, cmp_t *, void *);
static inline void swapfunc(char *, char *, int, int);

#define min(a, b)           \
    ({                      \
        typeof(a) _a = (a); \
        typeof(b) _b = (b); \
        _a < _b ? _a : _b;  \
    })

/* Heapsort routine from Bentley & McIlroy's "Engineering a Sort Function" */
#define swapcode(TYPE, parmi, parmj, n) \
    {                                   \
        long i = (n) / sizeof(TYPE);    \
        TYPE *pi = (TYPE *) (parmi);    \
        TYPE *pj = (TYPE *) (parmj);    \
        do {                            \
            TYPE t = *pi;               \
            *pi++ = *pj;                \
            *pj++ = t;                  \
        } while (--i > 0);              \
    }

static inline int lvnodecnt(size_t lv)
{
    return ((1 << ((lv) + 1)) - 1) - (1 << (lv)) + 1;
}

static inline int gettreelv(size_t n)
{
    size_t lv = 0;

    while (1)
    {
        if ((1 << lv) <= (n) &&
            (n) <= ((1 << (lv + 1)) - 1))
        {
            return lv - 1;
        }
        lv ++;
    }
}

static inline void swapfunc(char *a, char *b, int n, int swaptype)
{
    if (swaptype <= 1)
        swapcode(long, a, b, n) else swapcode(char, a, b, n)
}

#define swap(a, b)                         \
    do {                                   \
        if (swaptype == 0) {               \
            long t = *(long *) (a);        \
            *(long *) (a) = *(long *) (b); \
            *(long *) (b) = t;             \
        } else                             \
            swapfunc(a, b, es, swaptype);  \
    } while (0)

#define vecswap(a, b, n)                 \
    do {                                 \
        if ((n) > 0)                     \
            swapfunc(a, b, n, swaptype); \
    } while (0)

#define CMP(t, x, y) (cmp((x), (y)))

static inline char *med3(char *a, char *b, char *c, cmp_t *cmp, void *thunk)
{
    return CMP(thunk, a, b) < 0
               ? (CMP(thunk, b, c) < 0 ? b : (CMP(thunk, a, c) < 0 ? c : a))
               : (CMP(thunk, b, c) > 0 ? b : (CMP(thunk, a, c) < 0 ? a : c));
}

/* We use some elaborate condition variables and signalling
 * to ensure a bound of the number of active threads at
 * 2 * maxthreads and the size of the thread data structure
 * to maxthreads.
 */

/* Condition of starting a new thread. */
enum thread_state {
    ts_idle, /* Idle, waiting for instructions. */
    ts_work, /* Has work to do. */
    ts_term  /* Asked to terminate. */
};

/* Variant part passed to heapsort invocations. */
struct heapsort {
    enum thread_state st;   /* For coordinating work. */
    struct common *common;  /* Common shared elements. */
    void *a;                /* Array base. */
    size_t ne;             /* Number of elements. */
    size_t n;               /* Node number. */
    pthread_t id;           /* Thread id. */
    pthread_mutex_t mtx_st; /* For signalling state change. */
    pthread_cond_t cond_st; /* For signalling state change. */
};

/* Invariant common part, shared across invocations. */
struct common {
    int swaptype;           /* Code to use for swapping */
    size_t es;              /* Element size. */
    void *thunk;            /* Thunk for heapsort_r */
    cmp_t *cmp;             /* Comparison function */
    int nthreads;           /* Total number of pool threads. */
    int idlethreads;        /* Number of idle threads in pool. */
    int forkelem;           /* Minimum number of elements for a new thread. */
    struct heapsort *pool;     /* Fixed pool of threads. */
    pthread_mutex_t mtx_al; /* For allocating threads in the pool. */
};

static void *heapsort_thread(void *p);

static void minHeapify(void *a, struct common *c, int start, int heapSize)
{
    cmp_t *cmp;
    cmp = c->cmp;
    size_t es = c->es;
    int swaptype = c->swaptype;
    int least = start;
    int childL = start * 2 + 1;
    int childR = start * 2 + 2;

    if (childL < heapSize && CMP(thunk, (char *) a + childL * es, (char *) a + least * es) < 0)
        least = childL;
    
    if (childR < heapSize && CMP(thunk, (char *) a + childR * es, (char *) a + least * es) < 0)
        least = childR;

    /* Swap and continue heapifying if the root is not the greatest */
    if (least != start)
    {
        swap((char *) a + start * es, (char *) a + least * es);
        minHeapify(a, c, least, heapSize);
    }
}

void heapSort(void *a, int heapSize, size_t es, cmp_t *cmp)
{
    int i;
    struct common c;

    /* Initialize common elements. */
    c.swaptype = ((char *) a - (char *) 0) % sizeof(long) || es % sizeof(long)
                     ? 2
                 : es == sizeof(long) ? 0
                                      : 1;
    c.es = es;
    c.cmp = cmp;

    int swaptype = c.swaptype;

    if (_debugmod)
    {
        printf("[%s, %d][Debug Mode] Bef. Sort\n", __func__, __LINE__);
        printf("[%s, %d][Debug Mode] ========= Dump Fill Tree =========\n",
                __func__, __LINE__);
        printf("[%s, %d][Debug Mode] ",__func__, __LINE__);
        for(unsigned int j = 0; j < heapSize; j++)
        {
            printf("%u ", *(ELEM_T *)((char *) a + j * es));
        }
        printf("\n");
        printf("[%s, %d][Debug Mode] ==================================\n",
                __func__, __LINE__);
    }

    for(i = (heapSize / 2) - 1; i >= 0; i--)
    {
        minHeapify(a, &c, i, heapSize);
    }
    for(i = heapSize - 1; i > 0; i--){
        swap(a, ((char *) a + i * es));
        minHeapify(a, &c, 0, i);
    }
    if (_debugmod)
    {
        printf("[%s, %d][Debug Mode] Aft. Sort\n", __func__, __LINE__);
        printf("[%s, %d][Debug Mode] ========= Dump Fill Tree =========\n",
                __func__, __LINE__);
        printf("[%s, %d][Debug Mode] ",__func__, __LINE__);
        for(unsigned int j = 0; j < heapSize; j++)
        {
            printf("%u ", *(ELEM_T *)((char *) a + j * es));
        }
        printf("\n");
        printf("[%s, %d][Debug Mode] ==================================\n",
                __func__, __LINE__);
    }
}

/* The multithreaded heapsort public interface */
void heapsort_mt(void *a,
                 size_t n,
                 size_t es,
                 cmp_t *cmp,
                 int maxthreads,
                 int forkelem)
{
    struct heapsort *hs;
    struct common c;
    int islot;
    bool bailout = true;

    if (n < forkelem)
        goto f1;
    errno = 0;
    /* Try to initialize the resources we need. */
    if (pthread_mutex_init(&c.mtx_al, NULL) != 0)
        goto f1;
    if ((c.pool = calloc(maxthreads, sizeof(struct heapsort))) == NULL)
        goto f2;
    for (islot = 0; islot < maxthreads; islot++) {
        hs = &c.pool[islot];
        if (pthread_mutex_init(&hs->mtx_st, NULL) != 0)
            goto f3;
        if (pthread_cond_init(&hs->cond_st, NULL) != 0) {
            verify(pthread_mutex_destroy(&hs->mtx_st));
            goto f3;
        }
        hs->st = ts_idle;
        hs->common = &c;
        if (pthread_create(&hs->id, NULL, heapsort_thread, hs) != 0) {
            verify(pthread_mutex_destroy(&hs->mtx_st));
            verify(pthread_cond_destroy(&hs->cond_st));
            goto f3;
        }
    }

    /* All systems go. */
    bailout = false;

    /* Initialize common elements. */
    c.swaptype = ((char *) a - (char *) 0) % sizeof(long) || es % sizeof(long)
                     ? 2
                 : es == sizeof(long) ? 0
                                      : 1;
    c.es = es;
    c.cmp = cmp;
    c.forkelem = forkelem;
    c.idlethreads = c.nthreads = maxthreads;

    if (_debugmod)
    {
        printf("[%s, %d][Debug Mode] Bef. Sort\n", __func__, __LINE__);
        printf("[%s, %d][Debug Mode] ========= Dump Fill Tree =========\n",
                __func__, __LINE__);
        printf("[%s, %d][Debug Mode] ",__func__, __LINE__);
        for(unsigned int j = 0; j < n; j++)
        {
            printf("%u ", *(ELEM_T *)((char *) a + j * es));
        }
        printf("\n");
        printf("[%s, %d][Debug Mode] ==================================\n",
                __func__, __LINE__);
    }

    for (int lv = gettreelv(n) ; lv >= 0 ; lv--)
    {
        int levelnodecnt = lvnodecnt(lv);
        size_t startnode = (1 << lv) - 1;
        if (_debugmod)
        {
            printf("[%s, %d][Debug Mode] Level : %d\n", __func__, __LINE__, lv);
            printf("[%s, %d][Debug Mode] levelnodecnt : %d\n", __func__, __LINE__, levelnodecnt);
            printf("[%s, %d][Debug Mode] startnode : %ld\n", __func__, __LINE__, startnode);
        }
        while(1)
        {
            for (islot = 0; islot < maxthreads; islot++)
            {
                hs = &c.pool[islot];
                if (hs->st == ts_idle)
                {
                    verify(pthread_mutex_lock(&hs->mtx_st));
                    hs->st = ts_work;
                    hs->a = (char *) a + ((startnode + levelnodecnt - 1) * es);
                    hs->ne = n;
                    hs->n = startnode + levelnodecnt - 1;
                    c.idlethreads--;
                    verify(pthread_cond_signal(&hs->cond_st));
                    verify(pthread_mutex_unlock(&hs->mtx_st));
                    levelnodecnt--;
                }
                if (levelnodecnt < 1)
                    break;
            }
            if (levelnodecnt < 1)
                break;
        };
        for (islot = 0; islot < maxthreads; islot++)
        {
            hs = &c.pool[islot];
            while (hs->st == ts_work)
            {
                continue;
            }
        }
        if (_debugmod)
            printf("[%s, %d][Debug Mode] Finish First Sort.\n",
                    __func__, __LINE__);
    }
    for(int i = n - 1; i > 0; i--)
    {
        int swaptype = c.swaptype;
        swap(a, ((char *) a + i * es));
        minHeapify(a, &c, 0, i);
    }
    if (_debugmod)
    {
        printf("[%s, %d][Debug Mode] Aft. Sort\n", __func__, __LINE__);
        printf("[%s, %d][Debug Mode] ========= Dump Fill Tree =========\n",
                __func__, __LINE__);
        printf("[%s, %d][Debug Mode] ",__func__, __LINE__);
        for(unsigned int j = 0; j < n; j++)
        {
            printf("%u ", *(ELEM_T *)((char *) a + j * es));
        }
        printf("\n");
        printf("[%s, %d][Debug Mode] ==================================\n",
                __func__, __LINE__);
    }
    /* Wait for all threads to finish, and free acquired resources. */
f3:
    for (islot = 0; islot < maxthreads; islot++) {
        hs = &c.pool[islot];
        if (bailout) {
            verify(pthread_mutex_lock(&hs->mtx_st));
            hs->st = ts_term;
            verify(pthread_cond_signal(&hs->cond_st));
            verify(pthread_mutex_unlock(&hs->mtx_st));
        }
        verify(pthread_mutex_lock(&hs->mtx_st));
        hs->st = ts_term;
        verify(pthread_cond_signal(&hs->cond_st));
        verify(pthread_mutex_unlock(&hs->mtx_st));
        verify(pthread_join(hs->id, NULL));
        verify(pthread_mutex_destroy(&hs->mtx_st));
        verify(pthread_cond_destroy(&hs->cond_st));
    }
    free(c.pool);
f2:
    verify(pthread_mutex_destroy(&c.mtx_al));
    if (bailout) {
        fprintf(stderr, "Resource initialization failed; bailing out.\n");
    f1:
        qsort(a, n, es, cmp);
    }
}

/* Thread-callable quicksort. */
static void heapsort_algo(struct heapsort *hs)
{
    int swaptype;
    void *a;            /* Array of elements. */
    size_t n, es, ne;   /* Number of elements; size. */
    cmp_t *cmp;
    struct common *c;

    /* Initialize heapsort arguments. */
    c = hs->common;
    es = c->es;
    cmp = c->cmp;
    swaptype = c->swaptype;
    a = hs->a;
    n = hs->n;
    ne = hs->ne;

    /* From here on heapsort(3) business as usual. */
    size_t leftSide = 2 * n + 1;
    size_t rightSide = 2 * n + 2;
    size_t greatest = n;

    if (_debugmod)
    {
        printf("[%s, %d][Debug Mode] Work Node : %ld, Val : %u\n",
                __func__, __LINE__, n, *(ELEM_T *) a);
        if (leftSide < ne)
            printf("[%s, %d][Debug Mode] Work Node Left : %ld, Val : %u\n",
                    __func__, __LINE__, leftSide, *(ELEM_T *)((char *) a + (leftSide - n) * es));
        if (rightSide < ne)
            printf("[%s, %d][Debug Mode] Work Node Righ : %ld, Val : %u\n",
                    __func__, __LINE__, rightSide, *(ELEM_T *)((char *) a + (rightSide - n) * es));
    }

    if (leftSide < ne && CMP(thunk, (char *) a + (leftSide - n) * es, (char *) a + (greatest - n) * es) < 0)
        greatest = leftSide;

    if (rightSide < ne && CMP(thunk, (char *) a + (rightSide - n) * es, (char *) a + (greatest - n) * es) < 0)
        greatest = rightSide;

    /* Swap and continue heapifying if the root is not the greatest */
    if (greatest != n) {
        if (_debugmod)
            printf("[%s, %d][Debug Mode] Swap : (%ld, %ld)\n",
                    __func__, __LINE__, n, greatest);
        swap(a, ((char *) a + (greatest - n) * es));
        hs->a = (char *) a + (greatest - n) * es;
        hs->ne = ne;
        hs->n = greatest;
        heapsort_algo(hs);
    }
}

/* Thread-callable quicksort. */
static void *heapsort_thread(void *p)
{
    struct heapsort *hs;
    struct common *c;

    hs = p;
    c = hs->common;
again:
    /* Wait for work to be allocated. */
    verify(pthread_mutex_lock(&hs->mtx_st));
    while (hs->st == ts_idle)
        verify(pthread_cond_wait(&hs->cond_st, &hs->mtx_st));
    verify(pthread_mutex_unlock(&hs->mtx_st));
    if (hs->st == ts_term) {
        return NULL;
    }
    assert(hs->st == ts_work);

    heapsort_algo(hs);

    verify(pthread_mutex_lock(&c->mtx_al));
    hs->st = ts_idle;
    c->idlethreads++;
    verify(pthread_mutex_unlock(&c->mtx_al));
    goto again;
}

int num_compare(const void *a, const void *b)
{
    return (*(ELEM_T *) a - *(ELEM_T *) b);
}

int string_compare(const void *a, const void *b)
{
    return strcmp(*(char **) a, *(char **) b);
}

void *xmalloc(size_t s)
{
    void *p;

    if ((p = malloc(s)) == NULL) {
        perror("malloc");
        exit(1);
    }
    return (p);
}

void usage(void)
{
    fprintf(
        stderr,
        "usage: heapsort_mt [-stv] [-f forkelements] [-h threads] [-n elements]\n"
        "\t-s\tTest with 20-byte strings, instead of integers\n"
        "\t-t\tPrint timing results\n"
        "\t-d\tPrint tree operation log\n"
        "\t-v\tVerify the integer results\n"
        "Defaults are 1e7 elements, 2 threads, 100 fork elements\n");
    exit(1);
}

int main(int argc, char *argv[])
{
    bool opt_str = false;
    bool opt_time = false;
    bool opt_verify = false;
    bool opt_libc = false;
    int ch, i;
    size_t nelem = 10000000;
    int threads = 2;
    int forkelements = 10;
    ELEM_T *int_elem;
    char *ep;
    char **str_elem;
    struct timeval start, end;
    struct rusage ru;

    gettimeofday(&start, NULL);
    while ((ch = getopt(argc, argv, "f:h:ln:stvd")) != -1) {
        switch (ch) {
        case 'f':
            forkelements = (int) strtol(optarg, &ep, 10);
            if (forkelements <= 0 || *ep != '\0') {
                warnx("illegal number, -f argument -- %s", optarg);
                usage();
            }
            break;
        case 'h':
            threads = (int) strtol(optarg, &ep, 10);
            if (threads < 0 || *ep != '\0') {
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
        case 'd':
            _debugmod = true;
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
        for (i = 0; i < nelem; i++)
            if (asprintf(&str_elem[i], "%d%d", rand(), rand()) == -1) {
                perror("asprintf");
                exit(1);
            }
    } else {
        int_elem = xmalloc(nelem * sizeof(ELEM_T));
        for (i = 0; i < nelem; i++)
            int_elem[i] = rand() % nelem;
        printf("\n");
    }
    if (opt_str) {
        if (opt_libc)
            heapSort(str_elem, nelem, sizeof(char *), string_compare);
        else
            heapsort_mt(str_elem, nelem, sizeof(char *), string_compare, threads,
                        forkelements);
    } else {
        if (opt_libc)
            heapSort(int_elem, nelem, sizeof(ELEM_T), num_compare);
        else
            heapsort_mt(int_elem, nelem, sizeof(ELEM_T), num_compare, threads,
                        forkelements);
    }
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
}
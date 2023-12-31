#pragma once

#include <stdbool.h>
#include "atomic.h"
#include "futex.h"
#include "spinlock.h"

#define MUTEX_SPINS 128

typedef struct {
    atomic int state;
    unsigned short type;
    unsigned short prioceiling;
} mutex_t;

/* Mutex attributes */
typedef struct {
    unsigned short type;
    unsigned short prioceiling;
} mutexattr_t;

#define GETTID syscall(SYS_gettid)

enum {
    MUTEX_LOCKED = 1 << 0,
    MUTEX_SLEEPING = 1 << 1,
};

/* Mutex attribute's protocol */
enum {
    TBTHREAD_PRIO_NONE,
    TBTHREAD_PRIO_INHERIT = 3,
    TBTHREAD_PRIO_PROTECT = 6,
};

/* Initialize the mutex */
static inline void mutex_init(mutex_t *mutex, mutexattr_t *attr)
{
    atomic_init(&mutex->state, 0);
    mutex->type = attr->type;;
    mutex->prioceiling = attr->prioceiling;
    return;
}

#define cmpxchg(obj, expected, desired) \
    compare_exchange_strong(obj, expected, desired, relaxed, relaxed)


static inline bool mutex_trylock_pi(mutex_t *mutex)
{
    pid_t zero = 0;
    pid_t tid = GETTID;

    if (cmpxchg(&mutex->state, &zero, tid))
        return true;

    thread_fence(&mutex->state, acquire);
    return false;
}

static inline void mutex_lock_pi(mutex_t *mutex)
{
    for (int i = 0; i < MUTEX_SPINS; ++i) {
        if (mutex_trylock_pi(mutex))
            return;
        spin_hint();
    }

    futex_lock_pi(&mutex->state, NULL);
    thread_fence(&mutex->state, acquire);
}

static inline void mutex_unlock_pi(mutex_t *mutex) {
    pid_t tid = GETTID;
    if(cmpxchg(&mutex->state, &tid, 0))
        return;
    futex_unlock_pi(&mutex->state);
}

int mutexattr_setprotocol(mutexattr_t *attr, int protocol)
{
    attr->type = (attr->type % 3) + protocol;
    return 0;
}

static inline bool mutex_trylock(mutex_t *mutex)
{
    int state = load(&mutex->state, relaxed);
    if (state & MUTEX_LOCKED)
        return false;

    state = fetch_or(&mutex->state, MUTEX_LOCKED, relaxed);
    if (state & MUTEX_LOCKED)
        return false;

    thread_fence(&mutex->state, acquire);
    return true;
}

static inline void mutex_lock(mutex_t *mutex)
{
    for (int i = 0; i < MUTEX_SPINS; ++i) {
        if (mutex_trylock(mutex))
            return;
        spin_hint();
    }

    int state = exchange(&mutex->state, MUTEX_LOCKED | MUTEX_SLEEPING, relaxed);

    while (state & MUTEX_LOCKED) {
        futex_wait(&mutex->state, MUTEX_LOCKED | MUTEX_SLEEPING);
        state = exchange(&mutex->state, MUTEX_LOCKED | MUTEX_SLEEPING, relaxed);
    }

    thread_fence(&mutex->state, acquire);
}

static inline void mutex_unlock(mutex_t *mutex)
{
    int state = exchange(&mutex->state, 0, release);
    if (state & MUTEX_SLEEPING)
        futex_wake(&mutex->state, 1);  // FFFF
}

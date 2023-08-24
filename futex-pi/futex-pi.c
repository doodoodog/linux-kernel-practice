#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>
#include <string.h>

#include "mutex.h"
#include "atomic.h"

#define THREADCOUNT 3

mutex_t mtx1, mtx2;

void TASK1(void *arg)
{
    mutex_lock_pi(&mtx1);
    printf("1\n");
    mutex_unlock_pi(&mtx1);
	return;
}

void TASK2(void *arg)
{ 
    mutex_lock_pi(&mtx2);
    sleep(1);
    printf("2\n");
    mutex_unlock_pi(&mtx2);
	return;
}

void TASK3(void *arg)
{   
    mutex_lock_pi(&mtx1);
    sleep(1);
    printf("3\n");
    mutex_unlock_pi(&mtx1);
    return;
}

static void (*TASKS[])() = {
    TASK1,
    TASK2,
    TASK3,
};

int main() {
    int st;
    pthread_t th[THREADCOUNT];
    mutexattr_t mattr;
    mutexattr_setprotocol(&mattr, TBTHREAD_PRIO_INHERIT);
    mutex_init(&mtx1, &mattr);
    mutex_init(&mtx2, &mattr);
    pthread_attr_t attr;
    pthread_attr_setschedpolicy(&attr, SCHED_FIFO);
    pthread_attr_setinheritsched(&attr, PTHREAD_EXPLICIT_SCHED);
    struct sched_param param;

    for(int i = THREADCOUNT - 1; i >= 0; i--) {
        param.sched_priority = (THREADCOUNT - i) * 10;
        pthread_attr_setschedparam(&attr, &param);
        st = pthread_create(&th[i], &attr, (void *)TASKS[i], NULL);
        if (st != 0) {
            printf("Failed to spawn thread %d: %s\n", i, strerror(-st));
            return 1;
        }
    }

	for(int i = THREADCOUNT - 1; i >= 0; i--)
    {
        pthread_join(th[i], NULL);
    }

    sleep(2);
    return 0;
}

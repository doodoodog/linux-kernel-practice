CFLAGS := -std=gnu11 -Wall -g -O2 -D_GNU_SOURCE
LDFLAGS := -lpthread

all: futex-qsort-mt.c atomic.h  cond.h  futex.h  mutex.h  spinlock.h
	$(CC) $(CFLAGS) futex-qsort-mt.c -o futex-qsort-mt $(LDFLAGS)

# Test suite
NAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Darwin)
    PRINTF = printf
else
    PRINTF = env printf
endif
PASS_COLOR = \e[32;01m
NO_COLOR = \e[0m
notice = $(PRINTF) "$(PASS_COLOR)$(strip $1)$(NO_COLOR)\n"

check: all
	./sort -v -t

clean:
	$(RM) ./sort
.PHONY: clean
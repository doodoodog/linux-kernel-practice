CFLAGS = -Wall -fno-stack-protector -I. -pthread -lpthread -fsanitize=thread
CC := gcc

all:
	$(CC) $(CFLAGS) -o futex-pi futex-pi.c $(OBJ)
	$(CC) $(CFLAGS) -o futex futex.c $(OBJ)

check:
	$(CC) $(CFLAGS) -o futex-pi futex-pi.c $(OBJ)
	$(CC) $(CFLAGS) -o futex futex.c $(OBJ)
	sudo ./futex-pi
	sudo ./futex

test:
	python3 driver.py

clean: 
	rm -f test-*
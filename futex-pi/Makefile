CFLAGS = -Wall -fno-stack-protector -I. -pthread -lpthread -fsanitize=thread
CC := gcc

check:
	$(CC) $(CFLAGS) -o futex-pi futex-pi.c $(OBJ)
	sudo ./futex-pi

clean: 
	rm -f test-*
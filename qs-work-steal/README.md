Run :
$ gcc -O2 -Wall -std=c11 -o work-steal-qsort work-steal-qsort.c -lpthread
$ ./work-steal-qsort
...
work ter 1 finished
work item 10 finished
work item 11 finished
work item 14 finished
work item 6 finished
work item 16 finished
Expect 506 lines of output (including this one)

Class Ref. https://hackmd.io/@sysprog/linux2023-summer-quiz2
Code Ref. https://gist.github.com/jserv/111304e7c5061b05d4d29a47571f7a98
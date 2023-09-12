Run :
$ gcc -Wall -std=c11 -o mpmc mpmc.c -lpthread

參考執行輸出如下:
Amount: 10000000

#0
ints[1-10000000] have been verified through
elapsed time: 0.835668 seconds
DONE #0

#1
ints[1-10000000] have been verified through
elapsed time: 0.837184 seconds
DONE #1

#2
ints[1-10000000] have been verified through
elapsed time: 0.829464 seconds
DONE #2
...
#7
ints[1-10000000] have been verified through
elapsed time: 0.761233 seconds
DONE #7

Class Ref. https://hackmd.io/@sysprog/linux2023-summer-quiz2
Code Ref. https://gist.github.com/jserv/c7957a65f810205da462909491dae4bf
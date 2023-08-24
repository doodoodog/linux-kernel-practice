#!/usr/bin/env python3

import subprocess
import numpy as np

RED = '\033[91m'
GREEN = '\033[92m'
WHITE = '\033[0m'

TestFile = [
    "futex",
    "futex-pi"
]
def printInColor(text, color):
    print(color, text, WHITE, sep = '')

if __name__ == "__main__":
    comp_proc = subprocess.run('make clean all> /dev/null', shell = True)
    if comp_proc.returncode:
        printInColor(" ERROR: Compile Fail \n", RED)
        exit(1)

    for i in range (1,3):
        PI_times = 0;
        for runs in range(10):
            comp_proc = subprocess.run('sudo taskset -c 3 ./{} > data.txt'.format(TestFile[i - 1]), shell = True)
            output = np.loadtxt('data.txt', dtype = 'int32').T      
            if (output[0] == 2 and output[1] == 3 and output[2] == 1):
                PI_times += 1
        
        if comp_proc.returncode:
            printInColor("+++ Test-{} Fail +++ \n".format(i), RED)
            exit(1)
        else:
            if i == 1:
                printInColor("Normal mutex, Priority_inversion times = {} for {} runs".format(PI_times, runs + 1), WHITE)
            if i == 2:
                printInColor("Priority Inheritance mutex, Priority_inversion times = {} for {} runs".format(PI_times, runs + 1), WHITE)
            printInColor("+++ Test-{} Pass +++ \n".format(i), GREEN)
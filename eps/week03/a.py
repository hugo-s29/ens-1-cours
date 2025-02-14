from functools import reduce
from operator import mul
import itertools
import heapq

num_tests = int(input())

def prod(a):
    return [(x,y,i,j) for i,x in enumerate(a) for j, y in enumerate(a) if i != j]

for _ in range(num_tests):
    n = int(input())
    a = [ (int(x), i) for i, x in enumerate(input().split(' ')) ]

    five_smallest = heapq.nsmallest(5, a)
    five_largest  = heapq.nlargest (5, a)

    s = set(five_smallest + five_largest)

    max_prod = max(
        reduce(mul, [x for x, _ in p])
        for p in itertools.combinations(s, 5)
    )
    print(max_prod)

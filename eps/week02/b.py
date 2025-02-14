import heapq

num_tests = int(input())

for _ in range(num_tests):
    _ = [ int(x) for x in input().split(' ') ]
    a = [ int(x) for x in input().split(' ') ]
    b = [ int(x) for x in input().split(' ') ]

    heapq.heapify(a)

    for b_j in b:
        heapq.heapreplace(a, b_j)

    print(sum(a))

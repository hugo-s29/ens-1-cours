import itertools

num_tests = int(input())

for _ in range(num_tests):
    n = int(input())
    s = input()

    for x in range(1, n):
        print(int(s[:x+1], 2) - n, end=" ")
    print()










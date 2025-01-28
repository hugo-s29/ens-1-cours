import math

log = lambda x: int(math.log(x))

n = int(input())
k = int(input())

off = 0
max_off = 0

for _ in range(k):
    i = int(input())

    off = off ^ sum(u * 2**i for u in range(1, n // i + 1))

    n_off = log(off)

    if max_off < n_off: max_off = n_off

print(max_off)

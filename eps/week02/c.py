import sys

m, n = [ int(x) for x in input().split(' ') ]

p = []

for _ in range(n):
    print(1)
    sys.stdout.flush()
    q = int(input())
    if q == -2 or q == 0: sys.exit(0)
    p.append(q)

i = 0

def get_answer(k):
    global i

    print(k)
    sys.stdout.flush()
    q = int(input())

    if q == -2 or q == 0: sys.exit(0)

    q *= p[i]

    i = (i + 1) % n
    return q


a, b = 0, m

while b >= a:
    y = (a+b) // 2
    ans = get_answer(y)

    if ans < 0: b = y - 1
    else: a = y + 1



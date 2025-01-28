num_cases = int(input())

for _ in range(num_cases):
    a, b, c = sorted([ int(x) for x in input().split(' ') ])

    if a + b == c: print('YES')
    else: print('NO')


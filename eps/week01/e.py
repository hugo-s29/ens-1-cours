_, k = [ int(x) for x in input().split(' ') ]
r = { ord(x) - ord('a') + 1 for x in input() }

s = 0

for _ in range(k):
    if len(r) == 0:
        print('-1')
        break

    x = min(r)
    r = { y for y in r if y >= x + 2 }

    s += x
else:
    print(s)





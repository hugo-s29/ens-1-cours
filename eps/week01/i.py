n, m = [ int(x) for x in input().split(' ') ]
lines = [ [ int(x) for x in input().split(' ') ] for _ in range(n) ]

costs = [ lines[i][0] for i in range(n) ]
resell = [ lines[i][1:] for i in range(n) ]

opti = [ None for _ in range(n) ]

opti[n-1] = 0
opti[n-2] = 0

for k in reversed(range(n-1)):
    print([ (len(resell[l]), l - k) for l in range(k+1, n)])
    opti[k] = min(opti[l] + costs[l] - resell[l][l-k-1] for l in range(k+1, n) if l - k < m)

print(opti[0])


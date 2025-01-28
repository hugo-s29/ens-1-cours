n = int(input())

ax, ay = [ int(x) for x in input().split(' ') ]
bx, by = [ int(x) for x in input().split(' ') ]
cx, cy = [ int(x) for x in input().split(' ') ]

def sign(x):
    if x > 0: return 1
    elif x == 0: return 0
    else: return -1

ux, uy = sign(bx - ax), sign(by - ay)
vx, vy = sign(cx - ax), sign(cy - ay)

if ux == vx and uy == vy: print('YES')
else: print('NO')

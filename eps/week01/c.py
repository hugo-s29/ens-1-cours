x = input()

for x0, *group in zip(x, x[1:], x[2:], x[3:], x[4:], x[5:], x[6:]):
    if all( x0 == g for g in group ):
        print('YES')
        break
else:
    print('NO')

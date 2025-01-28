x = input()

i = len(x) - 1

while i >= 0:
    if i >= 2 and x[i-2:i+1] == '144': i -= 3
    elif i >= 1 and x[i-1:i+1] == '14': i -= 2
    elif i >= 0 and x[i] == '1': i -= 1
    else:
        print('NO')
        break
else:
    print('YES')



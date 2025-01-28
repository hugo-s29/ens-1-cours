num_cases = int(input())

for _ in range(num_cases):
    x = int(input())

    if 1900 <= x: print('Division 1')
    elif 1600 <= x: print('Division 2')
    elif 1400 <= x: print('Division 3')
    else: print('Division 4')

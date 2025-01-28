n, k = [ int(x) for x in input().split(' ') ]
lines = [ input() for _ in range(3 * n) ]
last_index = lambda li,x : next(i for i in reversed(range(len(li))) if li[i] == x)

#frequencies = [ (lines.count(l), last_index(lines, l), l) for l in set(lines)]
frequencies = dict()

def unique(seq):
    seen = set()
    seen_add = seen.add
    return [x for x in seq if not (x in seen or seen_add(x))]

unique_lines = unique(reversed(lines))

for l in unique_lines:
    c = lines.count(l)

    if c not in frequencies: frequencies[c] = []

    frequencies[c].append(l)

k2 = k
for _ in range(k):
    if k2 <= 0 or frequencies == dict(): break

    min_key = max(frequencies.keys())

    for item in frequencies[min_key]:
        if k2 <= 0: break
        print(item)
        k2 -= 1

    frequencies.pop(min_key, None)






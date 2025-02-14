import itertools

num_tests = int(input())

def score_len(n):
    return n - n // 4

def get_a_score(a, n0, n, l):
    added = min(l, n - n0)
    take = l - added
    return a[take] + 100 * added

def get_b_score(b, n0, n, l):
    take = min(l, n0)
    return b[take]

for _ in range(num_tests):
    n0 = int(input())
    a0 = sorted([ int(x) for x in input().split(' ') ])[::-1]
    b0 = sorted([ int(x) for x in input().split(' ') ])[::-1]
    i = n0

    a = [0]+list(itertools.accumulate(a0))
    b = [0]+list(itertools.accumulate(b0))

    l = score_len(i)
    sa = get_a_score(a, n0, i, l)
    sb = get_b_score(b, n0, i, l)

    while sa < sb:
        i += 1
        l = score_len(i)
        sa = get_a_score(a, n0, i, l)
        sb = get_b_score(b, n0, i, l)

    print(i - n0)

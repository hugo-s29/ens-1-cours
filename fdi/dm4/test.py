import os

test_chars = '0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ!"#$%&\'()*+,-./:;<=>?@[\\]^_`{|}~ \t\n\r\x0b\x0c'

with open('main.py') as f:
    code = f.read()

counts = { k: code.count(k) for k in set(code) }

for c in reversed(test_chars):
    encoded = {'"': r'\"', '$': r'\$', '\\': r'\\', '`': r'\`' }.get(c, c)
    res = os.popen(f'ipython main.py "{encoded}"').read()
    print(c, res)
    if int(res) != counts.get(c, 0):
        print("Failed !")
        print("Got", res, "but expected", counts.get(c, 0))
        break

print('Success !')


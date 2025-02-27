from PIL import Image
import json


images = [
    Image.open('frames/frame_' + str(k) + '_edges.png')\
    for k in range(1, 11)
]

for img in images:
    img.thumbnail((250, 250), Image.NEAREST)

def filter(x):
    r, g, b = x
    return (r+g+b)/3 >= 200

pos = [
    (0, 0),
    (0, 1),
    (0, 2),
    (1, 0),
    (1, 1),
    (1, 2),
    (0, 3),
    (1, 3),
]

def f(img):
    res = ""
    for j in range(0, (img.height // 4) * 4 - 1, 4):
        for i in range(0, (img.width // 2) * 2 - 1, 2):
            pixels = [
                img.getpixel((i+di,j+dj)) for (di, dj) in pos
            ]

            n = int(''.join([ '1' if filter(b) else '0' for b in pixels ]), 2)
            res += chr(0x2800 + n)
        res += "\\n"
    return res

for img in images:
    print('"' + f(img) + '"')

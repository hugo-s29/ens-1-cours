from PIL import Image

def remove_color(image_path, target_color1, target_color2, tolerance=30, output_path="output.png"):
    image = Image.open(image_path).convert("RGBA")
    data = image.getdata()

    new_data = []
    for pixel in data:
        r, g, b, a = pixel
        if False and abs(r - target_color2[0]) <= tolerance and \
             abs(g - target_color2[1]) <= tolerance and \
             abs(b - target_color2[2]) <= tolerance:
            new_data.append(target_color1)
        else:
            new_data.append(pixel)

    image.putdata(new_data)
    image = image.resize((64*1, 100*1), Image.Resampling.LANCZOS)
    image.save(output_path, "PNG")
    print(f"Processed image saved to {output_path}")

for i in range(1, 49):
    remove_color(f"frames/frame_{i}.png", (191, 124, 22), (118, 78, 22), tolerance=50, output_path=f"frames/frame_{i}_done.png")

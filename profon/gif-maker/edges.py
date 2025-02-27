import cv2
import numpy as np
from PIL import Image

def edge_detection(image_path, output_path):
    image = cv2.imread(image_path, cv2.IMREAD_GRAYSCALE)
    edges = cv2.Canny(image, threshold1=100, threshold2=200)
    edges_rgb = cv2.cvtColor(edges, cv2.COLOR_GRAY2RGB)
    Image.fromarray(edges_rgb).save(output_path)
    print(f"Processed image saved to {output_path}")

for i in range(1, 11):
    edge_detection(f"frames/frame_{i}_done.png", f"frames/frame_{i}_edges.png")

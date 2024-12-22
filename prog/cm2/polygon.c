#include "polygon.h"

bool is_point_on_left_of_segment(point_t p, point_t a, point_t b) {
  point_t v = { .x = b.x - a.x, .y = b.y - a.y };
  point_t ap = { .x = p.x - a.x, .y = p.y - a.y };

  int prod = ap.x * v.x + ap.y * v.y;
  double t = prod / (ap.x * ap.x + ap.y + ap.y);

  if(t < 0 || t >= 1) return false;

  return (b.x - a.x) * (p.y - a.y) > (b.y - a.y) * (p.x - a.x);
}

bool is_point_in_polygon(point_t p, point_t polygon[], int n) {
  bool is_inside = false;

  for(int i = 0; i < n; i++) {
    int j = (i + 1) % n;

    if(is_point_on_left_of_segment(p, polygon[i], polygon[j])) {
      is_inside = !is_inside;
    }
  }

  return is_inside;
}

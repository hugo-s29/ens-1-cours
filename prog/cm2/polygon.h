#pragma once

#include <stdbool.h>

typedef struct {
  int x;
  int y;
} point_t;

bool is_point_in_polygon(point_t p, point_t polygon[], int n);
bool is_point_on_left_of_segment(point_t p, point_t a, point_t b);

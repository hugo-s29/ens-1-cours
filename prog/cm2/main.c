#include<raylib.h>
#include<stdio.h>
#include "polygon.h"

#define MAX_SIZE 100

void draw_polygon(point_t polygon[MAX_SIZE], int n) {
  for(int i = 0; i < n; i++) {
    int j = (i + 1) % n;
    DrawLine(polygon[i].x, polygon[i].y, polygon[j].x, polygon[j].y, WHITE);
  }


  for(int i = 0; i < n; i++) {
    DrawCircle(polygon[i].x, polygon[i].y, 3, WHITE);
  }
}

int main() {
  point_t polygon[MAX_SIZE];
  point_t query;
  int n = 0;

  InitWindow(640, 480, "Test membership of a point in a polygon");
  SetTargetFPS(120);

  while(!WindowShouldClose()) {
    BeginDrawing();
    Vector2 v = GetMousePosition();

    query.x = v.x;
    query.y = v.y;

    ClearBackground(BLACK);

    if(is_point_in_polygon(query, polygon, n)) {
      DrawCircle(query.x, query.y, 4, GREEN);
    } else {
      DrawCircle(query.x, query.y, 4, RED);
    }

    if(IsMouseButtonPressed(MOUSE_BUTTON_LEFT) && n < MAX_SIZE) {
      polygon[n].x = v.x;
      polygon[n].y = v.y;

      n++;
    }

    draw_polygon(polygon, n);

    EndDrawing();
  }

  CloseWindow();
  return 0;
}

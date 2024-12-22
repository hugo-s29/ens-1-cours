#include<stdio.h>

struct str {
  int n;
  struct str2* x;
};

struct str2 {
  int n2;
  struct str x;
};


int main() {
  printf("%d\n", sizeof(struct str));
}

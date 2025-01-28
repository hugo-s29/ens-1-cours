#include<stdio.h>
#include<stdlib.h>
#include<stdbool.h>

int main() {
  int n, k, i;

  scanf("%d", &n);
  scanf("%d", &k);

  bool* city = calloc(sizeof(bool), n);

  int n_off = 0;
  int n_off_max = 0;

  for(int j = 0; j < k; j++) {
    scanf("%d", &i);

    for(int x = 1; x < n / i + 1; x++) {
      if (city[x * i - 1]) n_off--;
      else n_off++;

      city[x * i - 1] = !city[x * i - 1];
    }

    if (n_off_max < n_off) { n_off_max = n_off; }
  }

  printf("%d\n", n_off_max);

  free(city);
}

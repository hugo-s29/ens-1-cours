#include<stdio.h>
#include<stdlib.h>

void printPyramid(int n) {
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < i + 1; j++) {
            printf("* ");
        }

        printf("\n");
    }
}

int main() {
    int n;
    printf("> n ?");
    scanf("%d", &n);
    printf("\n");

    printPyramid(n);


    return EXIT_SUCCESS;
}

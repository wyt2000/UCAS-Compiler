#include <cstdio>
#include <cstdlib>

int GET() {
    int n;
    scanf("%d", &n);
    return n;
}
void * MALLOC(int n) {
    return malloc(n);
}
void FREE(void *p) {
    free(p);
}
void PRINT(int n) {
    printf("%d", n);
}


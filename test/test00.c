extern int GET();
extern void * MALLOC(int);
extern void FREE(void *);
extern void PRINT(int);

int a = 10;

void f() {
    a = -1;
}

int main() {
   f();
   PRINT(a);
}

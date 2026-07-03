#include <stdio.h>
/*@
    requires n > 0;
    assigns \nothing;
    behavior update:
        assumes  n >= 7;
        ensures \result == (n-7)/3 + 2;
    behavior nonupdate:
        assumes  n < 7;
        ensures \result == 1;
    complete behaviors;
    disjoint behaviors;
*/
int fun(int n) {
    int i = 7;
    int x = 1;
    /*@
        loop invariant 7 <= i <= n + 3 || i == 7;
        loop invariant i == 4 + 3*x;
        loop assigns x, i;
    */
    while(i <= n) {
        x += 1;
        i += 3;
    }
    return x;
}

int main() {
    int a = fun(20);
    printf("%d\n", a);
}

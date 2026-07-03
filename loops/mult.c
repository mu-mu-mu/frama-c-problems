#include <stdio.h>
/*@
    requires a >= 0 && b >= 0;
    ensures \result == \old(a + 1)*\old(b);
    assigns \nothing;
*/
int mul(int a, int b) {
    int x = a, y = b, prod = 0;
    /*@ 
        loop invariant -1 <= x <= a;
        loop invariant prod == (a-x)*y;
        loop assigns prod, x;
    */
    while(x >= 0) {
        prod = prod + y;
        x--;
    }
    return prod;
}

int main() {
    int pdt = mul(2, 5);
    //@ assert pdt == 15;
}

#include <stdio.h>
/*@
 axiomatic a {
  logic integer fact(integer i);
  logic integer power(integer i);

  axiom fact_def: fact(0) == 1;
  axiom power_def: power(0) == 1;
  }*/

/*@
requires 0 <= i;
terminates \true;
exits \false;
assigns \nothing;
ensures \result == power(i);
*/
int power(int i);

/*@
requires 0 <= i;
terminates \true;
exits \false;
assigns \nothing;
ensures \result == fact(i);
*/
int factorial(int i);

/*@
	requires 0 <= n;
	assigns \nothing;
*/
int pdt(int n) {
  int prod = 1;
  int i = 2;
  /*@
    loop invariant  prod == power((i - 2)/2)*fact((i - 2)/2);
    loop invariant 0 < i;
    loop invariant i <= n+2;
    loop assigns i, prod;  
    loop variant n - i;
  */
  while(i < n) {
    prod = power(i/2)*factorial(i/2);
    i = i+2;
  }
  return prod;
}

int main() {
    int p = pdt(10);
    printf("%d\n", p);
}
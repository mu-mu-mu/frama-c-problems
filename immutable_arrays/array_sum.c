/*@
  axiomatic SumArray {
  logic integer sumArr(int *a, integer n) reads a[0 .. n-1];
  axiom case_m:
    \forall integer m, int *a;
    (0 < m ==> (sumArr(a, m) == ( sumArr(a, m-1) + a[m-1] )));
  axiom case_m0:
    \forall int *a, integer m;
    m == 0 ==> sumArr(a, 0) == 0;
  }
*/

/*@
    requires n > 0;
    requires \valid_read(a + (0..n-1));
    assigns \nothing;
    ensures \result == sumArr(a, n);
*/
int sumArray(int *a, int n) {
    int p = 0, sum = 0;
    /*@
        loop invariant 0 <= p <= n;
        loop invariant (sum == sumArr(a, p));
        loop assigns sum, p;
    */
    while (p < n) {
        sum = sum + a[p];
        p++;
    }
    return sum;
}

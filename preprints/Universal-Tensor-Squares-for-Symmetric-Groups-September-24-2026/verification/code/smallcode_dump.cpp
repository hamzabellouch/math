#define main submitted_main
#include "smallcode_submitted.cpp"
#undef main
#include <iostream>

int main(int argc, char** argv) {
 n = atoi(argv[1]);
 for (int s = 0; s <= n; ++s) {
  diagrams(s, s, s, 63, one(64)-1);
  int m = 1;
  while (m < 2 * (int)masks[s].size()) m *= 2;
  idxs[s].assign(m, -1);
  for (int i = 0; i < (int)masks[s].size(); ++i)
   idxs[s][slot(s, masks[s][i])] = i;
 }
 for (int i = 0; i < (int)masks[n].size(); ++i) {
  cout << "partition " << i << ' ' << sym(masks[n][i]);
  int row = 0;
  for (int b = 127; b >= 0; --b) if (masks[n][i] & one(b)) {
   ++row;
   int length = b - 64 + row;
   if (length) cout << ' ' << length;
  }
  cout << '\n';
 }
 for (int mod : {1000000007, 1000000009}) {
  p = mod; fac[0] = 1; dimv[0] = V{1};
  for (int j = 1; j <= n; ++j) {
   invv[j] = inverse(j); fac[j] = mul(fac[j-1], invv[j]);
   dimv[j] = op(j-1, 1, true, dimv[j-1]);
  }
  cout << "dimensions " << p;
  for (int x : dimv[n]) cout << ' ' << x;
  cout << '\n';
  for (int i = 0; i < (int)masks[n].size(); ++i) {
   V v(masks[n].size()); v[i] = 1;
   v = calc(n, n, 0, v);
   cout << "square " << p << ' ' << i;
   for (int x : v) cout << ' ' << x;
   cout << '\n';
  }
  V v(masks[n].size());
  for (int i = 0; i < (int)v.size(); ++i) v[i] = (3*i+1)%5;
  v = calc(n, n, 0, v);
  cout << "mixed " << p;
  for (int x : v) cout << ' ' << x;
  cout << '\n';
 }
}

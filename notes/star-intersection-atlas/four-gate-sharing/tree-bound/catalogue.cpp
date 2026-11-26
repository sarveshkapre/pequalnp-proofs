// Enumerate the directed forests on normalized matched pairs in all five hosts.
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <set>
#include <string>
#include <vector>
using namespace std;
using U = uint64_t;
int pc(U s) { return __builtin_popcountll(s); }
struct Tree {
  vector<U> a, h, both;
  set<string> types[16];
  int high = 0;
  string root(int i, int back, U members) const {
    vector<string> branches;
    U neighbors = a[i] & members;
    while (neighbors) {
      int j = __builtin_ctzll(neighbors);
      neighbors &= neighbors - 1;
      if (j != back)
        branches.push_back(string(1, (h[i] >> j & 1) ? '>' : '<') +
                           root(j, i, members));
    }
    sort(branches.begin(), branches.end());
    string s = "(";
    for (auto &b : branches)
      s += b;
    return s + ")";
  }
  string forest(U group) const {
    vector<string> parts;
    while (group) {
      U front = group & -group, seen = front;
      while (front) {
        int v = __builtin_ctzll(front);
        front &= front - 1;
        U add = a[v] & group & ~seen;
        seen |= add;
        front |= add;
      }
      string best;
      for (U v = seen; v; v &= v - 1) {
        string form = root(__builtin_ctzll(v), -1, seen);
        if (best.empty() || form < best)
          best = form;
      }
      group &= ~seen;
      parts.push_back(best);
    }
    sort(parts.begin(), parts.end());
    string k;
    for (auto &x : parts)
      k += x;
    return k;
  }
  // A double edge or a second contact in one old component closes a cycle.
  void scan(U taken, U left) {
    int n = pc(taken);
    high = max(high, n);
    if (n >= 8)
      types[n].insert(forest(taken));
    while (left && n + pc(left) >= 8) {
      int i = __builtin_ctzll(left);
      left &= left - 1;
      U touches = a[i] & taken;
      bool ok = true;
      while (touches) {
        U front = touches & -touches, seen = front;
        while (front) {
          int v = __builtin_ctzll(front);
          front &= front - 1;
          U add = a[v] & taken & ~seen;
          seen |= add;
          front |= add;
        }
        if (pc(seen & touches) > 1) {
          ok = false;
          break;
        }
        touches &= ~seen;
      }
      if (ok)
        scan(taken | (U(1) << i), left & ~both[i]);
    }
  }
};
int main() {
  int k, n;
  while (cin >> k >> n) {
    if (n < 1 || n >= 64)
      return 2;
    Tree t;
    t.h.resize(n);
    for (int i = 0; i < n; i++)
      if (!(cin >> t.h[i]) || t.h[i] >= (U(1) << n) || (t.h[i] & (U(1) << i)))
        return 2;
    for (int i = 0; i < n; i++) {
      U ct = 0;
      for (int j = 0; j < n; j++)
        if (t.h[j] >> i & 1)
          ct |= U(1) << j;
      t.a.push_back(t.h[i] | ct);
      t.both.push_back(t.h[i] & ct);
    }
    t.scan(0, (U(1) << n) - 1);
    for (int i = 8; i <= t.high; i++) {
      cerr << k << " " << i << " " << t.types[i].size() << endl;
      for (auto &s : t.types[i])
        cout << k << " " << i << " " << s << "\n";
    }
    cout << flush;
  }
}

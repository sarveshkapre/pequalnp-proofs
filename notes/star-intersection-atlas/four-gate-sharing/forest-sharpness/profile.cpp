// Injective representation in a bipartite host whose vertices are row/column
// profiles. After fixing rows, columns with the same partial neighborhood
// share a domain. Those domains are disjoint, so cardinality is exact.
#include <bitset>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
using Types = bitset<128>;
using Rows = uint32_t;
int pop(Rows x) { return __builtin_popcount(x); }
struct Part {
  Rows columns;
  Types types;
};
struct Search {
  int m, n, t;
  vector<Rows> graph;
  vector<Types> edge;
  long long visits = 0;
  bool fits(Rows cells, const Types &host, const vector<Part> &parts) const {
    for (const auto &p : parts) {
      int need = pop(cells & p.columns);
      int available = (p.types & host).count();
      if (available < need ||
          int(p.types.count()) - available < pop(p.columns) - need)
        return false;
    }
    return true;
  }
  bool search(Rows remaining, Types usable, const vector<Part> &parts) {
    ++visits;
    if (!remaining)
      return true;
    int best = -1;
    vector<int> chosen;
    for (Rows v = remaining; v; v &= v - 1) {
      int i = __builtin_ctz(v);
      vector<int> options;
      for (int h = 0; h < t; h++)
        if (usable[h] && fits(graph[i], edge[h], parts)) {
          options.push_back(h);
          // This row cannot improve the current minimum; its discarded
          // options are never used as a branch domain.
          if (best >= 0 && options.size() >= chosen.size())
            break;
        }
      if (options.empty())
        return false;
      if (best < 0 || options.size() < chosen.size()) {
        best = i;
        chosen.swap(options);
      }
    }
    for (int h : chosen) {
      vector<Part> next;
      for (const auto &p : parts) {
        Rows yes = p.columns & graph[best], no = p.columns & ~graph[best];
        if (yes)
          next.push_back({yes, p.types & edge[h]});
        if (no)
          next.push_back({no, p.types & ~edge[h]});
      }
      Types available = usable;
      available.reset(h);
      if (search(remaining ^ (1U << best), available, next))
        return true;
    }
    return false;
  }
  bool run() {
    Types all;
    for (int j = 0; j < t; j++)
      all.set(j);
    return search((1U << m) - 1, all, {{(1U << n) - 1, all}});
  }
};
int main() {
  int tag, m, n, t;
  while (cin >> tag >> m >> n >> t) {
    if (m < 1 || n < 1 || m > 24 || n > 24 || t < 1 || t > 128)
      return 2;
    Search s{m, n, t, vector<Rows>(m), vector<Types>(t)};
    for (auto &r : s.graph) {
      unsigned x;
      if (!(cin >> x) || x >= (1U << n))
        return 2;
      r = x;
    }
    for (auto &r : s.edge) {
      string x;
      if (!(cin >> x) || int(x.size()) != t ||
          x.find_first_not_of("01") != string::npos)
        return 2;
      r = Types(x);
    }
    bool fit = s.run();
    cout << tag << " " << fit << " " << s.visits << endl;
  }
}

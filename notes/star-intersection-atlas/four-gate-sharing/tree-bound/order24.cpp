#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <map>
#include <set>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>
using namespace std;
using Mask = uint32_t;
using Rows = vector<Mask>;
using Words = vector<int>;
int count(Mask x) { return __builtin_popcount(x); }
int first(Mask x) { return __builtin_ctz(x); }
Mask bit(int i) { return Mask(1) << i; }
// Components after contracting each matched edge.
struct Groups {
  array<int, 12> name{};
  int number;
  explicit Groups(int n) : number(n) {
    for (int i = 0; i < n; i++)
      name[i] = i;
  }
  bool join(int a, int b) {
    int x = name[a], y = name[b];
    if (x == y)
      return false;
    for (auto &g : name)
      if (g == y)
        g = x;
    --number;
    return true;
  }
  bool joinAll(Mask endpoints) {
    int j = first(endpoints);
    endpoints &= endpoints - 1;
    for (; endpoints; endpoints &= endpoints - 1)
      if (!join(j, first(endpoints)))
        return false;
    return true;
  }
};
struct Connector {
  int word, side;
  Mask neighbors;
};
struct Host {
  array<bool, 256> f{};
  array<int, 256> type{};
  Words reps;
  Host(const string &s) {
    if (s.size() != 256 || s.find_first_not_of("01") != string::npos)
      throw runtime_error("invalid scalar table");
    for (int i = 0; i < 256; i++)
      f[i] = s[i] == '1';
    map<string, int> ids;
    for (int x = 0; x < 256; x++) {
      string sign;
      for (int y = 0; y < 256; y++)
        sign += f[x & y] ? '1' : '0';
      if (!ids.count(sign)) {
        ids[sign] = x;
        if (f[x])
          reps.push_back(x);
      }
      type[x] = ids[sign];
    }
  }
  Mask neighbors(int x, const Words &side) const {
    Mask result = 0;
    for (int j = 0; j < (int)side.size(); j++)
      if (!f[x & side[j]])
        result |= bit(j);
    return result;
  }
  Words options(int x, const Words &normalizedOpp, Mask target) const {
    set<int> words;
    for (int y = x;; y = (y - 1) & x) {
      if (f[y] && !(neighbors(y, normalizedOpp) & ~target))
        words.insert(type[y]);
      if (!y)
        break;
    }
    return Words(words.begin(), words.end());
  }
};
string rooted(const array<Mask, 32> &adj, int v, int parent) {
  vector<string> branches;
  for (Mask ns = adj[v]; ns; ns &= ns - 1) {
    int k = first(ns);
    if (k != parent)
      branches.push_back(rooted(adj, k, v));
  }
  sort(branches.begin(), branches.end());
  string code = "(";
  for (auto &s : branches)
    code += s;
  return code + ")";
}
string shape(const Rows &rows, int n, int components) {
  int m = rows.size(), v = m + n;
  array<Mask, 32> adj{};
  for (int i = 0; i < m; i++) {
    adj[i] = rows[i] << m;
    for (Mask ns = rows[i]; ns; ns &= ns - 1)
      adj[m + first(ns)] |= bit(i);
  }
  auto component_code = [&](Mask component, int flip) {
    Mask core = component;
    while (count(core) > 2) {
      Mask leaves = 0;
      for (Mask left = core; left; left &= left - 1) {
        int u = first(left);
        if (count(adj[u] & core) == 1)
          leaves |= bit(u);
      }
      if (!leaves)
        throw runtime_error("target contains a cycle");
      core ^= leaves;
    }
    string a = rooted(adj, first(core), -1);
    if (a.size() != 2 * unsigned(count(component)))
      throw runtime_error("disconnected target");
    if (flip >= 0)
      a = char('0' + ((first(core) >= m) ^ flip)) + a;
    core &= core - 1;
    if (!core)
      return a;
    string b = rooted(adj, first(core), -1);
    if (flip >= 0)
      b = char('0' + ((first(core) >= m) ^ flip)) + b;
    return min(a, b);
  };
  Mask all = bit(v) - 1;
  if (components == 1)
    return component_code(all, -1);
  vector<string> codes[2];
  for (Mask left = all; left;) {
    Mask visit = bit(first(left)), part = visit;
    while (visit) {
      int j = first(visit);
      visit &= visit - 1;
      Mask fresh = adj[j] & ~part;
      part |= fresh;
      visit |= fresh;
    }
    left &= ~part;
    for (int flip = 0; flip < 2; flip++)
      codes[flip].push_back(component_code(part, flip));
  }
  if (int(codes[0].size()) != components)
    throw runtime_error("invalid component count");
  string labels[2];
  for (int flip = 0; flip < 2; flip++) {
    sort(codes[flip].begin(), codes[flip].end());
    for (const auto &word : codes[flip])
      labels[flip] += word;
  }
  return min(labels[0], labels[1]);
}
set<string> withoutRestored, withRestored;
bool audit = false;
struct Census {
  const Host &h;
  int id, k, u, components;
  Words A, B, r, c;
  Rows base, target, transpose;
  vector<Words> opts;
  Words order;
  long long lifts = 0, restored = 0, completions = 0;
  unordered_map<string, string> &known;
  set<string> &found;
  Census(const Host &host, int index, Words a, Words b, int size,
         int component_count, unordered_map<string, string> &seen,
         set<string> &codes)
      : h(host), id(index), k(a.size()), u(size - 2 * k),
        components(component_count), A(a), B(b), r(k, -1), c(k, -1),
        known(seen), found(codes) {
    for (int x : A)
      base.push_back(h.neighbors(x, B));
  }
  void complete(const vector<Connector> &sel) {
    Rows rows = target;
    int n = k;
    for (auto x : sel)
      if (x.side == 0)
        rows.push_back(x.neighbors);
      else {
        for (Mask s = x.neighbors; s; s &= s - 1)
          rows[first(s)] |= bit(n);
        ++n;
      }
    ++completions;
    // The matched edge at each leaf makes equal leaf neighborhoods impossible.
    string key;
    key += char(n);
    for (auto mask : rows) {
      key += char(mask);
      key += char(mask >> 8);
    }
    auto it = known.find(key);
    if (it == known.end())
      it = known.emplace(key, shape(rows, n, components)).first;
    (target == base ? withoutRestored : withRestored).insert(it->second);
    if (found.insert(it->second).second) {
      cout << id << " " << it->second;
      if (audit) {
        Words xs = r, ys = c;
        for (const auto &connector : sel)
          (connector.side ? ys : xs).push_back(connector.word);
        cout << " " << xs.size();
        for (const auto &shore : {xs, ys})
          for (int word : shore)
            cout << " " << word;
      }
      cout << "\n";
    }
  }
  // Add distinct exposed vertices, preserving the induced graph and acyclicity.
  void connect(const vector<Connector> &pool, int start, Groups groups,
               vector<Connector> &sel) {
    int needed = u - int(sel.size());
    if (!needed) {
      if (groups.number == components)
        complete(sel);
      return;
    }
    for (int j = start; j + needed <= (int)pool.size(); j++) {
      auto x = pool[j];
      if (count(x.neighbors) > groups.number - needed + 2 - components)
        continue;
      auto next = groups;
      if (!next.joinAll(x.neighbors))
        continue;
      bool independent = true;
      for (auto y : sel)
        if (x.side != y.side && !h.f[x.word & y.word]) {
          independent = false;
          break;
        }
      if (!independent)
        continue;
      sel.push_back(x);
      connect(pool, j + 1, next, sel);
      sel.pop_back();
    }
  }
  // Alternative completion test: account for every edge, then count components
  // on the actual graph. A graph with v vertices and v-c edges is a forest
  // precisely when it has c components. This branch never contracts a matching.
  void auditChoices(const vector<Connector> &pool, int start, int edgesLeft,
                    vector<Connector> &sel) {
    const int need = u - int(sel.size());
    if (edgesLeft < 2 * need)
      return;
    if (need == 0) {
      if (edgesLeft)
        return;
      array<Mask, 32> adj{};
      auto edge = [&](int a, int b) {
        adj[a] |= bit(b);
        adj[b] |= bit(a);
      };
      for (int i = 0; i < k; ++i)
        for (Mask s = target[i]; s; s &= s - 1)
          edge(i, k + first(s));
      for (int i = 0; i < u; ++i) {
        const auto &x = sel[i];
        for (Mask s = x.neighbors; s; s &= s - 1)
          edge(2 * k + i, (x.side ? 0 : k) + first(s));
      }
      int parts = 0;
      Mask left = bit(2 * k + u) - 1;
      while (left) {
        ++parts;
        Mask active = bit(first(left));
        left ^= active;
        while (active) {
          int i = first(active);
          active &= active - 1;
          Mask fresh = left & adj[i];
          left ^= fresh;
          active |= fresh;
        }
      }
      if (parts == components)
        complete(sel);
      return;
    }
    for (int j = start; j + need <= int(pool.size()); ++j) {
      const auto &x = pool[j];
      if (count(x.neighbors) > edgesLeft - 2 * (need - 1))
        continue;
      if (any_of(sel.begin(), sel.end(), [&](const auto &y) {
            return x.side != y.side && !h.f[x.word & y.word];
          }))
        continue;
      sel.push_back(x);
      auditChoices(pool, j + 1, edgesLeft - count(x.neighbors), sel);
      sel.pop_back();
    }
  }
  void extend(Groups groups) {
    ++lifts;
    if (target != base)
      ++restored;
    vector<Connector> pool, sel;
    if (audit) {
      int edgesLeft = 2 * k + u - components;
      for (Mask row : target)
        edgesLeft -= count(row);
      for (int side = 0; side < 2; ++side)
        for (int word : h.reps) {
          Mask ns = h.neighbors(word, side ? r : c);
          if (count(ns) >= 2 && count(ns) <= edgesLeft - 2 * (u - 1))
            pool.push_back({word, side, ns});
        }
      auditChoices(pool, 0, edgesLeft, sel);
      return;
    }
    for (int side = 0; side < 2; side++)
      for (int x : h.reps) {
        Mask ns = h.neighbors(x, side ? r : c);
        int d = count(ns);
        if (d < 2 || d > groups.number - u + 2 - components)
          continue;
        auto g = groups;
        if (g.joinAll(ns))
          pool.push_back({x, side, ns});
      }
    connect(pool, 0, groups, sel);
  }
  // Rows and columns may both shrink. Enforce every prescribed cell jointly.
  void assign(int p, Groups groups) {
    if (p == 2 * k) {
      extend(groups);
      return;
    }
    int v = order[p], j = v % k;
    bool row = v < k;
    for (int x : opts[v]) {
      const Words &opp = row ? c : r;
      bool good = true;
      Mask wanted = row ? target[j] : transpose[j];
      for (int i = 0; i < k; i++)
        if (opp[i] >= 0 && (!h.f[x & opp[i]]) != bool(wanted & bit(i))) {
          good = false;
          break;
        }
      if (good) {
        (row ? r : c)[j] = x;
        assign(p + 1, groups);
        (row ? r : c)[j] = -1;
      }
    }
  }
  void solve(Rows wanted) {
    Groups groups(k);
    transpose.assign(k, 0);
    target = wanted;
    for (int i = 0; i < k; i++)
      for (Mask s = target[i]; s; s &= s - 1) {
        int j = first(s);
        transpose[j] |= bit(i);
        if (i != j && !groups.join(i, j))
          return;
      }
    if (groups.number < u + components)
      return;
    opts.assign(2 * k, {});
    order.clear();
    for (int j = 0; j < k; j++) {
      opts[j] = h.options(A[j], B, target[j]);
      opts[k + j] = h.options(B[j], A, transpose[j]);
      order.push_back(j);
      order.push_back(k + j);
    }
    stable_sort(order.begin(), order.end(),
                [&](int a, int b) { return opts[a].size() < opts[b].size(); });
    assign(0, groups);
  }
  void run(int t) {
    solve(base);
    // One extra contact can survive only when the order plus component count
    // is 25.
    if (k == 10 && t == 4 && 2 * k + u + components == 25)
      for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
          if (!(base[i] & bit(j))) {
            auto wanted = base;
            wanted[i] |= bit(j);
            solve(wanted);
          }
  }
};
int main(int argc, char **argv) {
  int size = 24, components = 1;
  if (argc == 3 || argc == 4) {
    if (argc == 4 && string(argv[3]) != "--audit")
      return 2;
    audit = argc == 4;
    size = stoi(argv[1]);
    components = stoi(argv[2]);
    if (!((size == 24 && components == 2) ||
          (size == 23 && (components == 2 || components == 3))))
      return 2;
  } else if (argc != 1)
    return 2;
  for (int h = 0; h < 5; h++) {
    string s;
    int n;
    if (!(cin >> s >> n) || n < 0 || n > 500)
      return 2;
    Host host(s);
    set<string> catalogue;
    long long lifts = 0, restored = 0, complete = 0;
    for (int i = 0; i < n; i++) {
      int k, t;
      if (!(cin >> k >> t) || (k != 10 && k != 11))
        return 2;
      Words a(k), b(k);
      for (int j = 0; j < k; j++)
        if (!(cin >> a[j] >> b[j]) || a[j] < 0 || a[j] > 255 || b[j] < 0 ||
            b[j] > 255)
          return 2;
      unordered_map<string, string> seen;
      Census c(host, h, a, b, size, components, seen, catalogue);
      c.run(t);
      lifts += c.lifts;
      restored += c.restored;
      complete += c.completions;
    }
    cout.flush();
    cerr << "Host " << h + 1 << " " << n << " seeds, " << lifts << " lifts ("
         << restored << " restored), " << complete << " completions, "
         << catalogue.size() << " shapes\n";
  }
  int only = 0;
  for (auto &x : withRestored)
    if (!withoutRestored.count(x))
      ++only;
  cerr << "Unique to restored: " << only
       << " union of others: " << withoutRestored.size() << "\n";
}

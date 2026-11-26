// Forward census of all nonleaf deletions, independently of the connector
// search. Each component is rooted at a centroid (by size); both global
// orientations survive.
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <set>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;
using Mask = uint32_t;
int first(Mask x) { return __builtin_ctz(x); }
int sizeOf(Mask x) { return __builtin_popcount(x); }
Mask bit(int v) { return Mask(1) << v; }

struct Tree {
  vector<Mask> adj;
  vector<unsigned> side;
  explicit Tree(const string &s) {
    vector<int> stack;
    for (char ch : s) {
      if (ch == ')') {
        if (stack.empty())
          throw runtime_error("unbalanced tree");
        stack.pop_back();
        continue;
      }
      if (ch != '(' || adj.size() >= 25)
        throw runtime_error("invalid tree");
      int v = adj.size();
      adj.push_back(0);
      side.push_back(stack.size() % 2);
      if (!stack.empty()) {
        int p = stack.back();
        adj[p] |= bit(v);
        adj[v] |= bit(p);
      }
      stack.push_back(v);
    }
    if (!stack.empty())
      throw runtime_error("unbalanced tree");
  }
  Mask reach(int v, Mask allowed) const {
    Mask active = bit(v), seen = active;
    while (active) {
      int i = first(active);
      active &= active - 1;
      Mask fresh = adj[i] & allowed & ~seen;
      active |= fresh;
      seen |= fresh;
    }
    return seen;
  }
  string rooted(int v, Mask part) const {
    vector<string> children;
    part &= ~bit(v);
    for (Mask s = part & adj[v]; s; s &= s - 1)
      children.push_back(rooted(first(s), part));
    sort(children.begin(), children.end());
    string result = "(";
    for (auto &child : children)
      result += child;
    return result + ")";
  }
  string code(Mask remaining) const {
    vector<string> pieces[2];
    while (remaining) {
      Mask part = reach(first(remaining), remaining);
      remaining ^= part;
      string choice[2];
      for (Mask s = part; s; s &= s - 1) {
        int v = first(s);
        bool central = true;
        for (Mask children = adj[v] & part; children; children &= children - 1)
          if (2 * sizeOf(reach(first(children), part & ~bit(v))) >
              sizeOf(part)) {
            central = false;
            break;
          }
        if (!central)
          continue;
        string word = rooted(v, part);
        for (int f = 0; f < 2; f++) {
          string colored = char('0' + (side[v] ^ f)) + word;
          if (choice[f].empty() || colored < choice[f])
            choice[f] = colored;
        }
      }
      for (int f = 0; f < 2; f++)
        pieces[f].push_back(choice[f]);
    }
    string label[2];
    for (int f = 0; f < 2; f++) {
      sort(pieces[f].begin(), pieces[f].end());
      for (auto &piece : pieces[f])
        label[f] += piece;
    }
    return min(label[0], label[1]);
  }
  void puncture(unordered_map<string, bool> &extensions, bool positive) const {
    Mask all = bit(adj.size()) - 1;
    for (int v = 0; v < int(adj.size()); ++v) {
      if (sizeOf(adj[v]) < 2)
        continue;
      Mask rest = all ^ bit(v), supports = 0;
      bool valid = true;
      for (Mask s = rest; s; s &= s - 1) {
        Mask ns = adj[first(s)] & rest;
        if (!ns || (sizeOf(ns) == 1 && (ns & supports))) {
          valid = false;
          break;
        }
        if (sizeOf(ns) == 1)
          supports |= ns;
      }
      if (valid) {
        auto [it, fresh] = extensions.emplace(code(rest), positive);
        if (!fresh && positive)
          it->second = true;
      }
    }
  }
};

int main() {
  unordered_map<string, bool> extensions;
  string word;
  int positive;
  while (cin >> positive >> word)
    Tree(word).puncture(extensions, positive != 0);
  set<string> unknown;
  for (const auto &item : extensions)
    if (!item.second)
      unknown.insert(item.first);
  for (const auto &label : unknown)
    cout << label << "\n";
  cerr << extensions.size() << " distinct colored forests; " << unknown.size()
       << " without a positive extension.\n";
}

// Offline exhaustive projection for the residual edges ab, bc, de.
// Bit i of a truth table represents the assignment with 5-bit mask i.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

namespace {
using Table = std::uint32_t;
constexpr unsigned A = 1, B = 2, C = 4, D = 8, E = 16;
constexpr std::array<unsigned, 9> ordinary{0, A, B, C, D, E, A|D, C|D, B|E};
constexpr std::array<unsigned, 2> c_guarded{C, C|D};
std::array<Table, 32> literals{};
Table target, edge_rows;
bool c_is_center, has_ce;

struct Wire {
    Table table;
    unsigned raw;
    bool nonempty;  // Raw support before projection.
    bool operator<(const Wire& w) const {
        if (table != w.table) return table < w.table;
        if (raw != w.raw) return raw < w.raw;
        return nonempty < w.nonempty;
    }
    bool operator==(const Wire& w) const {
        return table == w.table && raw == w.raw && nonempty == w.nonempty;
    }
};
struct Gate { char op; Wire wire; };
std::array<Gate, 5> gates;
std::uint64_t visited;
std::string order;

Wire combine(char op, Wire x, Wire y) {
    if (op == 'A') return {x.table & y.table, 0, false};
    return {x.table | y.table, x.raw | y.raw, x.nonempty || y.nonempty};
}

Wire base(unsigned support) {
    return {literals[support], support, true};
}

std::vector<Wire> ports(unsigned used) {
    std::vector<Wire> wires;
    for (unsigned raw : ordinary) {
        std::vector<Table> choices{literals[raw]};
        for (unsigned i = 0; i < used; ++i) {
            const auto& g = gates[i];
            if (g.op != 'O' || !g.wire.nonempty || (g.wire.raw & ~raw)) continue;
            auto n = choices.size();
            for (size_t j = 0; j < n; ++j) choices.push_back(choices[j] | g.wire.table);
        }
        for (Table table : choices) wires.push_back({table, raw, true});
    }
    for (unsigned i = 0; i < used; ++i) wires.push_back(gates[i].wire);
    std::sort(wires.begin(), wires.end());
    wires.erase(std::unique(wires.begin(), wires.end()), wires.end());
    return wires;
}

bool covers(unsigned used) {
    // Enumerate unions of any subset of the globally raw-bearing exceptional ORs.
    // The spare slot permits the three-OR positive control.
    std::array<Wire, 8> subsets{};
    unsigned count = 1;
    for (unsigned i = 0; i < used; ++i) {
        auto g = gates[i];
        if (g.op != 'O' || !g.wire.nonempty) continue;
        for (unsigned j = 0; j < count; ++j) subsets[count+j] = combine('O', subsets[j], g.wire);
        count *= 2;
    }

    Table outside = 0;
    for (unsigned i = 0; i < used; ++i) {
        auto g = gates[i];
        if (g.op != 'O' || !g.wire.nonempty || g.wire.raw != 0) continue;
        const Table s = g.wire.table;
        if ((s & ~target) == 0) {
            outside |= s;  // Grant all positives of a safe source without requiring a leaf.
            continue;
        }
        if (c_is_center && (s & ~target & ~literals[C])) continue;
        // If c is outside Z then an unsafe s can only reach a top whose private
        // leaf is c. Otherwise its centre-facing source rejects every c-off negative.
        // Deliberately allow different guard choices for different positive rows.
        for (unsigned raw : ordinary) {
            if (!c_is_center && raw != c_guarded[0] && raw != c_guarded[1]) continue;
            for (unsigned leaf = 0; leaf < count; ++leaf) {
                if (subsets[leaf].raw & ~raw) continue;
                const Table term = s & (literals[raw] | subsets[leaf].table);
                if ((term & ~target) == 0) outside |= term;
            }
        }
    }
    if ((outside & edge_rows) == edge_rows) return true;
    if (!c_is_center) return false;
    // c labels only one top, whose centre and leaf operands must be fixed.
    for (unsigned center = 0; center < count; ++center) {
        if (subsets[center].raw & ~C) continue;
        for (unsigned raw : {0u, has_ce ? E : 0u}) {
            for (unsigned leaf = 0; leaf < count; ++leaf) {
                if (subsets[leaf].raw & ~raw) continue;
                const Table term = (literals[C] | subsets[center].table)
                                 & (literals[raw] | subsets[leaf].table);
                if ((term & ~target) == 0 && ((outside | term) & edge_rows) == edge_rows) {
                    return true;
                }
            }
        }
    }
    return false;
}

bool search(unsigned used) {
    if (used == order.size()) {
        ++visited;
        return covers(used);
    }
    const auto choices = ports(used);
    std::vector<Wire> seen;
    for (size_t i = 0; i < choices.size(); ++i) {
        for (size_t j = i; j < choices.size(); ++j) {
            auto w = combine(order[used], choices[i], choices[j]);
            auto it = std::lower_bound(seen.begin(), seen.end(), w);
            if (it != seen.end() && *it == w) continue;
            seen.insert(it, w);
            gates[used] = {order[used], w};
            if (search(used+1)) return true;
        }
    }
    return false;
}

constexpr Table row(unsigned r) { return Table(1) << r; }

void graph(bool inside, bool cross) {
    c_is_center = inside;
    has_ce = cross;
    target = (literals[A] & literals[B]) | (literals[B] & literals[C])
           | (literals[D] & literals[E]);
    edge_rows = row(A|B) | row(B|C) | row(D|E);
    if (cross) {
        target |= literals[C] & literals[E];
        edge_rows |= row(C|E);
    }
}

bool controls() {
    graph(false, false);
    unsigned n = 0;
    bool inputs_legal = true;
    auto add = [&](char op, Wire x, Wire y) {
        auto choices = ports(n);
        inputs_legal &= std::binary_search(choices.begin(), choices.end(), x)
                     && std::binary_search(choices.begin(), choices.end(), y);
        Wire w = combine(op, x, y);
        gates[n++] = {op, w};
        return w;
    };
    // One extra exceptional OR buys a+c; two ordinary outside literals
    // promote the two products. This control uses only admitted ports.
    Wire ac = add('O', base(A), base(C));
    Wire path = add('A', ac, base(B));
    Wire isolated = add('A', base(D), base(E));
    add('O', path, base(0));
    add('O', isolated, base(0));
    if (!inputs_legal || !covers(n)) return false;
    graph(true, false);
    if (!covers(n)) return false;
    graph(true, true);
    if (!covers(n)) return false; // The c-centred top can supply ce with its raw leaf.
    graph(false, false);
    std::cout << "positive controls: two ANDs, three ORs cover all three graph modes\n";
    // Two promoted sources b and de pass the three positive rows and both
    // complements of minimum covers. A single b must still be rejected.
    n=0;
    Wire b_copy = add('A', base(B), base(B));
    isolated = add('A', base(D), base(E));
    add('O', b_copy, base(0));
    add('O', isolated, base(0));
    Table weak = b_copy.table | isolated.table;
    if (!inputs_legal || (weak & edge_rows) != edge_rows
        || (weak & (row(A|C|D) | row(A|C|E))) || !(weak & row(B)) || covers(n)) return false;
    std::cout << "negative control: b or de passes two cover tests and fails the guarded model\n";
    return true;
}
}  // namespace

int main(int argc, char** argv) {
    for (unsigned support = 0; support < 32; ++support)
        for (unsigned r = 0; r < 32; ++r)
            if (r & support) literals[support] |= row(r);
    if (argc == 2 && std::string(argv[1]) == "controls") return controls() ? 0 : 1;
    if (argc != 3) return 2;
    const std::string mode = argv[1];
    order = argv[2];
    if ((mode != "outside" && mode != "inside" && mode != "cross") ||
        order.size() != 4 || std::count(order.begin(), order.end(), 'A') != 2 ||
        std::count(order.begin(), order.end(), 'O') != 2) return 2;
    graph(mode != "outside", mode == "cross");
    const bool found = search(0);
    std::cout << mode << ' ' << order << ' ' << (found ? "WITNESS" : "EXHAUSTED")
              << " leaves " << visited << '\n';
    return found ? 1 : 0;
}

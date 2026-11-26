// Compute the minimum number of cross edges on the endpoints of a forest matching.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

using Mask = std::uint64_t;

int count(Mask x) { return __builtin_popcountll(x); }
int first(Mask x) { return __builtin_ctzll(x); }
Mask bit(int i) { return Mask(1) << i; }

struct Catalogue {
    std::vector<Mask> links, forbidden;
    std::array<int, 12> minimum;
    unsigned long long extremalTen = 0;
    std::vector<Mask> tenEdgeSets;
    bool fourDisjointContacts = true;

    explicit Catalogue(const std::vector<Mask>& rows) : links(rows.size()), forbidden(rows.size()) {
        minimum.fill(100);
        for (unsigned i = 0; i < rows.size(); ++i) {
            if (!(rows[i] & bit(i))) throw std::runtime_error("missing diagonal");
            for (unsigned j = 0; j < rows.size(); ++j) {
                if (i == j) continue;
                bool outgoing = rows[i] & bit(j), incoming = rows[j] & bit(i);
                if (outgoing || incoming) links[i] |= bit(j);
                if (outgoing && incoming) forbidden[i] |= bit(j);
            }
        }
    }

    void visit(Mask selected, Mask available, int size, int contacts,
               const std::vector<Mask>& components) {
        if (size >= 9) minimum.at(size) = std::min(minimum.at(size), contacts);
        if (size == 10 && contacts == 4) {
            ++extremalTen;
            tenEdgeSets.push_back(selected);
            for (Mask c : components) if (count(c) > 2) fourDisjointContacts = false;
        }
        while (available && size + count(available) >= 9) {
            int v = first(available);
            available ^= bit(v);
            Mask neighbors = links[v] & selected, merged = bit(v);
            std::vector<Mask> next;
            bool cycle = false;
            for (Mask component : components) {
                Mask hits = neighbors & component;
                if (hits & (hits-1)) { cycle = true; break; }
                if (hits) merged |= component;
                else next.push_back(component);
            }
            if (cycle) continue;
            next.push_back(merged);
            visit(selected | bit(v), available & ~forbidden[v], size+1, contacts+count(neighbors), next);
        }
    }
};

int main() {
    const int expected[5][3] = {{3,4,8},{3,6,9},{3,4,8},{3,4,8},{3,4,8}};
    for (int h = 0; h < 5; ++h) {
        int n;
        if (!(std::cin >> n) || n < 11 || n > 63) return 2;
        std::vector<Mask> rows(n);
        for (auto& row : rows) if (!(std::cin >> row) || row >= bit(n)) return 2;
        Catalogue table(rows);
        table.visit(0, bit(n)-1, 0, 0, {});
        for (int k = 9; k <= 11; ++k) if (table.minimum[k] != expected[h][k-9]) return 1;
        if (!table.fourDisjointContacts || bool(table.extremalTen) != (h != 1)) return 1;
        for (Mask s : table.tenEdgeSets) std::cout << "case " << h << ' ' << s << '\n';
        std::cout << "Host " << h+1 << " minimum cross edges at sizes 9, 10, 11: "
                  << table.minimum[9] << ", " << table.minimum[10] << ", " << table.minimum[11]
                  << ". Size-10 configurations with four disjoint contacts: " << table.extremalTen << '\n';
    }
}

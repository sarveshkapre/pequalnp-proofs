// Exact minimum number of binary OR occurrences in a monotone separator.
// Input per case: ID, counts, minimal true inputs, maximal false inputs.
// Each input is an 8-bit mask. AND and input conjunctions are free.
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

using Mask = unsigned;

unsigned size_of(Mask mask) {
    return __builtin_popcount(mask);
}

unsigned solve(const std::vector<Mask>& on, const std::vector<Mask>& off) {
    // The DNF of selected positive points costs at most |on| - 1.
    for (auto x : on)
        for (auto y : off)
            if ((x & y) == x) throw std::invalid_argument("inseparable boundary");

    const Mask p_end = 1U << on.size(), q_end = 1U << off.size();
    std::vector<Mask> common(p_end, 255);
    std::vector<std::uint8_t> value(p_end * q_end);
    for (Mask p = 1; p < p_end; ++p) {
        common[p] = common[p & (p - 1)] & on[__builtin_ctz(p)];
        for (Mask q = 1; q < q_end; ++q) {
            // A single conjunction can exclude y exactly when a common input bit is absent in y.
            bool leaf = true;
            for (Mask pending = q; pending; pending &= pending-1) {
                Mask y = off[__builtin_ctz(pending)];
                if ((y & common[p]) == common[p]) {
                    leaf = false;
                    break;
                }
            }
            if (leaf) continue;
            unsigned best = size_of(p)-1;
            for (Mask a = (q-1) & q; a > (q^a); a = (a-1) & q) {
                // AND splits the negative inputs.
                unsigned cost = value[p*q_end+a] + value[p*q_end+(q^a)];
                best = std::min(best, cost);
            }
            for (Mask a = (p-1) & p; a > (p^a); a = (a-1) & p) {
                // OR splits the positive inputs.
                unsigned cost = 1 + value[a*q_end+q] + value[(p^a)*q_end+q];
                best = std::min(best, cost);
            }
            value[p*q_end+q] = static_cast<std::uint8_t>(best);
        }
    }
    return value.back();
}

int main() {
    unsigned id, positives, negatives, cases = 0;
    while (std::cin >> id >> positives >> negatives) {
        if (id != cases + 1 || !positives || !negatives || positives > 13 || negatives > 7)
            throw std::invalid_argument("unexpected boundary size");
        std::vector<Mask> on(positives), off(negatives);
        for (auto* points : {&on, &off}) {
            for (auto& x : *points)
                if (!(std::cin >> x) || x > 255) throw std::invalid_argument("invalid point");
        }
        auto cost = solve(on, off);
        std::cout << "Class " << id << ": symbolic minimum " << cost << '\n';
        if (cost != 6) return 1;
        ++cases;
    }
    return (std::cin.eof() && cases == 5) ? 0 : 1;
}

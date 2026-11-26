// Exact monotone synthesis on a small signed test set. The input describes
// each primary by the positive rows it accepts and the negative rows it rejects.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <utility>

using Mask = uint32_t;
using Negative = unsigned __int128;
struct Signal { Mask pos; Negative neg; };
struct Gate { int a, b; bool is_and; };
using Slots = std::array<int, 32>;
std::array<Signal, 48> wires;
std::array<Gate, 32> gates;
int positives, negatives, inputs, budget;
uint64_t visited = 0;
Mask all_pos;
Negative all_neg;

bool search(const Slots& live, int n, int depth, int first_pair) {
    ++visited;
    int extra = budget - depth - (n - 1);
    if (extra < 0 || depth == budget) return false;
    // Which comparisons can only one live wire separate?
    Mask private_pos[32]{};
    Negative private_neg[32]{};
    for (int p = 0; p < positives; ++p) {
        Negative once = 0, twice = 0;
        for (int i = 0; i < n; ++i) {
            auto w = wires[live[i]];
            if ((w.pos >> p) & 1) { twice |= once & w.neg; once |= w.neg; }
        }
        if (once != all_neg) return false;
        for (int i = 0; i < n; ++i) {
            auto w = wires[live[i]];
            if (!((w.pos >> p) & 1)) continue;
            Negative private_here = w.neg & ~twice;
            if (private_here) { private_pos[i] |= 1u << p; private_neg[i] |= private_here; }
        }
    }
    // Topologically sort ready gates by larger pin, then by smaller pin.
    // A newly ready gate reads a later wire than those already ready.
    for (int j = 1; j < n; ++j) for (int i = 0; i < j; ++i) {
        int a = live[i], b = live[j], pair = 48*b+a;
        if (pair < first_pair) continue;
        auto x = wires[a], y = wires[b];
        for (bool and_op : {false, true}) {
            Signal z = and_op ? Signal{x.pos & y.pos, x.neg | y.neg}
                              : Signal{x.pos | y.pos, x.neg & y.neg};
            if (!z.pos || !z.neg) continue;
            if (z.pos == all_pos && z.neg == all_neg) {
                gates[depth] = {a,b,and_op};
                for (int g=0; g<=depth; ++g)
                    std::cout << (gates[g].is_and ? "and " : "or ") << gates[g].a
                              << ' ' << gates[g].b << '\n';
                return true;
            }
            if (depth+1 == budget) continue;
            bool dominated = false;
            for (int k=0; k<inputs+depth; ++k)
                if (!(z.pos & ~wires[k].pos) && !(z.neg & ~wires[k].neg)) {
                    dominated = true; break;
                }
            if (dominated) continue;
            int required = and_op
                ? int(bool(private_pos[i] & ~z.pos)) + 2*int(bool(private_pos[j] & ~z.pos))
                : int(bool(private_neg[i] & ~z.neg)) + 2*int(bool(private_neg[j] & ~z.neg));
            for (int keep=0; keep<4; ++keep) {
                if ((keep & required) != required || __builtin_popcount(keep)>extra) continue;
                Slots next;
                int len = 0;
                for (int k=0;k<n;++k)
                    if ((k!=i || (keep&1)) && (k!=j || (keep&2))) next[len++] = live[k];
                const int id = inputs + depth;
                wires[id]=z;
                gates[depth]={a,b,and_op};
                next[len++]=id;
                if (search(next,len,depth+1,pair)) return true;
            }
        }
    }
    return false;
}

int main() {
    if (!(std::cin >> positives >> negatives >> inputs >> budget) ||
        positives<1 || negatives<1 || positives>31 || negatives>127 ||
        inputs<2 || inputs>20 || budget<1 || budget>24 || inputs+budget>48) return 2;
    all_pos=(1u<<positives)-1; all_neg=(Negative(1)<<negatives)-1;
    Slots live;
    for(int i=0;i<inputs;++i) {
        uint64_t low, high;
        if (!(std::cin >> wires[i].pos >> low >> high)) return 2;
        wires[i].neg=Negative(high)<<64 | low;
        live[i]=i;
        if(wires[i].pos==all_pos && wires[i].neg==all_neg) {
            std::cout << "INPUT " << i << '\n'; return 0;
        }
    }
    bool found=search(live,inputs,0,0);
    std::cout << (found?"FOUND ":"EXHAUSTED ") << visited << '\n';
}

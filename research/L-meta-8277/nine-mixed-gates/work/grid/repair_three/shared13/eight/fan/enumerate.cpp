// Enumerate commutative AND/OR trees with one subexpression used twice.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <tuple>
#include <vector>

using Truth = __uint128_t;
using Counts = std::array<int, 3>;  // ordinary point leaves, line leaves, shared markers
using Key = std::tuple<int, Counts>;
using Codes = std::array<uint32_t, 8>;
struct Witness { std::string lower, upper; };
struct Profile { unsigned multiplicity = 0; Witness first; };

std::map<Key, std::vector<std::string>> memo;

const std::vector<std::string>& expressions(Counts n, int sharedType) {
    Key key{sharedType, n};
    auto [it, fresh] = memo.try_emplace(key);
    auto& out = it->second;
    if (!fresh) return out;
    const auto [p, l, s] = n;
    if (p+l+s == 1) {
        out.push_back(p ? "p" : l ? "l" : "s");
        return out;
    }
    if (!(p || (s && (sharedType & 1))) || !(l || (s && (sharedType & 2)))) return out;
    for (int i=0; i<=p; ++i) for (int j=0; j<=l; ++j) for (int k=0; k<=s; ++k) {
        Counts a{i,j,k}, b{p-i,l-j,s-k};
        if (!(i+j+k) || a>b) continue;
        const auto& left = expressions(a, sharedType);
        const auto& right = expressions(b, sharedType);
        for (const auto& u : left) for (const auto& v : right) {
            if (a == b && u > v) continue;
            out.push_back("&"+u+v);
            out.push_back("|"+u+v);
        }
    }
    return out;
}

struct State {
    std::array<Truth, 3> points;
    std::array<Truth, 5> lines;
    Truth shared = 0;
    int pc = 0, lc = 0;
    Truth eval(const std::string& expr, size_t& off) {
        char op = expr.at(off++);
        if (op=='p') return points.at(pc++);
        if (op=='l') return lines.at(lc++);
        if (op=='s') return shared;
        Truth a = eval(expr,off);
        Truth b = eval(expr,off);
        assert(op=='&' || op=='|');
        return op=='&' ? a&b : a|b;
    }
};

int main(int argc, char** argv) {
    if (argc!=3) { std::cerr << "usage: enumerator LINE_WIDTH OUTPUT.tsv\n"; return 2; }
    int lines = std::stoi(argv[1]);
    assert(lines >= 3 && lines <= 5);
    int unitWidth = 1<<lines;
    auto& log = std::cout;
    State seed{};
    for (int row=0; row<4; ++row) for (int code=0; code<unitWidth; ++code) {
        Truth word = Truth{1} << (row*unitWidth + code);
        if (row) seed.points[row-1] |= word;
        for (int i=0;i<lines;++i) if ((code>>i)&1) seed.lines[i] |= word;
    }
    uint32_t all = lines==5 ? UINT32_MAX : ((uint32_t{1}<<unitWidth)-1);
    std::array<std::map<Codes, Profile>, 2> answers;
    unsigned total=0;
    for (int p=0; p<=3; ++p) for (int l=0; l<=lines; ++l) {
        if (!p && !l) continue;
        int type = (p ? 1 : 0) + (l ? 2 : 0);
        const auto& bottoms = expressions({p,l,0},0);
        const auto& tops = expressions({3-p,lines-l,2},type);
        unsigned number=0;
        for (const std::string& bottom : bottoms) {
            State sub = seed;
            size_t cursor=0;
            sub.shared = sub.eval(bottom,cursor);
            assert(cursor==bottom.size());
            for (const std::string& top : tops) {
                State finish = sub;
                cursor=0;
                Truth table=finish.eval(top,cursor);
                assert(cursor==top.size() && finish.pc==3 && finish.lc==lines);
                ++number;
                uint32_t zero = uint32_t(table)&all;
                std::array<uint32_t,3> vals{};
                for (int i=0;i<3;++i) vals[i]=uint32_t(table >> ((i+1)*unitWidth))&all;
                if ((zero|vals[0]|vals[1]|vals[2])&1) continue;
                Codes codes{};
                for (int m=1; m<8; ++m) {
                    uint32_t allowed = all & ~zero;
                    for (int i=0;i<3;++i) allowed &= ((m>>i)&1) ? vals[i] : ~vals[i];
                    codes[m]=allowed;
                }
                if (!codes[1] || !codes[2] || !codes[4]) continue;
                for (int shape=0; shape<2; ++shape) {
                    Codes kept=codes;
                    if (shape==0) {
                        if (!codes[7]) continue;
                        kept[3]=kept[5]=kept[6]=0;
                    } else {
                        if (!codes[3] || !codes[5] || !codes[6]) continue;
                        kept[7]=0;
                    }
                    auto& result=answers[shape][kept];
                    if (result.multiplicity++ == 0) result.first={bottom,top};
                }
            }
        }
        if (number) log << "reused subtree " << p << " point, " << l << " line: " << number << "\n";
        total+=number;
    }
    std::ofstream f(argv[2]);
    for (int s=0;s<2;++s) {
        unsigned feasible=0;
        for (auto& [k, v] : answers[s]) {
            f << (s?"013":"012") << '\t' << v.multiplicity << '\t' << v.first.lower << '\t' << v.first.upper;
            for (auto x:k) f << '\t' << x;
            f << '\n';
            feasible+=v.multiplicity;
        }
        log << (s?"013":"012") << ": " << feasible << " feasible expression pairs, "
            << answers[s].size() << " distinct labeled code constraints\n";
    }
    log << "expression pairs " << total << "\n";
    return f ? 0 : 1;
}

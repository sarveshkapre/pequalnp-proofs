// Separate exhaustion check. Work with ordinary truth values on both signs.
// Do not sort the smaller pins or discard gates dominated by earlier signals.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>

using Word = unsigned __int128;
struct Column { uint32_t yes; Word no; };
struct Entry { Column value; int id; };
using State = std::array<Entry,32>;
unsigned npos, nneg, nsrc, maxg;
uint32_t target;
Word mask;
uint64_t calls;
std::array<std::array<int,3>,32> chosen;

bool solve(const State& state, int size, unsigned used, int previous) {
    ++calls;
    if (used == maxg || used+size-1>maxg) return false;
    // For each positive, intersect the negative truth columns of every source
    // on at that positive. Dropping a wire is legal only if no negative makes
    // all those available sources true. Compute the comparisons unique to
    // each source by prefix/suffix intersections, without counting covers.
    uint32_t forced_yes[32]{};
    Word forced_no[32]{};
    for (unsigned p=0; p<npos; ++p) {
        Word prefix[33], suffix=mask;
        prefix[0]=mask;
        for(int i=0;i<size;++i) {
            Column c=state[i].value;
            prefix[i+1]=prefix[i] & ((c.yes>>p&1)? c.no : mask);
        }
        if (prefix[size]) return false;
        for(int i=size-1;i>=0;--i) {
            Column c=state[i].value;
            if(c.yes>>p&1) {
                Word witness=prefix[i]&suffix;
                if(witness) { forced_yes[i]|=1u<<p; forced_no[i]|=witness; }
                suffix&=c.no;
            }
        }
    }
    for(int right=1;right<size;++right) {
        if(state[right].id<previous) continue;
        for(int left=0;left<right;++left) {
            auto x=state[left].value, y=state[right].value;
            for(int op=0;op<2;++op) {
                Column z=op ? Column{x.yes&y.yes,x.no&y.no} : Column{x.yes|y.yes,x.no|y.no};
                if(!z.yes || z.no==mask) continue;
                if(z.yes==target && !z.no) {
                    chosen[used]={op,state[left].id,state[right].id};
                    for(unsigned g=0;g<=used;++g) {
                        auto row=chosen[g];
                        std::cout<<(row[0]?"and ":"or ")<<row[1]<<' '<<row[2]<<'\n';
                    }
                    return true;
                }
                // If an operand is as good as this gate on every signed test,
                // the gate can be bypassed in a size-minimal circuit.
                if((!(z.yes&~x.yes) && !(x.no&~z.no)) ||
                   (!(z.yes&~y.yes) && !(y.no&~z.no))) continue;
                bool needs_left=(forced_yes[left]&~z.yes) || (forced_no[left]&z.no);
                bool needs_right=(forced_yes[right]&~z.yes) || (forced_no[right]&z.no);
                for(int drop=0;drop<4;++drop) {
                    if((needs_left && (drop&1)) || (needs_right && (drop&2))) continue;
                    int next_size=size+1-__builtin_popcount(drop);
                    if(used+next_size>maxg) continue;
                    State next;
                    int idx=0;
                    for(int k=0;k<size;++k) {
                        if((k==left && (drop&1)) || (k==right && (drop&2))) continue;
                        next[idx++]=state[k];
                    }
                    chosen[used]={op,state[left].id,state[right].id};
                    next[idx]={z,int(nsrc+used)};
                    if(solve(next,next_size,used+1,state[right].id)) return true;
                }
            }
        }
    }
    return false;
}

int main() {
    if(!(std::cin>>npos>>nneg>>nsrc>>maxg) || npos<1 || npos>31 || nneg<1 || nneg>127 ||
       nsrc<2 || nsrc>20 || maxg<1 || maxg>24) return 2;
    target=(1u<<npos)-1; mask=(Word(1)<<nneg)-1;
    State pool;
    for(unsigned i=0;i<nsrc;++i) {
        uint32_t pos; uint64_t lo,hi;
        if(!(std::cin>>pos>>lo>>hi)) return 2;
        pool[i]={{pos,mask^(Word(hi)<<64 | lo)},int(i)};
        if(pos==target && !pool[i].value.no) { std::cout<<"INPUT "<<i<<'\n'; return 0; }
    }
    bool found=solve(pool,int(nsrc),0,-1);
    std::cout<<(found?"FOUND ":"EXHAUSTED ")<<calls<<'\n';
}

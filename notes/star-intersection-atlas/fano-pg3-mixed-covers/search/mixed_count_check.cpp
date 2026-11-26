// Count labeled 13-antichains independently by face rank. Fix the chosen
// vertices, select facets and squares, then count available edges binomially.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>
using U=unsigned;
using Counts=std::array<uint64_t,14>;
struct Choices {
    int k;
    std::vector<U> edges,squares,facets;
    std::vector<U> edgeBelow,squareBelowFacet,edgeBelowFacet;
    uint64_t binom[33][14]{};
    uint64_t squareSets(U allowed,U e,int need){
        // Every available edge has rank one, so all chosen edges are incomparable.
        uint64_t out=binom[std::popcount(e)][need];
        if(!need)return out;
        while(allowed){int i=std::countr_zero(allowed);allowed&=allowed-1;
            out+=squareSets(allowed,e&~edgeBelow[i],need-1);}
        return out;
    }
    uint64_t facetSets(U fs,U sq,U ed,int need){
        uint64_t out=squareSets(sq,ed,need);
        if(!need)return out;
        while(fs){int i=std::countr_zero(fs);fs&=fs-1;
            out+=facetSets(fs,sq&~squareBelowFacet[i],ed&~edgeBelowFacet[i],need-1);}
        return out;
    }
    Choices(U holes,int k_):k(k_){
        for(int n=0;n<=32;n++){binom[n][0]=1;if(n)for(int r=1;r<=13;r++)binom[n][r]=binom[n-1][r-1]+binom[n-1][r];}
        for(U fixed=1;fixed<16;fixed++)for(U s=0;s<16;s++)if(!(s&~fixed)){
            U f=0;for(U x=0;x<16;x++)if((x&fixed)==s)f|=1u<<x;
            if(f&~holes)continue;
            if(std::popcount(f)==2)edges.push_back(f);
            if(std::popcount(f)==4)squares.push_back(f);
            if(std::popcount(f)==8)facets.push_back(f);
        }
        auto below=[](U f,const std::vector<U>& a){U out=0;for(int i=0;i<int(a.size());i++)if(!(a[i]&~f))out|=1u<<i;return out;};
        for(U sq:squares)edgeBelow.push_back(below(sq,edges));
        for(U f:facets){squareBelowFacet.push_back(below(f,squares));edgeBelowFacet.push_back(below(f,edges));}
    }
    static U all(int n){return n==32?~0u:((1u<<n)-1);}
    uint64_t run(){return facetSets(all(facets.size()),all(squares.size()),all(edges.size()),k);}
};
int main(){
    std::array<int,4> perm={0,1,2,3};std::vector<std::array<int,16>> actions;
    do{for(int add=0;add<16;add++){std::array<int,16> a{};
        for(int x=0;x<16;x++){a[x]=add;for(int b=0;b<4;b++)if(x&(1<<b))a[x]^=1<<perm[b];}
        actions.push_back(a);
    }}while(std::next_permutation(perm.begin(),perm.end()));
    Counts total{};
    std::vector<bool> seen(65536);
    for(U h=0;h<65536;h++)if(!seen[h]&&std::popcount(h)>=3){
        int n=std::popcount(h)-3;
        uint64_t orbit=0;
        for(auto& a:actions){
            U moved=0;for(int i=0;i<16;i++)if(h&(1u<<i))moved|=1u<<a[i];
            if(!seen[moved])++orbit;seen[moved]=true;
        }
        total[n]+=orbit*Choices(h,n).run();
    }
    for(int i=0;i<=13;i++)std::cout<<i<<' '<<total[i]<<'\n';
}

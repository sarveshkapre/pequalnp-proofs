#pragma once
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <vector>
using Mask=unsigned;
constexpr Mask full=8191;
struct Action{
    std::array<Mask,128> lo{};
    std::array<Mask,64> hi{};
    Mask move(Mask x)const{return lo[x&127]|hi[x>>7];}
};
using Score=std::array<uint8_t,16>;
Score combine(const Score&a,const Score&b){
    Score r{};for(int i=0;i<16;++i)r[i]=std::min(a[i],b[i]);return r;
}
int sum(const Score&a){int n=0;for(auto v:a)n+=v;return n;}
inline int read_geometry(std::array<Mask,13>& rows, std::array<Mask,13>& col, std::vector<Action>& group) {
    for(auto&r:rows)if(!(std::cin>>r))return 2;
    for(int i=0;i<13;++i)for(int j=0;j<13;++j)col[j]|=((rows[i]>>j)&1)<<i;
    int start;
    while(std::cin>>start){
        std::array<int,13> p{},l{};p[0]=start;
        for(int i=1;i<13;++i)if(!(std::cin>>p[i]))return 3;
        for(int& v:l)if(!(std::cin>>v))return 3;
        Mask seen=0;
        for(int i=0;i<13;++i){
            if(p[i]<0||p[i]>12||l[i]<0||l[i]>12)return 3;
            seen|=1u<<p[i];
            for(int j=0;j<13;++j)if(((rows[i]>>j)&1)!=((rows[p[i]]>>l[j])&1))return 4;
        }
        if(seen!=full)return 3;
        Action a;
        for(Mask s=1;s<128;++s)a.lo[s]=a.lo[s&(s-1)]|(1u<<p[std::countr_zero(s)]);
        for(Mask s=1;s<64;++s)a.hi[s]=a.hi[s&(s-1)]|(1u<<p[7+std::countr_zero(s)]);
        group.push_back(a);
    }
    return group.size()==5616 ? 0 : 5;
}

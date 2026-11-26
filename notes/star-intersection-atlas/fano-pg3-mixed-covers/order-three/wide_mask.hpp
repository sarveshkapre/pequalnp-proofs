// Fixed-size storage for larger host graphs. Inputs are parsed as hexadecimal rows.
#include <array>
#include <bit>
#include <cstdint>
#include <string>

struct Wide {
#ifdef WIDE_MASK_BLOCKS
    static constexpr int blocks=WIDE_MASK_BLOCKS;
#else
    static constexpr int blocks=8;
#endif
    std::array<uint64_t,blocks> w{};
    Wide(uint64_t a=0){w[0]=a;}
    explicit operator bool() const {
        uint64_t u=0;for(auto x:w)u|=x;return u!=0;
    }
    bool operator==(Wide const&) const=default;
    Wide &operator|=(const Wide &s){for(int i=0;i<blocks;i++)w[i]|=s.w[i];return *this;}
    Wide &operator&=(const Wide &s){for(int i=0;i<blocks;i++)w[i]&=s.w[i];return *this;}
    friend Wide operator&(Wide a,const Wide &b){return a&=b;}
    friend Wide operator|(Wide a,const Wide &b){return a|=b;}
    friend Wide operator^(Wide a,const Wide &b){for(int i=0;i<blocks;i++)a.w[i]^=b.w[i];return a;}
    friend Wide operator~(Wide a){for(auto &v:a.w)v=~v;return a;}
    friend Wide operator-(Wide a,int n){
        uint64_t borrow=n;
        for(int i=0;i<blocks&&borrow;i++){auto old=a.w[i];a.w[i]-=borrow;borrow=(old<borrow);}
        return a;
    }
};
using Mask=Wide;
static int weight(const Wide &x){int n=0;for(auto v:x.w)n+=std::popcount(v);return n;}
static Mask bit(int i){Wide s;if(i<64*Wide::blocks)s.w[i/64]=uint64_t(1)<<(i%64);return s;}
static int take(Wide &x){
    for(int i=0;i<Wide::blocks;i++){
        auto &v=x.w[i];if(v){int j=std::countr_zero(v);v&=v-1;return 64*i+j;}
    }
    return -1;
}
static Mask fromHex(const std::string &s){
    Wide a;
    for(size_t j=0;j<s.size();j++){
        char c=s[s.size()-1-j];int v=c>='a'?c-'a'+10:c-'0';
        if(v<0||v>15||j>=16*Wide::blocks)throw std::invalid_argument("invalid hex mask");
        a.w[j/16]|=uint64_t(v)<<(4*(j%16));
    }
    return a;
}

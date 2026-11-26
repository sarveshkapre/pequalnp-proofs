// Independent four-bit mixed check. Around one point the four lines partition
// the other twelve into four triples. The nine remaining lines form a pair of
// orthogonal Latin squares on those triples, giving 72 labeled completions.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
using U=unsigned;
using Triple=std::array<int,3>;
using Latin=std::array<int,9>;
static int take(U& x){int i=std::countr_zero(x);x&=x-1;return i;}
struct Geometry {
    std::array<std::vector<uint16_t>,65536> stars;
    std::vector<std::pair<Latin,Latin>> systems;
    Geometry(){
        U box[16][16]{};
        std::vector<U> faces;
        for(int r=0;r<16;r++)for(int c=0;c<16;c++){
            for(int x=0;x<16;x++)if(!((x^r)&(x^c)))box[r][c]|=1u<<x;
            faces.push_back(box[r][c]);
        }
        std::sort(faces.begin(),faces.end());faces.erase(std::unique(faces.begin(),faces.end()),faces.end());
        if(faces.size()!=81)throw std::logic_error("bad face list");
        for(U forbid=0;forbid<65536;forbid++){
            U accessible[16]{};
            for(int c=0;c<16;c++)for(int p=0;p<16;p++)if(!(box[p][c]&forbid))accessible[c]|=1u<<p;
            for(U c:faces)if(!(c&forbid)){
                bool maximal=true;
                for(int axis=0;axis<4;axis++){
                    U step=0;for(U rest=c;rest;)step|=1u<<(take(rest)^(1<<axis));
                    if(step!=c&&!(step&forbid)){maximal=false;break;}
                }
                if(!maximal)continue;
                U star=0;for(U x=c;x;)star|=accessible[take(x)];
                stars[forbid].push_back(star);
            }
        }
        // Enumerate every order-three Latin square directly by row permutations.
        std::vector<Triple> perms;Triple p={0,1,2};
        do{perms.push_back(p);}while(std::next_permutation(p.begin(),p.end()));
        std::vector<Latin> squares;
        for(auto a:perms)for(auto b:perms)for(auto c:perms){
            Latin x{};bool valid=true;
            for(int i=0;i<3;i++){valid&=a[i]!=b[i]&&b[i]!=c[i]&&a[i]!=c[i];x[i]=a[i];x[i+3]=b[i];x[i+6]=c[i];}
            if(valid)squares.push_back(x);
        }
        for(auto& a:squares)for(auto& b:squares){
            U labels=0;for(int i=0;i<9;i++)labels|=1u<<(3*a[i]+b[i]);
            if(labels==511)systems.emplace_back(a,b);
        }
        if(squares.size()!=12||systems.size()!=72)throw std::logic_error("bad small Latin squares");
    }
};
struct Plane {
    const Geometry& geometry;
    std::array<U,13> rows;
    std::array<signed char,8192> cache{};
    std::array<Triple,4> groups{};
    std::array<U,256> lower{},upper{};
    explicit Plane(const Geometry& g,const std::array<U,13>& r):geometry(g),rows(r){
        U hits[16]{};
        for(int a=0;a<13;a++)for(U rest=rows[a];rest;)hits[take(rest)]|=1u<<a;
        for(U i=1;i<256;i++){
            lower[i]=lower[i&(i-1)]|hits[std::countr_zero(i)];
            upper[i]=upper[i&(i-1)]|hits[8+std::countr_zero(i)];
        }
    }
    bool eligible(int a,int b,int c,int d){
        U idx=(1u<<a)|(1u<<b)|(1u<<c)|(1u<<d);
        if(cache[idx])return cache[idx]>0;
        U forbid=rows[a]|rows[b]|rows[c]|rows[d];
        for(U star:geometry.stars[forbid])if((lower[star&255]|upper[star>>8]|idx)==8191){
            cache[idx]=1;return true;
        }
        cache[idx]=-1;return false;
    }
    bool complete(){
        // Only a transversal of the pencil groups can be one of the nine lines.
        U possibilities[9]{};
        for(int x=0;x<9;x++){
            for(int a=0;a<3;a++)for(int b=0;b<3;b++)
                if(eligible(groups[0][x/3],groups[1][x%3],groups[2][a],groups[3][b]))
                    possibilities[x]|=1u<<(3*a+b);
            if(!possibilities[x])return false;
        }
        for(auto& [a,b]:geometry.systems){
            bool ok=true;for(int i=0;i<9&&ok;i++)ok=possibilities[i]&(1u<<(3*a[i]+b[i]));
            if(ok)return true;
        }
        return false;
    }
    bool pencil(int k,U rest){
        if(!rest)return complete();
        int a=take(rest);U rr=rest;
        while(rr){
            int b=take(rr);U cc=rr;
            while(cc){int c=take(cc);
                if(!eligible(12,a,b,c))continue;
                groups[k]={a,b,c};
                if(pencil(k+1,rest^(1u<<b)^(1u<<c)))return true;
            }
        }
        return false;
    }
};
int main(int argc,char**argv){
    if(argc!=2)return 2;
    Geometry g;int id;uint64_t total=0,good=0;
    std::ofstream out(argv[1]);if(!out)return 2;
    while(std::cin>>id){
        std::array<U,13> f;for(auto& a:f)if(!(std::cin>>a)||!a||a>65535)return 2;
        if(Plane(g,f).pencil(0,4095)){
            ++good;out<<id;for(auto a:f)out<<' '<<a;out<<'\n';out.flush();
        }
        if(++total%100000==0)std::cout<<"tested="<<total<<" possible="<<good<<std::endl;
    }
    std::cout<<"complete="<<total<<" possible="<<good<<std::endl;
}

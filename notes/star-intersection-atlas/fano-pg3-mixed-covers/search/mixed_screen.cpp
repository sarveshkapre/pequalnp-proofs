// Necessary one-sided four-cube condition. Only families admitting a full
// 2-(13,4,1) design are passed to the independent simultaneous search.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
using U=unsigned;
using Pairs=unsigned __int128;
struct RegionTable {
    std::array<std::vector<uint16_t>,65536> maximal;
    RegionTable(){
        std::vector<U> faces;
        for(U mask=0;mask<16;mask++)for(U v=0;v<16;v++)if(!(v&~mask)){
            U f=0;for(U x=0;x<16;x++)if((x&mask)==v)f|=1u<<x;faces.push_back(f);
        }
        for(U forbidden=0;forbidden<65536;forbidden++){
            std::vector<U> safe;for(U f:faces)if(!(f&forbidden))safe.push_back(f);
            auto& best=maximal[forbidden];
            for(U c:safe){
                U star=0;for(U f:safe)if(f&c)star|=f;
                if(std::any_of(best.begin(),best.end(),[&](U s){return !(star&~s);}))continue;
                best.erase(std::remove_if(best.begin(),best.end(),[&](U s){return !(s&~star);}),best.end());
                best.push_back(star);
            }
        }
    }
};
struct Block {
    std::array<int,4> points;
    Pairs pairs;
};
struct Catalog {
    std::vector<Block> blocks;
    std::array<std::vector<int>,78> byPair;
    std::array<std::array<int,2>,78> endpoints{};
    Catalog(){
        int pairs[13][13]{};int n=0;
        for(int i=0;i<13;i++)for(int j=i+1;j<13;j++){
            pairs[i][j]=n;endpoints[n++]={i,j};
        }
        for(int i=0;i<13;i++)for(int j=i+1;j<13;j++)for(int k=j+1;k<13;k++)for(int l=k+1;l<13;l++){
            Block b{{i,j,k,l},0};
            for(int a:b.points)for(int z:b.points)if(a<z){
                b.pairs|=Pairs(1)<<pairs[a][z];byPair[pairs[a][z]].push_back(blocks.size());
            }
            blocks.push_back(b);
        }
    }
};
struct Check {
    const RegionTable& rt;const Catalog& cat;
    std::array<U,13> faces;
    std::array<std::array<U,256>,2> hits{};
    std::array<int8_t,715> possible{};
    std::array<std::vector<int>,78> choices;
    Check(const RegionTable& r,const Catalog& c,const std::array<U,13>& f):rt(r),cat(c),faces(f){
        possible.fill(-1);
        for(int j=0;j<2;j++){
            std::array<U,8> v{};
            for(int k=0;k<8;k++)for(int p=0;p<13;p++)if(faces[p]&(1u<<(8*j+k)))v[k]|=1u<<p;
            for(U mask=1;mask<256;mask++)hits[j][mask]=hits[j][mask&(mask-1)]|v[std::countr_zero(mask)];
        }
    }
    bool eligible(int i){
        if(possible[i]>=0)return possible[i];
        U forbid=0;for(int p:cat.blocks[i].points)forbid|=faces[p];
        for(U s:rt.maximal[forbid]){
            U touched=hits[0][s&255]|hits[1][s>>8];
            if(std::popcount(touched)==9){possible[i]=1;return true;}
        }
        possible[i]=0;return false;
    }
    bool design(Pairs covered) const {
        int shortest=716,best=-1;
        for(int p=0;p<78;p++)if(!(covered&(Pairs(1)<<p))){
            int count=0;
            for(int i:choices[p])if(!(cat.blocks[i].pairs&covered)&&++count>=shortest)break;
            if(!count)return false;
            if(count<shortest){best=p;shortest=count;}
        }
        if(best<0)return true;
        for(int i:choices[best])if(!(cat.blocks[i].pairs&covered)&&design(covered|cat.blocks[i].pairs))return true;
        return false;
    }
    int run(){
        // Large row faces often yield the first pair with no admissible line.
        for(int p=77;p>=0;p--){
            bool found=false;
            for(int i:cat.byPair[p])if(eligible(i)){found=true;break;}
            if(!found)return 0;
        }
        for(int p=0;p<78;p++)for(int i:cat.byPair[p])if(eligible(i))choices[p].push_back(i);
        return design(0)?2:1;
    }
};
int main(int argc,char**argv){
    if(argc!=2)return 2;
    RegionTable regions;Catalog cat;std::ofstream kept(argv[1]);
    if(!kept)return 2;
    uint64_t n=0,pair=0,design=0;int id;
    while(std::cin>>id){
        std::array<U,13> f;for(auto& x:f)if(!(std::cin>>x)||!x||x>65535)return 2;
        Check c(regions,cat,f);int s=c.run();++n;pair+=s>=1;design+=s==2;
        if(s==2){kept<<id;for(auto x:f)kept<<' '<<x;kept<<'\n';kept.flush();}
        if(n%100000==0)std::cout<<"processed="<<n<<" pair_survivors="<<pair<<" design_survivors="<<design<<std::endl;
    }
    std::cout<<"complete="<<n<<" pair_survivors="<<pair<<" design_survivors="<<design<<std::endl;
}

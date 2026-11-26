// Isomorphism representatives for antichains in the four-dimensional cube.
// A nonsingleton in an antichain can use only vertices omitted as singletons.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <set>
#include <vector>
using Set=unsigned __int128;
using Action=std::array<int,16>;
static Set b(int i){return Set(1)<<i;}
static bool leftEarlier(Set left,Set right){
    Set diff=left^right;
    return bool(left&diff&(-diff));
}
static int cardinality(Set x){return std::popcount(uint64_t(x))+std::popcount(uint64_t(x>>64));}
static int takeSet(Set &s){auto low=uint64_t(s);int i=low?std::countr_zero(low):64+std::countr_zero(uint64_t(s>>64));s&=s-1;return i;}
static unsigned moveVertices(unsigned mask,const Action& a){
    unsigned out=0;while(mask){int p=std::countr_zero(mask);out|=1u<<a[p];mask&=mask-1;}return out;
}
struct Generator {
    int count;
    unsigned holes;
    uint64_t families=0,labeled=0;
    bool countOnly=false;
    std::vector<unsigned> faces;
    std::vector<Set> incomparable;
    std::vector<std::vector<int>> maps;
    std::vector<std::vector<Set>> images;
    std::vector<int> picked;
    void visit(int depth,Set available,Set chosen){
        if(depth==count){
            ++families;
            int stab=std::count(images[depth].begin(),images[depth].end(),chosen);
            if(!stab||384%stab)throw std::logic_error("bad cube stabilizer");
            labeled+=384/stab;
            if(!countOnly){
                std::cout<<(families-1);
                for(int i=0;i<16;i++)if(!(holes&(1u<<i)))std::cout<<' '<<(1u<<i);
                for(int i:picked)std::cout<<' '<<faces[i];
                std::cout<<'\n';
            }
            return;
        }
        if(cardinality(available)<count-depth)return;
        while(available){
            int x=takeSet(available);Set next=chosen|b(x);
            Set future=available&incomparable[x];
            if(cardinality(future)<count-depth-1)continue;
            bool canonical=true;
            for(int g=0;g<int(maps.size());g++){
                Set z=images[depth][g]|b(maps[g][x]);
                if(leftEarlier(z,next)){canonical=false;break;}
                images[depth+1][g]=z;
            }
            if(!canonical)continue;
            picked.push_back(x);visit(depth+1,future,next);picked.pop_back();
        }
    }
    void run(unsigned omitted,const std::vector<Action>& stabilizer){
        holes=omitted;faces.clear();maps.clear();std::set<unsigned> subsets;
        for(int mask=0;mask<16;mask++)for(int v=0;v<16;v++)if(!(v&~mask)){
            unsigned f=0;for(int x=0;x<16;x++)if((x&mask)==v)f|=1u<<x;
            if(!(f&~holes)&&std::popcount(f)>1)subsets.insert(f);
        }
        faces.assign(subsets.begin(),subsets.end());int size=faces.size();incomparable.assign(size,0);
        for(int i=0;i<size;i++)for(int j=i+1;j<size;j++)
            if((faces[i]&~faces[j])&&(faces[j]&~faces[i]))incomparable[i]|=b(j);
        for(auto& a:stabilizer){
            std::vector<int> m;for(unsigned f:faces){
                unsigned t=moveVertices(f,a);auto it=std::lower_bound(faces.begin(),faces.end(),t);
                if(it==faces.end()||*it!=t)throw std::logic_error("invalid induced action");
                m.push_back(it-faces.begin());
            }maps.push_back(m);
        }
        images.assign(count+1,std::vector<Set>(maps.size()));
        visit(0,b(size)-1,0);
    }
};
int main(int argc,char** argv){
    if(argc<2||argc>3)return 2;
    Generator g;g.count=std::stoi(argv[1]);if(g.count<0||g.count>13)return 2;
    g.countOnly=argc==3 && std::string(argv[2])=="count";if(argc==3&&!g.countOnly)return 2;
    std::array<int,4> p={0,1,2,3};std::vector<Action> actions;
    do{for(int t=0;t<16;t++){Action a;
        for(int i=0;i<16;i++){int x=t;for(int j=0;j<4;j++)if((i>>j)&1)x^=1<<p[j];a[i]=x;}
        actions.push_back(a);
    }}while(std::next_permutation(p.begin(),p.end()));
    std::vector<bool> seen(65536);int holeShapes=0;
    for(unsigned h=0;h<65536;h++)if(!seen[h]&&std::popcount(h)==g.count+3){
        std::vector<Action> stab;
        for(auto& a:actions){auto d=moveVertices(h,a);seen[d]=true;if(d==h)stab.push_back(a);}
        ++holeShapes;g.run(h,stab);
    }
    std::cerr<<"nonvertices="<<g.count<<" hole_shapes="<<holeShapes<<" orbit_count="<<g.families
             <<" labeled_antichains="<<g.labeled<<'\n';
}

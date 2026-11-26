// Test two-sided row/singleton and column/singleton witnesses on PG(2,3).
// Input: thirteen four-cube faces (16-bit vertex sets) for the point labels.
// Column labels and the projective labeling of the points are unrestricted.
#define main original_embedding_main
#include "../order-three/orbit_embedding.cpp"
#undef main
#include <map>
#include <set>

using FaceSet=unsigned __int128;
constexpr FaceSet faceBit(int n){return FaceSet(1)<<n;}
static int takeFace(FaceSet& s){
    auto low=uint64_t(s);
    int i=low?std::countr_zero(low):64+std::countr_zero(uint64_t(s>>64));
    s&=s-1;
    return i;
}
struct Cube {
    std::vector<unsigned> vertices;
    std::array<FaceSet,81> disjoint{},incomparable{};
    Cube(){
        for(unsigned mask=0;mask<16;mask++)for(unsigned val=0;val<16;val++)if(!(val&~mask)){
            unsigned set=0;
            for(unsigned u=0;u<16;u++)if((mask&u)==val)set|=1u<<u;
            vertices.push_back(set);
        }
        if(vertices.size()!=81)throw std::logic_error("cube size");
        for(int f=0;f<81;f++)for(int g=0;g<81;g++){
            unsigned a=vertices[f],b=vertices[g];if(!(a&b))disjoint[f]|=faceBit(g);
            if((a&~b)&&(b&~a))incomparable[f]|=faceBit(g);
        }
    }
};
struct Block {
    FaceSet choices{};
    std::vector<std::array<FaceSet,13>> connectors;
};
struct Model {
    const Geometry& pg;
    const Cube& cube;
    std::array<unsigned,13> rowFaces{},blocks{};
    std::array<FaceSet,13> meetRow{};
    std::array<int,13> points{},columns{};
    std::vector<Block> cand=std::vector<Block>(8192);
    uint64_t labeled=0,oneSided=0,fits=0,searchNodes=0;
    bool found=false;
    Model(const Geometry& geometry,const Cube& cube_):pg(geometry),cube(cube_){}
    void prepare(bool verticesOnly){
        for(int p=0;p<13;p++){
            if(std::find(cube.vertices.begin(),cube.vertices.end(),rowFaces[p])==cube.vertices.end())
                throw std::invalid_argument("row label is not a cube face");
            for(int q=0;q<p;q++)if(!(rowFaces[p]&~rowFaces[q])||!(rowFaces[q]&~rowFaces[p]))
                throw std::invalid_argument("row profiles must form an antichain");
            for(int f=0;f<81;f++)if(rowFaces[p]&cube.vertices[f])meetRow[p]|=faceBit(f);
        }
        for(unsigned b=0;b<=all13;b++)if(std::popcount(b)==4){
            auto& block=cand[b];block.connectors.resize(81);
            FaceSet safe=~FaceSet(0);unsigned pp=b;
            while(pp)safe&=~meetRow[first(pp)];
            safe&=faceBit(81)-1;
            FaceSet options=safe;
            while(options){
                int c=takeFace(options);
                if(verticesOnly && !std::has_single_bit(cube.vertices[c]))continue;
                bool works=true;
                for(int p=0;p<13;p++)if(!(b&(1u<<p))){
                    FaceSet routes=meetRow[p]&~cube.disjoint[c]&safe;
                    if(!routes){works=false;break;}
                    block.connectors[c][p]=routes;
                }
                if(works)block.choices|=faceBit(c);
            }
        }
    }
    bool permitted(int line,int c,unsigned chosen) const {
        unsigned earlier=chosen;
        while(earlier)if(!(cube.incomparable[c]&faceBit(columns[first(earlier)])))return false;
        unsigned active=chosen|(1u<<line);
        for(int p=0;p<13;p++){
            FaceSet safe=faceBit(81)-1;
            unsigned incident=active&pg.row[points[p]];
            while(incident){
                int l=first(incident);
                safe&=cube.disjoint[l==line?c:columns[l]];
            }
            unsigned outside=active&~pg.row[points[p]];
            while(outside){
                int l=first(outside),v=l==line?c:columns[l];
                if(!(safe&cand[blocks[l]].connectors[v][p]))return false;
            }
        }
        return true;
    }
    bool chooseColumns(unsigned chosen){
        ++searchNodes;
        if(chosen==all13)return true;
        int best=-1,shortest=82;
        FaceSet options=0;
        unsigned todo=all13^chosen;
        while(todo){
            int l=first(todo),count=0;
            FaceSet inst=cand[blocks[l]].choices,good=0;
            while(inst){int c=takeFace(inst);if(permitted(l,c,chosen)){good|=faceBit(c);if(++count>=shortest)break;}}
            if(!count)return false;
            if(count<shortest){best=l;shortest=count;options=good;}
        }
        while(options){
            int c=takeFace(options);
            columns[best]=c;
            if(chooseColumns(chosen|(1u<<best)))return true;
        }
        return false;
    }
    void visit(int depth,unsigned used){
        if(found)return;
        if(depth==13){
            ++oneSided;
            if(!chooseColumns(0))return;
            ++fits;found=true;
            std::cout<<"CANDIDATE points=";for(int x:points)std::cout<<x<<',';
            std::cout<<" columns=";for(int x:columns)std::cout<<cube.vertices[x]<<',';
            std::cout<<std::endl;return;
        }
        unsigned labels=pg.orbits[used];
        while(labels && !found){
            int p=first(labels);points[depth]=p;unsigned ls=pg.row[p];bool ok=true;
            while(ls){auto& b=blocks[first(ls)];b|=1u<<depth;if(std::popcount(b)==4 && !cand[b].choices)ok=false;}
            if(depth==12)++labeled;
            if(ok)visit(depth+1,used|(1u<<p));
            ls=pg.row[p];while(ls)blocks[first(ls)]^=1u<<depth;
        }
    }
};
int main(int argc,char** argv){
    bool verticesOnly=argc==2 && std::string(argv[1])=="vertex-columns";
    if(argc>1&&!verticesOnly)return 2;
    Geometry pg;Cube cube;int id;
    while(std::cin>>id){
        Model m(pg,cube);for(auto& x:m.rowFaces)if(!(std::cin>>x))return 2;
        m.prepare(verticesOnly);m.visit(0,0);
        std::cout<<id<<' '<<(m.found?"LOCAL_MODEL":"EXCLUDED")<<" completed_labels="<<m.labeled
                 <<" one_sided="<<m.oneSided<<" column_nodes="<<m.searchNodes<<std::endl;
    }
}

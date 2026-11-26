// Exact Hamming distance for the other two-gate form (two parallel meets).
// First choose all intrinsically positive rows. Each meet then has two
// disjoint point sets. The best classification of each column is independent.
#include "plane_distance_symmetry.hpp"

struct Pair { Mask a,b; int code; };
using Group = std::vector<const Action*>;
std::array<Score,8192> dist{};
struct Census {
    const std::array<Mask,13>& col;
    Mask fullRows;
    Group sym;
    int best;
    std::array<int,8192> digit{};
    std::vector<int> orbit, stamp;
    std::vector<Pair> banks, first;
    long long visits=0;
    Pair encode(Mask a,Mask b)const{
        if(a>b)std::swap(a,b);
        return {a,b,digit[a]+2*digit[b]};
    }
    void build(){
        Mask active=full^fullRows;
        std::array<int,13> trit{};
        int width=1;
        for(int i=0;i<13;++i)if(active>>i&1){trit[i]=width;width*=3;}
        for(Mask a=1;a<=full;++a)digit[a]=digit[a&(a-1)]+trit[std::countr_zero(a)];
        orbit.assign(width,-1);stamp.assign(width,-1);
        for(Mask a=active;;a=(a-1)&active){
            Mask rest=active^a;
            for(Mask b=rest;;b=(b-1)&rest){
                if(a<=b)banks.push_back(encode(a,b));
                if(!b)break;
            }
            if(!a)break;
        }
        for(auto q:banks)if(orbit[q.code]<0){
            int id=first.size();first.push_back(q);
            for(auto g:sym)orbit[encode(g->move(q.a),g->move(q.b)).code]=id;
        }
        for(Mask u=0;u<=full;++u)for(int j=0;j<13;++j)dist[u][j]=std::popcount((u|fullRows)^col[j]);
    }
    void run(){
        for(int id=0;id<int(first.size());++id){
            Pair q=first[id];Group stabilizer;
            for(auto g:sym)if(encode(g->move(q.a),g->move(q.b)).code==q.code)stabilizer.push_back(g);
            const Score base=combine(combine(dist[full],dist[0]),combine(dist[q.a],dist[q.b]));
            for(auto v:banks){
                if(orbit[v.code]<id||stamp[v.code]==id)continue;
                if(stabilizer.size()>1)for(auto g:stabilizer)stamp[encode(g->move(v.a),g->move(v.b)).code]=id;
                ++visits;
                const Score singles=combine(dist[v.a],dist[v.b]);
                const Score cross=combine(combine(dist[v.a|q.a],dist[v.a|q.b]),
                                          combine(dist[v.b|q.a],dist[v.b|q.b]));
                int cost=sum(combine(base,combine(singles,cross)));
                if(cost<best){
                    best=cost;
                    std::cout<<"best "<<cost<<" full rows "<<fullRows<<" pairs "<<q.a<<' '<<q.b
                             <<' '<<v.a<<' '<<v.b<<std::endl;
                }
            }
        }
    }
};
int main(){
    std::array<Mask,13> rows{},col{};std::vector<Action> group;
    if(int err=read_geometry(rows,col,group))return err;
    std::array<bool,8192> seen{};
    int best=170;long long total=0;
    for(Mask f=0;f<=full;++f){
        if(seen[f] || 9*std::popcount(f)>=best)continue;
        Group sym;
        for(const auto& g:group){Mask v=g.move(f);seen[v]=true;if(v==f)sym.push_back(&g);}
        Census c{col,f,sym,best};c.build();c.run();best=c.best;total+=c.visits;
        std::cout<<"full row case "<<f<<" banks "<<c.banks.size()<<" first orbits "<<c.first.size()
                 <<" pairs "<<c.visits<<" running best "<<best<<std::endl;
    }
    std::cout<<"complete "<<best<<" pairs "<<total<<std::endl;
}

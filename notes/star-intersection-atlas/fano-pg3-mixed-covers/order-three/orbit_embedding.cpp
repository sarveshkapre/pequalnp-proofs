// Exact search for a 13-point projective plane as an induced bipartite submatrix.
// Choose host rows in clique-search order. Keep all compatible target labellings,
// up to projectivities fixing earlier target labels, and all eligible host columns.
#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>
#include "wide_mask.hpp"

using U = unsigned;
static constexpr U all13 = (1u<<13)-1;
static int first(U &x){int a=std::countr_zero(x);x &= x-1;return a;}
using V = std::array<int,3>;
struct Geometry {
    std::vector<V> points;
    std::array<U,13> row{};
    std::array<U,8192> orbits{};
    Geometry() {
        for(int i=1;i<27;i++){
            V v={i/9,(i/3)%3,i%3};
            if(*std::find_if(v.begin(),v.end(),[](int x){return x!=0;})==1)points.push_back(v);
        }
        if(points.size()!=13)throw std::logic_error("points");
        for(int p=0;p<13;p++)for(int l=0;l<13;l++)
            if(std::inner_product(points[p].begin(),points[p].end(),points[l].begin(),0)%3==0)row[p]|=1u<<l;
        std::vector<std::array<int,13>> pgl;
        std::vector<U> fixed;
        for(int m=1;m<19683;m++){
            std::array<int,9> a{};int v=m;
            for(int &x:a){x=v%3;v/=3;}
            if(*std::find_if(a.begin(),a.end(),[](int x){return x!=0;})!=1)continue;
            int det=a[0]*(a[4]*a[8]-a[5]*a[7])-a[1]*(a[3]*a[8]-a[5]*a[6])+a[2]*(a[3]*a[7]-a[4]*a[6]);
            if(det%3==0)continue;
            std::array<int,13> perm{};U fix=0;
            for(int i=0;i<13;i++){
                V w{};for(int r=0;r<3;r++)
                    w[r]=std::inner_product(a.begin()+3*r,a.begin()+3*r+3,points[i].begin(),0)%3;
                if(*std::find_if(w.begin(),w.end(),[](int x){return x!=0;})==2)
                    for(int &j:w)j=2*j%3;
                perm[i]=std::find(points.begin(),points.end(),w)-points.begin();
                if(perm[i]==i)fix|=1u<<i;
            }
            pgl.push_back(perm);fixed.push_back(fix);
        }
        if(pgl.size()!=5616)throw std::logic_error("projectivity count");
        // For each fixed subset, suppress points having a smaller image under
        // any element of its pointwise stabilizer. Identity needs no processing.
        for(U s=0;s<=all13;s++)orbits[s]=all13^s;
        for(size_t i=0;i<pgl.size();i++){
            U movedDown=0;
            for(int p=0;p<13;p++)if(pgl[i][p]<p)movedDown|=1u<<p;
            for(U s=fixed[i];;s=(s-1)&fixed[i]){
                orbits[s]&=~movedDown;
                if(!s)break;
            }
        }
    }
};
struct Bucket { Mask host; U target=0; };
struct State {
    std::array<Bucket,13> bins;
    std::array<signed char,13> labels;
    U used=0;
    int num=0;
};
struct Search {
    Geometry const &g;
    std::vector<Mask> rows,pairAdj;
    std::vector<U> pairCount,deg;
    std::vector<unsigned char> triples;
    int n,m;
    std::array<int,13> chosen{},resultRows{},resultCols{};
    std::array<uint64_t,14> nodes{},numberStates{};
    std::chrono::steady_clock::time_point deadline;
    uint64_t maxNodes,visits=0;
    bool timeout=false;
    bool expired(){
        if(visits>=maxNodes||std::chrono::steady_clock::now()>=deadline)timeout=true;
        return timeout;
    }
    Search(Geometry const &gg,std::vector<Mask> h,int nc,int seconds,uint64_t cap):
        g(gg),rows(std::move(h)),pairAdj(rows.size()),
        pairCount(rows.size()*rows.size()),deg(rows.size()),triples(rows.size()*rows.size()*rows.size()),
        n(rows.size()),m(nc),deadline(std::chrono::steady_clock::now()+std::chrono::seconds(seconds)),maxNodes(cap){
        for(int i=0;i<n;i++)deg[i]=weight(rows[i]);
        for(int a=0;a<n;a++)for(int b=0;b<a;b++){
            int ab=weight(rows[a]&rows[b]);
            pairCount[a*n+b]=pairCount[b*n+a]=ab;
            if(ab>=1 && int(deg[a])-ab>=3 && int(deg[b])-ab>=3 && m-int(deg[a]+deg[b])+ab>=6){
                pairAdj[a]|=bit(b);pairAdj[b]|=bit(a);
            }
        }
        for(int a=0;a<n;a++)for(int b=0;b<a;b++){
            Mask ab=rows[a]&rows[b];
            for(int c=0;c<b;c++){
                int abc=weight(ab&rows[c]);
                int x=int(pairCount[a*n+b])-abc,y=int(pairCount[a*n+c])-abc,z=int(pairCount[b*n+c])-abc;
                int p=int(deg[a])-abc-x-y,q=int(deg[b])-abc-x-z,r=int(deg[c])-abc-y-z;
                int zero=m-abc-x-y-z-p-q-r;
                unsigned char flags=(abc>=1 && std::min({p,q,r})>=3 && zero>=3 ? 1 : 0)
                    | (std::min({x,y,z})>=1 && std::min({p,q,r})>=2 && zero>=4 ? 2 : 0);
                triples[(a*n+b)*n+c]=flags;triples[(a*n+c)*n+b]=flags;
                triples[(b*n+a)*n+c]=flags;triples[(b*n+c)*n+a]=flags;
                triples[(c*n+a)*n+b]=flags;triples[(c*n+b)*n+a]=flags;
            }
        }
    }
    bool fit(State const&s,int a,int p,State *next=nullptr){
        int count=0;
        for(int j=0;j<s.num;j++){
            const auto &bin=s.bins[j];
            U yes=bin.target&g.row[p],no=bin.target&~g.row[p];
            if(yes){Mask pool=bin.host&rows[a];if(weight(pool)<std::popcount(yes))return false;
                if(next)next->bins[count++]={pool,yes};}
            if(no){Mask pool=bin.host&~rows[a];if(weight(pool)<std::popcount(no))return false;
                if(next)next->bins[count++]={pool,no};}
        }
        if(next){next->num=count;next->used=s.used|(1u<<p);next->labels=s.labels;
            next->labels[std::popcount(s.used)]=p;}
        return true;
    }
    bool remainingFits(State const &s,Mask options){
        // When target lines have distinct, uniquely forced columns, injectivity
        // on unassigned rows also bounds every joint pattern on those columns.
        std::array<int,13> cols{},lines{};int nc=0;
        for(int j=0;j<s.num;j++)if(std::has_single_bit(s.bins[j].target)&&weight(s.bins[j].host)==1){
            Mask col=s.bins[j].host;cols[nc]=take(col);lines[nc++]=std::countr_zero(s.bins[j].target);}
        if(nc>=2){
            std::array<U,13> want{},avail{};int nbin=0;
            U ts=all13^s.used;
            while(ts){int p=first(ts);U sig=0;
                for(int i=0;i<nc;i++)sig|=((g.row[p]>>lines[i])&1)<<i;
                int j=0;while(j<nbin&&want[j]!=sig)++j;
                if(j==nbin)want[nbin++]=sig;
                ++avail[j];}
            Mask hs=options;
            while(hs){int a=take(hs);U sig=0;
                for(int i=0;i<nc;i++)sig|=U((rows[a].w[cols[i]/64]>>(cols[i]%64))&1)<<i;
                for(int j=0;j<nbin;j++)if(want[j]==sig){if(avail[j])--avail[j];break;}}
            for(int j=0;j<nbin;j++)if(avail[j])return false;
        }
        return true;
    }
    void record(State const&s){
        for(int j=0;j<13;j++)resultRows[s.labels[j]]=chosen[j];
        for(int j=0;j<s.num;j++){
            U ts=s.bins[j].target;Mask hs=s.bins[j].host;
            while(ts){int l=first(ts);resultCols[l]=take(hs);}
        }
        for(int p=0;p<13;p++)for(int l=0;l<13;l++){
            int c=resultCols[l];if(((rows[resultRows[p]].w[c/64]>>(c%64))&1)!=((g.row[p]>>l)&1))
                throw std::logic_error("invalid extracted witness");}
    }
    bool visit(int depth,Mask cand,std::vector<Mask> const &adj,std::vector<State> const &states){
        ++nodes[depth];numberStates[depth]+=states.size();++visits;
        if((visits&127)==0&&expired())return false;
        if(depth==13){record(states.front());return true;}
        if(weight(cand)<13-depth)return false;
        std::vector<int> order,colors;
        int color=0;Mask byColor=cand;
        while(byColor){Mask eligible=byColor;color++;
            while(eligible){int a=take(eligible);byColor&=~bit(a);eligible&=~adj[a];
                order.push_back(a);colors.push_back(color);}}
        for(int i=int(order.size())-1;i>=0;--i){
            if(colors[i]+depth<13)return false;
            int x=order[i];cand&=~bit(x);
            Mask nextPool=cand&adj[x];
            if(weight(nextPool)+depth+1<13)continue;
            std::vector<State> next;
            for(auto const &s:states){
                U ps=g.orbits[s.used];
                while(ps){
                    int p=first(ps);State ns;
                    if(fit(s,x,p,&ns)&&remainingFits(ns,nextPool))next.push_back(ns);
                }
            }
            if(next.empty())continue;
            chosen[depth]=x;auto tightened=adj;
            Mask ay=nextPool;
            while(ay){int y=take(ay);Mask bz=ay&adj[y];
                while(bz){int z=take(bz);if(!triples[(x*n+y)*n+z]){
                    tightened[y]&=~bit(z);tightened[z]&=~bit(y);}}}
            if(visit(depth+1,nextPool,tightened,next))return true;
            if(timeout)return false;
        }
        return false;
    }
    bool run(){
        State root{};root.num=1;root.bins[0]={bit(m)-1,all13};for(auto &i:root.labels)i=-1;
        return visit(0,bit(n)-1,pairAdj,{root});
    }
};
int main(int argc,char**argv){
    int seconds=argc>1?std::stoi(argv[1]):10;
    uint64_t cap=argc>2?std::stoull(argv[2]):1000000000;
    Geometry g;
    int rep,n,m;
    while(std::cin>>rep>>n>>m){
        if(n<0||m<0||n>=64*Mask::blocks||m>=64*Mask::blocks)return 2;
        std::vector<Mask> h(n);for(auto &row:h){std::string hex;std::cin>>hex;row=fromHex(hex);}
        auto start=std::chrono::steady_clock::now();
        Search search(g,std::move(h),m,seconds,cap);
        bool solved=search.run();
        std::cout<<rep<<' '<<(solved?"FOUND":search.timeout?"LIMIT":"EXCLUDED")
            <<" nodes="<<search.visits<<" sec="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<" layers=";
        for(auto z:search.nodes)std::cout<<z<<',';
        std::cout<<" states=";for(auto z:search.numberStates)std::cout<<z<<',';
        if(solved){std::cout<<" rows=";for(int z:search.resultRows)std::cout<<z<<',';
            std::cout<<" columns=";for(int z:search.resultCols)std::cout<<z<<',';}
        std::cout<<std::endl;
    }
}

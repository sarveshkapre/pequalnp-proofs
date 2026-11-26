// Universal upper bound after removing every nonpositive or degree-one vertex.
// These boards are supersets of possible trimmed predictions; flags must be C4-free.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdlib>
#include <iostream>
#include <vector>
using Counts=std::array<int,8>;
struct Upper{
    int d,r;
    bool three_clauses=false;
    std::vector<int> labels;
    std::array<int,8> adj{};
    Counts rows{},cols{},colsize{},maxcol{},rowdeg{};
    int best=0;
    long long examined=0;
    int capacity(int mult,int degree)const{
        if(!mult)return 0;
        if(three_clauses && degree==1)return mult<=d?mult:-1000;
        if(mult>3)return -1000;
        if(degree<2||degree>=2*d)return -1000;
        if(mult==1)return std::min(degree,2*d-degree);
        if(degree%2==0|| (mult==3&&degree!=3))return -1000;
        return mult;
    }
    // A pair of columns contributes to at most one positive row neighborhood.
    // With only this global constraint the optimum fills the cheapest
    // available increases first: adding a flag to t flags costs t new pairs.
    int pair_bound(const Counts& mult,const Counts& degree,const Counts& other)const{
        int area=0,edges=0,remaining=0;
        std::array<int,32> possible{};
        int active=0;for(int k=0;k<r;++k)if(mult[k])active|=1<<k;
        for(int i=0;i<r;++i){
            remaining+=other[i]*(other[i]-1)/2;
            for(int j=0;j<i;++j)if(adj[i]&adj[j]&active)remaining+=other[i]*other[j];
            if(!mult[i])continue;
            int n=degree[i]/2+1;
            edges+=mult[i]*n;remaining-=mult[i]*n*(n-1)/2;
            area+=mult[i]*degree[i];
            if(mult[i]==1)for(int h=n;h<std::min(d,degree[i]);++h)++possible[h];
        }
        if(remaining<0)return -1000;
        for(int h=1;h<32;++h){
            int count=std::min(possible[h],remaining/h);
            edges+=count;remaining-=count*h;
        }
        return 2*edges-area;
    }
    void columns(int j,int upper){
        if(j==r){
            if(upper<=best)return;
            int score=0;
            for(int i=0;i<r;++i)score+=capacity(rows[i],rowdeg[i]);
            if(score<=best)return;
            // Pairwise neighborhood intersections on a single shore are at
            // most one in the true board. Jointly lower-bound the number of
            // neighbors each positive vertex needs in its predicted set.
            for(int side=0;side<2;++side){
                const auto& mult=side?cols:rows;
                const auto& other=side?rows:cols;
                const auto& degree=side?colsize:rowdeg;
                for(int a=0;a<r;++a)if(mult[a])
                    for(int b=0;b<a;++b)if(mult[b]){
                        int mask=adj[a]&adj[b],shared=0;
                        while(mask){int v=std::countr_zero(static_cast<unsigned>(mask));shared+=other[v];mask&=mask-1;}
                        if(degree[a]/2+degree[b]/2+2>degree[a]+degree[b]-shared+1)return;
                    }
            }
            ++examined;
            int u=std::min({upper,score,pair_bound(rows,rowdeg,cols),pair_bound(cols,colsize,rows)});
            best=std::max(best,u);
            return;
        }
        for(int n=0;n<=maxcol[j];++n){
            cols[j]=n;
            columns(j+1,upper+capacity(n,colsize[j]));
            if(n<maxcol[j])for(int i=0;i<r;++i)if(adj[j]>>i&1)++rowdeg[i];
        }
        for(int i=0;i<r;++i)if(adj[j]>>i&1)rowdeg[i]-=maxcol[j];
    }
    void run(){
        r=labels.size();
        for(int i=0;i<r;++i)for(int j=0;j<r;++j)
            if(three_clauses?((labels[i]|labels[j])==7):bool(labels[i]&labels[j]))adj[i]|=1<<j;
        int radix=(three_clauses?d:3)+1,count=1;
        for(int i=0;i<r;++i)count*=radix;
        for(int code=0;code<count;++code){
            int x=code;
            for(int i=0;i<r;++i){rows[i]=x%radix;x/=radix;}
            for(int j=0;j<r;++j){
                colsize[j]=0;
                for(int i=0;i<r;++i)if(adj[j]>>i&1)colsize[j]+=rows[i];
                maxcol[j]=three_clauses && colsize[j]==1 ? d : 3;
                while(maxcol[j]&&capacity(maxcol[j],colsize[j])<0)--maxcol[j];
            }
            columns(0,0);
        }
    }
};
int main(int argc,char**argv){
    if(argc!=3)return 2;
    int d=std::atoi(argv[1]),s=std::atoi(argv[2]);
    if(d<3||d>40||s<2||s>5||(s==5&&d>8))return 2;
    Upper u{d};
    if(s==5){u.three_clauses=true;u.labels={1,2,4,3,5,6};}
    else for(int a=1;a<(1<<s);++a)if(s<4||((a&3)!=3&&(a&12)!=12))u.labels.push_back(a);
    u.run();
    std::cout<<"degree "<<d<<" rectangle model "<<s
             <<(u.three_clauses?" positive trimmed bound ":" leafless bound ")<<u.best<<'\n';
}

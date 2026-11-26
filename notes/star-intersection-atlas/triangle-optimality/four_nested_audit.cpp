// Independent upper check for the order-four three-clause case.
// A gain of 25 would leave at most five units short of the six type maxima.
#include <algorithm>
#include <array>
#include <iostream>
#include <cstdlib>
#include <vector>
using V=std::array<int,6>;
constexpr int words[6]={1,2,4,6,5,3};
int choose2(int x){return x*(x-1)/2;}
struct Profile{V count{},neighbors{};int total=0;};

bool feasible(const Profile& a,const Profile& b,int target){
    int edges=0,area=0,maxScore=0;
    std::vector<int> increments;
    int pairs=0;
    for(int i=0;i<6;++i){
        int m=a.count[i],deg=b.neighbors[i];
        if(!m)continue;
        if(!deg||deg>=10)return false;
        int low=deg/2+1, high=std::min(5,deg);
        if(m>1){
            if(deg>1 && (deg%2==0||m>3||(m==3&&deg!=3)))return false;
            high=low;
        }
        maxScore+=m*(2*high-deg);
        edges+=m*low;
        area+=m*deg;
        pairs+=m*choose2(low);
        for(int h=low;h<high;++h)for(int v=0;v<m;++v)increments.push_back(h);
    }
    if(maxScore<target)return false;
    int budget=0;
    for(int j=0;j<6;++j){
        if(!b.count[j])continue;
        budget+=choose2(b.count[j]);
        for(int k=0;k<j;++k){
            bool possible=false;
            for(int i=0;i<6;++i)if(a.count[i]&&((words[i]|words[j])==7)&&((words[i]|words[k])==7))possible=true;
            if(possible)budget+=b.count[j]*b.count[k];
        }
    }
    int needed=std::max(0,(area+target+1)/2-edges);
    if(needed>int(increments.size()))return false;
    std::sort(increments.begin(),increments.end());
    for(int i=0;i<needed;++i)pairs+=increments[i];
    return pairs<=budget;
}
int main(int argc,char**argv){
    int target=argc==2?std::atoi(argv[1]):25;
    if(target!=24&&target!=25)return 2;
    std::vector<Profile> options;
    for(int code=0;code<46656;++code){
        Profile a;int x=code,zero=0;
        for(auto& m:a.count){m=x%6;x/=6;a.total+=m;zero+=m==0;}
        if(zero>1||a.total>21)continue;
        // Each pair type sees at least two active types if at most one is missing.
        if(*std::max_element(a.count.begin()+3,a.count.end())>3)continue;
        for(int i=0;i<6;++i)for(int j=0;j<6;++j)
            if((words[i]|words[j])==7)a.neighbors[i]+=a.count[j];
        options.push_back(a);
    }
    unsigned long long boards=0,possible=0;
    for(int i=0;i<int(options.size());++i)for(int j=0;j<=i;++j){
        ++boards;
        if(feasible(options[i],options[j],target)&&feasible(options[j],options[i],target))++possible;
    }
    std::cout<<"order four profiles "<<options.size()<<" shore-unordered boards "<<boards
             <<" passing both independent "<<target<<"-gain pair budgets "<<possible<<'\n';
    return (possible==0)!=(target==25);
}

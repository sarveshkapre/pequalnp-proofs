// Direct labelled Fano-plane Hamming optimization for both ordinary two-gate forms.
#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
using U=unsigned;
constexpr U all=127;
using Cost=std::array<unsigned char,7>;
std::array<Cost,128> costs;
int score(const U* patterns,int n){
    Cost best;best.fill(7);
    for(int i=0;i<n;++i)for(int c=0;c<7;++c)best[c]=std::min(best[c],costs[patterns[i]][c]);
    int result=0;for(auto b:best)result+=b;return result;
}
int main(){
    for(U m=0;m<128;++m)for(int j=1;j<=7;++j){
        U col=0;for(int p=1;p<=7;++p)if(std::popcount(U(j&p))%2==0)col|=1u<<(p-1);
        costs[m][j-1]=std::popcount(col^m);
    }
    int nbest=50,pbest=50;
    for(U a=0;a<=all;++a)for(U b=a;b<=all;++b)for(U c=b;c<=all;++c){
        U patterns[]={all,all^a,all^b,all^c,all^(a|b),all^(a|c),all^(b|c),all^(a|b|c)};
        nbest=std::min(nbest,score(patterns,8));
    }
    long long count=0;
    for(U f=0;f<=all;++f){
        U active=all^f;
        for(U a=active;;a=(a-1)&active){
            U x=active^a;
            for(U b=x;;b=(b-1)&x){
                if(a<=b)for(U c=active;;c=(c-1)&active){
                    U y=active^c;
                    for(U d=y;;d=(d-1)&y){
                        if(c<=d){
                            U pat[]={all,f,f|a,f|b,f|c,f|d,f|a|c,f|a|d,f|b|c,f|b|d};
                            pbest=std::min(pbest,score(pat,10));++count;
                        }
                        if(!d)break;
                    }
                    if(!c)break;
                }
                if(!b)break;
            }
            if(!a)break;
        }
    }
    std::cout<<"Fano all 49 cells, three raw clauses "<<nbest<<" errors, two parallel meets "
             <<pbest<<" errors, parallel representative assignments "<<count<<'\n';
}

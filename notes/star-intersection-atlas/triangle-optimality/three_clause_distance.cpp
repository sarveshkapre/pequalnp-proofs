// Exact Hamming distance to a three-raw-clause conjunction on all 169 cells.
// Its zero cells form a union of three arbitrary rectangles. Fix their row
// sets; each column then independently chooses any of the eight unions.
#include "plane_distance_symmetry.hpp"
std::array<Score,8192> dist{};
int main(){
    std::array<Mask,13> rows{},col{};std::vector<Action> group;
    if(int error=read_geometry(rows,col,group))return error;
    std::array<int,8192> orbit;orbit.fill(-1);
    std::vector<Mask> reps;
    for(Mask r=0;r<=full;++r)if(orbit[r]<0){
        int id=reps.size();reps.push_back(r);
        for(const auto& p:group)orbit[p.move(r)]=id;
    }
    for(Mask s=0;s<=full;++s)for(int j=0;j<13;++j)dist[s][j]=std::popcount(s^(full^col[j]));
    int best=170;long long tuples=0,pairs=0;
    for(Mask a:reps){
        std::vector<const Action*> stab;
        for(const auto&p:group)if(p.move(a)==a)stab.push_back(&p);
        std::array<bool,8192> seenB{};
        for(Mask b=0;b<=full;++b)if(!seenB[b]&&orbit[b]>=orbit[a]){
            std::vector<const Action*> st;
            for(auto p:stab){Mask q=p->move(b);seenB[q]=true;if(q==b)st.push_back(p);}
            ++pairs;
            const Mask ab=a|b;
            const Score lo=combine(combine(dist[0],dist[a]),combine(dist[b],dist[ab]));
            std::array<bool,8192> seenC{};
            for(Mask c=0;c<=full;++c)if(!seenC[c]&&orbit[c]>=orbit[b]){
                if(st.size()>1)for(auto p:st)seenC[p->move(c)]=true;
                ++tuples;
                int score=sum(combine(lo,combine(combine(dist[c],dist[c|a]),combine(dist[c|b],dist[c|ab]))));
                if(score<best){
                    best=score;
                    std::cout<<"best "<<score<<" row sets "<<a<<' '<<b<<' '<<c<<std::endl;
                }
            }
        }
    }
    std::cout<<"complete "<<best<<" row subset orbits "<<reps.size()<<" pair representatives "<<pairs
             <<" triple representatives "<<tuples<<std::endl;
}

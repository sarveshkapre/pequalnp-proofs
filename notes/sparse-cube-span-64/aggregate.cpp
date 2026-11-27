// Test the moment kernel on aggregated exponents. All rank witnesses are modulo 1009.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <functional>
#include <iostream>
#include <map>
#include <numeric>
#include <string>
#include <vector>

namespace {
#ifdef CONTROL_MOD11
constexpr int prime = 11;
#else
constexpr int prime = 1009;
#endif
constexpr int limit = 64, max_nodes = 12, max_columns = 21;
using Edge = std::array<int, 2>;
using Shape = std::array<Edge, 3>;
using Row = std::array<int, max_columns>;
constexpr int choose3[] = {1,3,3,1};
int inverse[prime], inv_difference[6*limit+1];

int mod(int value) {
    int result = value % prime;
    return result < 0 ? result + prime : result;
}

struct Basis {
    int size, rank = 0;
    std::array<Row,max_columns> rows{};
    explicit Basis(int n) : size(n) {}
    void insert(Row row) {
        for (int i=0; i<size; ++i) {
            if (!row[i]) continue;
            if (!rows[i][i]) {
                const int scale = inverse[row[i]];
                for (int j=i;j<size;++j) rows[i][j]=row[j]*scale%prime;
                ++rank;
                return;
            }
            const int scale=row[i];
            for (int j=i+1;j<size;++j)
                row[j]=mod(row[j]-scale*rows[i][j]);
        }
    }
};

// Grid points (1,x[,y]). At d=3, x+y<=D. All monomials of homogeneous
// degree D are covered when the products of the constraints have full rank.
struct Grid {
    std::vector<std::array<int,2>> points;
    std::array<std::vector<Row>,6> multipliers;
    Grid(int d, int degree) {
        for (int x=0; x<=degree; ++x)
            for (int y=0; y<=(d==3 ? degree-x : 0); ++y) points.push_back({x,y});
        for (int r=0;r<=degree;++r)
            for (int a=0;a<=degree-r;++a)
                for (int b=0;b<=(d==3 ? degree-r-a : 0);++b) {
                    Row row{};
                    for (std::size_t i=0;i<points.size();++i) {
                        int v=1;
                        for (int j=0;j<a;++j) v=v*points[i][0]%prime;
                        for (int j=0;j<b;++j) v=v*points[i][1]%prime;
                        row[i]=v;
                    }
                    multipliers[r].push_back(row);
                }
    }
};

enum class Proof { nodes, private_relation, aggregate_relation, full_rank, unresolved };

struct MomentKernel {
    int n=0;
    int t[max_nodes]{}, count[max_nodes]{}, slot[3][4]{}, factor[max_nodes]{};

    explicit MomentKernel(const Shape& edges) {
        for (int i=0;i<3;++i) for (int j=0;j<4;++j) {
            const int exponent=(3-j)*edges[i][0]+j*edges[i][1];
            int s=0;
            while (s<n && t[s]!=exponent) ++s;
            if (s==n) t[n++]=exponent;
            slot[i][j]=s;
            ++count[s];
        }
        if (n<9) return;
        for (int i=0;i<n;++i) {
            int weight=1;
            for (int j=0;j<n;++j) if (i!=j)
                weight=weight*inv_difference[3*limit+t[i]-t[j]]%prime;
            factor[i]=weight;
        }
    }

    // Use a cube identity only when all required slots are known.
    static int relation(const int h[],int k) {
        switch(k) {
        case 0: return mod(h[1]*h[1]-3*h[0]*h[2]);
        case 1: return mod(h[2]*h[2]-3*h[1]*h[3]);
        case 2: return mod(h[1]*h[2]-9*h[0]*h[3]);
        case 3: return mod(h[1]*h[1]%prime*h[1]-27*(h[0]*h[0]%prime)*h[3]);
        default:return mod(h[2]*h[2]%prime*h[2]-27*h[0]*(h[3]*h[3]%prime));
        }
    }
    static constexpr int masks[]={7,14,15,11,13};

    int private_mask(int i) const {
        int mask=0;
        for (int j=0;j<4;++j) if(count[slot[i][j]]==1) mask|=1<<j;
        return mask;
    }

    // Nine nodes give exactly one projective aggregate vector. Recover cube
    // slots from adjacent nonzero entries or by splitting a known node sum.
    Proof scalar_case() const {
        int h[3][4]{},known[3]{};
        for(int i=0;i<3;++i) {
            known[i]=private_mask(i);
            for(int j=0;j<4;++j) if(known[i]&(1<<j)) h[i][j]=factor[slot[i][j]];
        }
        bool changed=true, initial=true;
        while(changed) {
            changed=false;
            for(int i=0;i<3;++i) {
                for(int k=0;k<5;++k) if((known[i]&masks[k])==masks[k] && relation(h[i],k))
                    return initial ? Proof::private_relation : Proof::aggregate_relation;
                for(int j=0;j<3 && known[i]!=15;++j) {
                    if(((known[i]>>j)&3)!=3 || !h[i][j] || !h[i][j+1]) continue;
                    int c=h[i][j]*inverse[choose3[j]]%prime;
                    const int next=h[i][j+1]*inverse[choose3[j+1]]%prime;
                    const int ratio=next*inverse[c]%prime;
                    for(int k=0;k<j;++k) c=c*inverse[ratio]%prime;
                    for(int k=0;k<4;++k) {
                        const int value=choose3[k]*c%prime;
                        if((known[i]&(1<<k)) && h[i][k]!=value) return Proof::aggregate_relation;
                        h[i][k]=value;
                        c=c*ratio%prime;
                    }
                    changed=true;
                    known[i]=15;
                }
            }
            initial=false;
            for(int s=0;s<n;++s) {
                int missing=0, ai=0, aj=0, total=0;
                for(int i=0;i<3;++i) for(int j=0;j<4;++j) if(slot[i][j]==s) {
                    if(known[i]&(1<<j)) total+=h[i][j];
                    else {++missing; ai=i; aj=j;}
                }
                const int diff=mod(factor[s]-total);
                if(!missing && diff) return Proof::aggregate_relation;
                if(missing==1) {
                    h[ai][aj]=diff;
                    known[ai]|=1<<aj;
                    changed=true;
                }
            }
        }
        return Proof::unresolved;
    }

    Proof projected(int degree, const Grid& grid) const {
        int vals[3][max_columns][4]{};
        int size=int(grid.points.size());
        for(int point=0;point<size;++point) {
            const auto [x,y]=grid.points[point];
            int aggregate[max_nodes];
            for(int s=0;s<n;++s)
                aggregate[s]=(1+t[s]*(x+t[s]*y))%prime*factor[s]%prime;
            for(int i=0;i<3;++i) for(int j=0;j<4;++j)
                vals[i][point][j]=aggregate[slot[i][j]];
        }
        Basis basis(size);
        for(int i=0;i<3;++i) {
            const int mask=private_mask(i);
            for(int k=0;k<5;++k) if ((mask&masks[k])==masks[k]) {
                const int r=k<3 ? 2:3;
                if (r>degree) continue;
                Row values{};
                for(int h=0;h<size;++h) values[h]=relation(vals[i][h],k);
                for(const auto& mult:grid.multipliers[r]) {
                    Row row{};
                    for(int h=0;h<size;++h) row[h]=values[h]*mult[h]%prime;
                    basis.insert(row);
                    if(basis.rank==size) return Proof::full_rank;
                }
            }
        }
        return Proof::unresolved;
    }

    Proof certify() const {
        if(n<=8) return Proof::nodes;
        if(n==9) return scalar_case();
        static const Grid binary3(2,3), binary5(2,5), ternary3(3,3), ternary4(3,4);
        if(n==10) {
            if(projected(3,binary3)==Proof::full_rank) return Proof::full_rank;
            return projected(5,binary5);
        }
        if(n!=11) std::abort();
        if(projected(3,ternary3)==Proof::full_rank) return Proof::full_rank;
        return projected(4,ternary4);
    }
};

std::vector<Shape> patterns(int k) {
    std::vector<Edge> edges;
    for(int i=0;i<k;++i) for(int j=i+1;j<k;++j) edges.push_back({i,j});
    std::vector<Shape> out;
    for(auto a:edges) for(auto b:edges) for(auto c:edges) {
        if(b<a || c<b) continue;
        Shape shape{a,b,c};
        int degree[5]{};
        for(auto e:shape) for(auto v:e) ++degree[v];
        if(*std::min_element(degree,degree+k)==0 || *std::max_element(degree,degree+k)!=2) continue;
        out.push_back(shape);
    }
    return out;
}
} // namespace

int main(int argc,char** argv) {
    inverse[1]=1;
    for(int i=2;i<prime;++i) inverse[i]=prime-(prime/i)*inverse[prime%i]%prime;
    for(int d=-3*limit;d<=3*limit;++d) inv_difference[3*limit+d]=inverse[mod(d)];
    if constexpr (prime==11) {
        const Shape control={Edge{0,1},Edge{0,10},Edge{1,2}};
        if(argc!=1 || MomentKernel(control).certify()!=Proof::unresolved) return 1;
        std::cout<<"PASS aggregate verifier retains the characteristic-11 witness\n";
        return 0;
    }
    if(argc!=4) {std::cerr<<"usage: aggregate MIN_SPAN MAX_SPAN UNRESOLVED.tsv\n";return 2;}
    int lower=std::stoi(argv[1]), upper=std::stoi(argv[2]);
    if(lower<1 || lower>upper || upper>limit) return 2;
    std::ofstream hard(argv[3]);
    if(!hard) return 2;
    auto a3=patterns(3),a4=patterns(4),a5=patterns(5);
    if(a3.size()!=1 || a4.size()!=18 || a5.size()!=30) return 2;
    std::cout<<"span\tendpoints\tfew_nodes\tprivate_identity\treconstruction\tfull_rank\tunresolved\n";
    for(int span=lower;span<=upper;++span) for(int k=3;k<=5;++k) {
        const auto& pats=k==3 ? a3 : k==4 ? a4 : a5;
        std::array<long long,5> stats{};
        int points[5]={0};
        points[k-1]=span;
        std::function<void(int)> enumerate=[&](int i) {
            if(i<k-1) {
                for(int s=points[i-1]+1;s<=span-(k-1-i);++s) {
                    points[i]=s;
                    enumerate(i+1);
                }
                return;
            }
            for(const auto& pat:pats) {
                Shape edges=pat;
                for(auto& e:edges) for(int& v:e) v=points[v];
                const auto proof=MomentKernel(edges).certify();
                ++stats[int(proof)];
                if(proof==Proof::unresolved) {
                    for(auto e:edges) hard<<e[0]<<' '<<e[1]<<' ';
                    hard<<'\n';
                }
            }
        };
        enumerate(1);
        std::cout<<span<<'\t'<<k;
        for(auto x:stats) std::cout<<'\t'<<x;
        std::cout<<std::endl;
    }
    return hard.good() ? 0 : 2;
}

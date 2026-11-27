// Independent census. Remove a designated cube, solve for the sum of the
// other two, and test necessary binary forms on the designated cube.
#include <algorithm>
#include <array>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

namespace {
#ifdef CONTROL_MOD11
constexpr int p=11;
#else
constexpr int p=10007;
#endif
constexpr int max_power=9, bound=64;
constexpr int binom[]={1,3,3,1};
int inv[p];
int reduce(int x) { int v=x%p; return v<0 ? v+p : v; }

// Unused endpoint coefficients are exact structural zeros. The range must
// continue to include a leading coefficient which merely vanishes modulo p.
struct Form {
    std::array<int,max_power+1> c{};
    int low=max_power+1, high=-1;
    void put(int j,int value) {
        c[j]=value;
        low=std::min(low,j);
        high=std::max(high,j);
    }
};
Form multiply(const Form& a,const Form& b) {
    Form out;
    if(a.high<0 || b.high<0) return out;
    out.low=a.low+b.low;
    out.high=a.high+b.high;
    if(out.high>max_power) std::abort();
    for(int i=a.low;i<=a.high;++i) for(int j=b.low;j<=b.high;++j)
        out.c[i+j]=(out.c[i+j]+a.c[i]*b.c[j])%p;
    return out;
}
Form subtract(Form a,const Form& b,int scale=1) {
    a.low=std::min(a.low,b.low);
    a.high=std::max(a.high,b.high);
    for(int i=b.low;i<=b.high;++i) a.c[i]=reduce(a.c[i]-scale*b.c[i]);
    return a;
}
Form scaled(Form a,int k) {
    for(int i=a.low;i<=a.high;++i) a.c[i]=a.c[i]*k%p;
    return a;
}

struct Univariate {
    int degree=-1;
    std::array<int,max_power+1> c{};
    void trim() {while(degree>=0 && !c[degree]) --degree;}
};
Univariate gcd(Univariate a, Univariate b) {
    while(b.degree>=0) {
        if(!b.degree) return b;
        const int lead_inverse=inv[b.c[b.degree]];
        while(a.degree>=b.degree) {
            int shift=a.degree-b.degree;
            int scale=a.c[a.degree]*lead_inverse%p;
            for(int j=0;j<b.degree;++j) a.c[j+shift]=reduce(a.c[j+shift]-scale*b.c[j]);
            --a.degree;
            a.trim();
        }
        std::swap(a,b);
    }
    return a;
}
struct ProjectiveTest {
    Univariate common;
    bool excludes_infinity=false;
    bool add(const Form& f) {
        if(f.high<0) return false;
        Univariate v;
        v.degree=f.high-f.low;
        for(int j=0;j<=v.degree;++j) v.c[j]=f.c[f.low+j];
        excludes_infinity|=v.c[v.degree]!=0;
        v.trim();
        if(common.degree!=0 && v.degree>=0) common=gcd(common,v);
        return excludes_infinity && common.degree==0;
    }
};

struct Arm {
    int a,b;
    std::array<int,4> nodes;
    Arm(int first,int last):a(first),b(last) {
        for(int j=0;j<4;++j) nodes[j]=(3-j)*a+j*b;
    }
    bool contains(int v) const { return a==v || b==v; }
    bool meets(const Arm& other) const { return contains(other.a)||contains(other.b); }
};

bool simple_cube_failure(const int f[4]) {
    return reduce(f[1]*f[1]-3*f[0]*f[2])!=0 || reduce(f[2]*f[2]-3*f[1]*f[3])!=0
        || reduce(f[1]*f[2]-9*f[0]*f[3])!=0;
}

bool check_monomials(const Form data[8], const int ids[2][4],
                     const bool in_nodes[4],int n) {
    if(n<8) return true;
    for(int j: {0,3}) if(!in_nodes[j]) {
        bool excluded=false;
        for(int a=0;a<2;++a) {
            int f[4];
            for(int k=0;k<4;++k) f[k]=data[ids[a][k]].c[j];
            excluded|=simple_cube_failure(f);
        }
        if(!excluded) return false;
    }
    return true;
}

bool cube_test(ProjectiveTest& test, const Form f[4]) {
    if(test.add(subtract(multiply(f[1],f[1]),multiply(f[0],f[2]),3))) return true;
    if(test.add(subtract(multiply(f[2],f[2]),multiply(f[1],f[3]),3))) return true;
    return test.add(subtract(multiply(f[1],f[2]),multiply(f[0],f[3]),9));
}

// If slot k is the one shared slot, return a necessary identity on the
// private triple and forms num,den satisfying h[k]*den=num identically.
bool private_three(ProjectiveTest& test, const Form f[4],int k,Form& num,Form& den) {
    if(k==0 || k==3) {
        const int near=k==0 ? 1 : 2, far=3-near;
        num=multiply(f[near],f[near]);
        den=scaled(f[far],3);
        return test.add(subtract(multiply(f[far],f[far]),multiply(f[near],f[3-k]),3));
    }
    const int near=3-k, end=k==1 ? 3 : 0, opposite=3-end;
    num=multiply(f[near],f[near]);
    den=scaled(f[end],3);
    return test.add(subtract(multiply(num,f[near]),multiply(multiply(f[end],f[end]),f[opposite]),27));
}

bool project(const Arm& designated,const Arm& left,const Arm& right) {
    int nodes[8], ids[2][4], n=4, missing[2]={-1,-1};
    for(int j=0;j<4;++j) {nodes[j]=left.nodes[j];ids[0][j]=j;}
    for(int j=0;j<4;++j) {
        int i=0;
        while(i<n && nodes[i]!=right.nodes[j]) ++i;
        if(i==n) nodes[n++]=right.nodes[j];
        else {missing[0]=i; missing[1]=j;}
        ids[1][j]=i;
    }
    if(n<7) return false;
    Form data[8], remainder;
    bool inside[4]{};
    for(int j=0;j<4;++j) {
        int t=designated.nodes[j], prod=1, same=-1;
        for(int i=0;i<n;++i) {
            if(nodes[i]==t) {same=i;break;}
            prod=prod*reduce(t-nodes[i])%p;
        }
        if(same>=0) {inside[j]=true; data[same].put(j,p-binom[j]);}
        else {
            if(n==7) remainder.put(j,binom[j]*prod%p);
            for(int i=0;i<n;++i)
                data[i].put(j,reduce(-binom[j]*prod%p*inv[reduce(t-nodes[i])]));
        }
    }
    if(n+std::count(inside,inside+4,false)<=8) return true;
    for(int i=0;i<n;++i) {
        int d=1;
        for(int k=0;k<n;++k) if(i!=k) d=d*reduce(nodes[i]-nodes[k])%p;
        for(int j=0;j<4;++j) if(!inside[j]) data[i].c[j]=data[i].c[j]*inv[d]%p;
    }
    if(!check_monomials(data,ids,inside,n)) return false;
    ProjectiveTest test;
    if(n==7 && test.add(remainder)) return true;
    Form numerator[2],denominator[2];
    for(int i=0;i<2;++i) {
        Form f[4];
        for(int k=0;k<4;++k) f[k]=data[ids[i][k]];
        if(n==8) {if(cube_test(test,f)) return true;}
        else if(private_three(test,f,missing[i],numerator[i],denominator[i])) return true;
    }
    if(n==8) return false;
    Form lhs=multiply(data[missing[0]],multiply(denominator[0],denominator[1]));
    lhs=subtract(lhs,multiply(numerator[0],denominator[1]));
    return test.add(subtract(lhs,multiply(numerator[1],denominator[0])));
}

int classification(const Arm& a,const Arm& b,const Arm& c) {
    if(project(a,b,c)) return 0;
    if(project(b,a,c)) return 0;
    if(project(c,a,b)) return 0;
    // No admissible disjoint or singly linked pair can occur if the union is tiny.
    int values[12];
    std::copy(a.nodes.begin(),a.nodes.end(),values);
    std::copy(b.nodes.begin(),b.nodes.end(),values+4);
    std::copy(c.nodes.begin(),c.nodes.end(),values+8);
    std::sort(values,values+12);
    return std::unique(values,values+12)-values<=8 ? 0 : 1;
}
} // namespace

int main(int argc,char** argv) {
    inv[1]=1;
    for(int i=2;i<p;++i) inv[i]=p-(p/i)*inv[p%i]%p;
    if constexpr (p==11) {
        if(argc!=1 || !classification(Arm(0,1),Arm(0,10),Arm(1,2))) return 1;
        std::cout<<"PASS two-cube verifier retains the characteristic-11 witness\n";
        return 0;
    }
    if(argc<4 || argc>5) {std::cerr<<"usage: two_cubes MIN_SPAN MAX_SPAN UNRESOLVED.tsv [complement]\n";return 2;}
    const bool complement=argc==5;
    if(complement && std::string(argv[4])!="complement") return 2;
    const int low=std::stoi(argv[1]), high=std::stoi(argv[2]);
    if(low<1 || low>high || high>bound) return 2;
    std::ofstream hard(argv[3]);
    if(!hard) return 2;
    std::vector<Arm> arms;
    for(int a=0;a<high;++a) for(int b=a+1;b<=high;++b) arms.emplace_back(a,b);
    long long counts[bound+1][7][2]{};
    for(std::size_t i=0; i<arms.size() && arms[i].a==0; ++i)
        for(std::size_t j=i;j<arms.size();++j) for(std::size_t k=j;k<arms.size();++k) {
            const Arm &a=arms[i], &b=arms[j], &c=arms[k];
            const int span=std::max(a.b,std::max(b.b,c.b));
            if(span<low) continue;
            const bool common=(b.contains(a.a)&&c.contains(a.a)) || (b.contains(a.b)&&c.contains(a.b));
            const bool disjoint=!a.meets(b) && !b.meets(c) && !c.meets(a);
            if((common || disjoint)!=complement) continue;
            const int distinct=2+!a.contains(b.a)+!a.contains(b.b)
                +(!a.contains(c.a)&&!b.contains(c.a))+(!a.contains(c.b)&&!b.contains(c.b));
            const int status=classification(a,b,c);
            ++counts[span][distinct][status];
            if(status) hard<<a.a<<' '<<a.b<<' '<<b.a<<' '<<b.b<<' '<<c.a<<' '<<c.b<<'\n';
        }
    std::cout<<"span\tendpoints\texcluded\tunresolved\n";
    for(int s=low;s<=high;++s) for(int v=complement?2:3;v<=(complement?6:5);++v)
        std::cout<<s<<'\t'<<v<<'\t'<<counts[s][v][0]<<'\t'<<counts[s][v][1]<<'\n';
    return hard.good()?0:2;
}

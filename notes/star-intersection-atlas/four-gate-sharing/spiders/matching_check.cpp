// Verify the forest matching ceiling and the individual forbidden matchings.
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

using Mask = std::uint64_t;
using std::vector;
int indexOf(Mask bit) { return __builtin_ctzll(bit); }
int count(Mask bits) { return __builtin_popcountll(bits); }
Mask one(int i) { return Mask(1) << i; }

struct Host {
    vector<Mask> forward, backward, adjacent, doubleEdge;

    explicit Host(vector<Mask> graph) : forward(graph), backward(graph.size()),
            adjacent(graph.size()), doubleEdge(graph.size()) {
        for (unsigned i=0; i<graph.size(); ++i) {
            if (!(graph[i]&one(i))) throw std::runtime_error("missing matching edge");
            forward[i] &= ~one(i);
            for (unsigned j=0; j<graph.size(); ++j)
                if ((graph[j]&one(i)) && i!=j) backward[i] |= one(j);
            adjacent[i] = forward[i] | backward[i];
            doubleEdge[i] = forward[i] & backward[i];
        }
    }

    // Contract the selected diagonal edges. Two opposite cross edges form
    // a cycle immediately. A new vertex may touch each old component once.
    int largestForest(Mask selected, Mask available) const {
        int best = count(selected);
        while (available) {
            int v = indexOf(available);
            available &= available-1;
            Mask neighbors = selected & adjacent[v];
            bool acyclic = true;
            while (neighbors) {
                Mask front = neighbors & -neighbors, component = front;
                while (front) {
                    int u = indexOf(front);
                    front &= front-1;
                    Mask extra = adjacent[u] & selected & ~component;
                    component |= extra;
                    front |= extra;
                }
                if (count(component & neighbors)>1) { acyclic=false; break; }
                neighbors &= ~component;
            }
            if (acyclic)
                best=std::max(best,largestForest(selected|one(v),available & ~doubleEdge[v]));
        }
        return best;
    }

    // A normalized matching can lose cross edges. Each cross edge that is
    // absent in the proposed spider MUST still be absent after normalization.
    bool fits(const vector<Mask>& target, vector<Mask> domain, Mask pending) const {
        if (!pending) return true;
        int next = indexOf(pending);
        for (Mask bits=pending; bits; bits &= bits-1) {
            int v=indexOf(bits);
            if (count(domain[v])<count(domain[next])) next=v;
        }
        pending &= ~one(next);
        for (Mask options=domain[next]; options; options &= options-1) {
            int u=indexOf(options);
            vector<Mask> reduced=domain;
            bool possible=true;
            for (Mask bits=pending; bits; bits &= bits-1) {
                int v=indexOf(bits);
                reduced[v] &= ~one(u);
                if (!(target[next]&one(v))) reduced[v] &= ~forward[u];
                if (!(target[v]&one(next))) reduced[v] &= ~backward[u];
                if (!reduced[v]) { possible=false; break; }
            }
            if (possible && fits(target,reduced,pending)) return true;
        }
        return false;
    }
};

int main() {
    int cases;
    if (!(std::cin>>cases) || cases<1 || cases>300) return 2;
    vector<vector<Mask>> targets;
    for (int i=0;i<cases;++i) {
        unsigned m;
        if (!(std::cin>>m) || m<2 || m>12) return 2;
        vector<Mask> rows(m);
        for(auto& row:rows) if (!(std::cin>>row) || row>=one(m)) return 2;
        targets.push_back(rows);
    }
    for (int i=1;i<=5;++i) {
        unsigned n;Mask interior;
        if (!(std::cin>>n>>interior) || n>=64 || !n || interior>=one(n)) return 2;
        vector<Mask> rows(n);
        for(auto& row:rows) if (!(std::cin>>row) || row>=one(n)) return 2;
        Host host(rows);
        const vector<Mask> twoDisjointEdges = {1,2};
        if (!host.fits(twoDisjointEdges, vector<Mask>(2,interior), 3)) {
            std::cerr<<"positive matching control failed\n";return 1;
        }
        int maximum=host.largestForest(0,one(n)-1);
        if (maximum!=11) { std::cerr<<"unexpected matching maximum\n";return 1; }
        int num=0;
        for(const auto& target:targets) {
            vector<Mask> domain(target.size(),interior);
            if (host.fits(target,domain,one(target.size())-1)) {
                std::cerr<<"possible embedding: host "<<i<<" pattern "<<num<<"\n";return 1;
            }
            ++num;
        }
        std::cout<<"Host "<<i<<": forest matching maximum "<<maximum<<", "
                 <<num<<" forbidden matchings excluded."<<std::endl;
    }
}

# Four circuit intersections on a subdivided star

**Theorem.** Suppose a finite bipartite tree has at most one vertex of degree at least three. If a circuit constructs its edge set with at most four binary intersections, it has a formula using at most five. Unions of row and column stars are free. A circuit may reuse a gate, and a formula pays separately for each occurrence. The theorem includes all paths and subdivisions of stars, with arbitrary degrees and arm lengths.

**Consequence for arbitrary trees.** If some tree has circuit cost four and formula cost six, there is such a tree on **at most 32 vertices in total** with **at least two vertices of degree at least three** after duplicate leaves are removed. The existence of such a tree remains open here.

## The matching bound that makes the search finite

The [previous four-gate reduction](https://github.com/sarveshkapre/pequalnp-proofs/tree/637ca77a6c4c7d9ca1abbdb80ea02416134f4005/notes/star-intersection-atlas/four-gate-sharing) treats zero cells, so free unions become free meets and a paid intersection becomes a binary join. It checks 7,037 live wirings. All but 40 immediately give formulas of cost at most five. The remaining wirings reduce to five monotone Boolean functions on eight inputs. For each such function f there is a bipartite host with eight-bit words on both shores. The row with word r and column with word c are joined exactly when f(r & c) = 0, where & is bitwise intersection. A graph constructed with that wiring is an induced restriction of the host, allowing duplicate vertex types. The final free meet is included in this representation. Reading a formula on fewer rows and columns preserves its cost bound. Duplicating a vertex also preserves the bound, by copying its memberships in the formula's rectangles.

**Lemma.** In each of the five hosts the largest matching in an induced forest has size exactly 11.

Take any matching in such a forest and write its edges as pairs of words (rᵢ,cᵢ). For each pair, independently extend rᵢ & cᵢ to an inclusion-maximal word z with f(z) = 0. Put every bit of z into both words. Outside z, the two original words were disjoint. Assign each still unassigned bit to one of them. The resulting words Rᵢ,Cᵢ contain the originals, have intersection z, and have union 255. All matched edges survive. By monotonicity, every surviving cross edge was already an edge. If two resulting row words coincide, both cross edges between their matched pairs survive, giving a four-cycle in the original forest. The same holds for column words. Thus the enlarged words still describe a matching with distinct vertices on each side.

The numbers of ordered pairs (R,C) meeting these conditions in the five hosts are 56, 56, 48, 48 and 48. For a selected set of pairs, contract its matched edges. Two oppositely oriented cross edges give a cycle of length four before contraction. In the absence of such a pair of cross edges, acyclicity is exactly acyclicity of the undirected graph after contraction. In increasing pair order the checker adds every possible next pair. It rejects a pair with a double cross edge, or one with two neighbors in the same existing component. Each rejected partial set already contains a cycle. The largest admissible set has size 11 in every host. As a positive control, the replay reconstructs one size-11 matching per host and checks acyclicity directly on its 22 vertices.

Now repeatedly remove one of any two same-shore vertices having identical neighborhoods. In a tree these are duplicate leaves, and their deletion preserves both minimum costs. For a nontrivial reduced tree in one of the five hosts let S be a minimum vertex cover. By Kőnig's theorem its size s equals the maximum matching size, hence s ≤ 11. The vertices outside S are independent. At most s are leaves, since each needs a distinct neighbor in S. If h others have degree at least two, the forest on them together with S has at least 2h edges and at most s+h−1. Thus h ≤ s−1 and the reduced tree has at most 3s−1 ≤ 32 vertices. The single vertex is immediate. This argument applies to trees arising from the five exceptional hosts. The other wirings already have five-gate formulas.

## Why every one-branch tree has a five-gate formula

Root the tree at its branching vertex, or choose a root on the path when no vertex branches. List its arm lengths in decreasing order. After deleting duplicate leaves there is at most one arm of length one. A spider with arms of lengths ℓᵢ has matching number

    Σ floor(ℓᵢ / 2) + 1{at least one arm has odd length}.

Avoiding the hub gives the sum, by matching separately on each arm. Using the hub improves the sum by one exactly when the chosen arm is odd, and a matching can use the hub only once. Hence every exceptional profile has longest arm at most 22. Enumerating the nonincreasing profiles of matching number at most 11, with at most one length-one arm, gives 2,486, including the isolated hub. Truncating arms or deleting them produces an induced subtree, so coordinatewise comparisons of sorted arm lengths suffice for the following cover.

* **44 upper-bound certificates.** Each specifies a spider, a formula shape with five paid joins, and row and column masks. A bit present in both masks is membership in that raw rectangle. The checker evaluates the formula on every cell of the specified spider. The shapes actually used are a union of six rectangles (34 certificates), the nested shape 0 in the replay (nine), and the meet of a five-rectangle union and a two-rectangle union (one). Each certificate also covers every smaller profile it contains.
* **57 exclusions from the exceptional hosts.** Each lists a spider and a matching in it. In each target every row and column has a nonneighbor, so every vertex word x in any representation must have f(x) = 1. Otherwise monotonicity would make that vertex adjacent to every vertex on the opposite side. The condition persists when words are enlarged. The normalized matching must therefore use pairs from the preceding enumeration with f(R) = f(C) = 1. Their counts are 42, 42, 36, 34 and 34. For each target cross edge that was *absent*, the corresponding cross edge between the chosen pairs must be absent. A present cross edge may disappear. The checker assigns distinct pairs to all matched edges with exhaustive backtracking, enforcing these two directional constraints. It finds no assignment in any of the 285 target/host tests. Each exclusion also rules out every larger profile containing it as an induced subtree.

Every one of the 2,486 profiles is either contained in a certified upper-bound profile or contains an excluded profile. Both tests allow either orientation of the bipartition, since the hosts are symmetric and rectangle formulas transpose. This proves the theorem. The argument uses only checkable witnesses and exhaustive finite decisions. A timeout or a failed search for a formula supplies no exclusion.

## Replay

From this directory, with Python 3.10 or later and a C++17 compiler supporting the GCC/Clang bit-count intrinsics, run

```sh
c++ -O3 -std=c++17 -Wall -Wextra -pedantic matching_check.cpp -o /tmp/spider-matching-check
python3 -I -B replay.py /tmp/spider-matching-check
```

The replay reads `evidence.json`, reconstructs the five hosts from the published wiring masks, and ends with these lines. It has no package or solver dependencies. For the preceding wiring classification, follow the linked parent replay.

```text
2486 profiles covered by 44 explicit formulas and 57 forbidden spiders.
Host 1: forest matching maximum 11, 57 forbidden matchings excluded.
Host 2: forest matching maximum 11, 57 forbidden matchings excluded.
Host 3: forest matching maximum 11, 57 forbidden matchings excluded.
Host 4: forest matching maximum 11, 57 forbidden matchings excluded.
Host 5: forest matching maximum 11, 57 forbidden matchings excluded.
```

The proof combines the written reductions with executable finite checks. It has no Lean or official-verifier verdict. Pjscruggs developed the star-intersection atlas. The [8×8 sharing discussion](https://github.com/open-goat/pequalnp-proofs/discussions/23239) records the three-gate forms developed with ChatGPT Pro and the [earlier three-versus-four tree](https://github.com/open-goat/pequalnp-proofs/discussions/23239#discussioncomment-19914235). The matching normalization, 32-vertex bound and subdivided-star theorem are the additions here. For earlier work on graph complexity from stars see [Pudlák, Rödl and Savický](https://users.math.cas.cz/~pudlak/graph-complexity.pdf) and [Jukna](https://www.cambridge.org/core/journals/combinatorics-probability-and-computing/article/abs/on-graph-complexity/6DE2097D9F18AD633EEEDA8C24FBBC75). Priority for these precise statements is unestablished.

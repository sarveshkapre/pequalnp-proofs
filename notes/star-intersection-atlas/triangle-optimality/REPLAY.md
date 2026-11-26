# Reproducing the finite checks

The programs here use C++20 and the Python 3 standard library. Run the commands from this directory. The generated file contains only incidence masks and permutations. No solver, network access or external data are required.

```sh
mkdir -p build
for name in fano_two_distance three_clause_distance two_parallel_distance leafless_rectangles four_nested_audit
do
    c++ -std=c++20 -O3 "$name.cpp" -o "build/$name" || exit 1
done
python3 -I -B plane3_geometry.py > build/geometry.txt
build/fano_two_distance
build/three_clause_distance < build/geometry.txt
build/two_parallel_distance < build/geometry.txt
build/leafless_rectangles 24 2
build/leafless_rectangles 24 3
build/leafless_rectangles 24 4
build/leafless_rectangles 5 5
build/leafless_rectangles 6 5
build/four_nested_audit 25
build/four_nested_audit 24
```

The [ten final output lines](finite-checks.txt) were recorded in a fresh Mac replay with networking disabled for the checkers. The labelled searches count every cell. The type checks bound all possible incidence boards satisfying necessary constraints. A surviving profile in the order-four control means it passes the two pair-count tests. The triangle construction itself attains the bound.

For the separately formalized row inequalities, [the source](ChainHamming.lean) includes the three axiom queries, and the [fresh Mac kernel record](chain-hamming-kernel.log) reports their output under Lean 4.36.0. From a matching Mathlib environment, the commands are:

```sh
lake env lean -DwarningAsError=true -o ChainHamming.olean ChainHamming.lean
lake env sh -c 'LEAN_PATH=".:$LEAN_PATH" leanchecker -v ChainHamming'
```

These lemmas concern nested predicted rows. Formalizing the triangle optimum would additionally require the topology reduction, signed-weight bounds and verification of the finite cases.

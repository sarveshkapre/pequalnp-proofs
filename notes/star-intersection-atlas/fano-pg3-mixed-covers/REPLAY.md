# Replaying the checks

Use Python 3.10 or later, with assertions enabled. Start in the directory containing this file.

## Constructions and the Fano weight certificate

```sh
python3 -I check_examples.py
python3 -B search/check_saved.py
```

The first check evaluates the actual sets on the negative cells and verifies every weight vector decoded from the Lean certificate. The three lists of counts, in canonical, row and column order, should be `(21, 84, 84)`, `(52, 468, 406)` and `(52, 468, 468)`. The Fano weights cover 2,260 families and 30,548 eligible triples. The second command applies the independent signed-word checker to the saved list of 194 row families. It should find 478 designs, 85 with a possible column antichain, and zero two-sided solutions. The full enumeration below checks that the saved list is complete.

## Lean source and kernel replay

The proof sources use Lean 4.36.0 and Mathlib revision `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. From a checkout with the pinned Mathlib and its dependencies already built, run the following command, replacing the argument with the absolute path to this note's replay script.

```sh
lake env python3 /absolute/path/to/replay_lean.py
```

The replay builds 25 files from source in a fresh temporary directory, then invokes the standalone Lean kernel checker on the four target modules. Read the emitted axiom reports for the named theorems. The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`. The pinned Lean compiler commit is `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`. The printed warnings about unused section variables concern the formulation of helper lemmas.

## Regenerating the order-three lower bound

The first two search programs below read the same symmetry-reduced row-family stream. They implement different geometric tests. The two final checks implement the constraints on both sides independently. This is a finite computation. It uses C++20 with support for 128-bit unsigned integers and Python's standard library. The full enumeration can take substantial CPU time.

Run this block in Bash in the note directory. It creates a fresh temporary directory for executables and intermediate results. Each retained row family is identified by its stratum, index and thirteen 16-bit face masks.

```bash
set -euo pipefail
scratch=$(mktemp -d)
for name in mixed_family_generator mixed_count_check mixed_screen mixed_pencil_check mixed_faces; do
    clang++ -std=c++20 -O3 "search/$name.cpp" -o "$scratch/$name"
done
"$scratch/mixed_count_check" > "$scratch/independent-counts"
awk 'NR > 1 {print $1, $3}' search/expected.tsv | diff - "$scratch/independent-counts"
for i in {0..13}; do
    for screen in mixed_screen mixed_pencil_check; do
        "$scratch/mixed_family_generator" "$i" 2>"$scratch/generator-$i" |
            "$scratch/$screen" "$scratch/$screen-$i" > "$scratch/$screen-$i.log"
    done
    awk -v i="$i" '$1 != "#" && $1 == i {sub(/^[0-9]+ /,""); print}' search/survivors.txt > "$scratch/expected-$i"
    cmp "$scratch/mixed_screen-$i" "$scratch/expected-$i"
    cmp "$scratch/mixed_pencil_check-$i" "$scratch/expected-$i"
    "$scratch/mixed_faces" < "$scratch/expected-$i" > "$scratch/final-$i"
    awk 'NF && $2 != "EXCLUDED" {bad=1} END {exit bad}' "$scratch/final-$i"
    test "$(wc -l < "$scratch/final-$i")" -eq "$(wc -l < "$scratch/expected-$i")"
    cat "$scratch/generator-$i"
done
python3 -B search/check_saved.py
```

Compare the reported orbit and labeled-family counts for all fourteen strata against [the expected counts](search/expected.tsv). The totals are 23,823,975 orbits and 9,107,560,888 labeled families. The independent count by dimension does not use the orbit stream.

## Release readback on November 26, 2026

The offline Mac rebuild compiled all 25 files from this package and the standalone kernel accepted the four target modules in 188 seconds. In this source set the following reports were observed.

```text
'FusionFanoLower.fano_not_row_mixed_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'FusionFanoLower.fano_not_full_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'FusionRowMixedCounterexample.plane3_row_mixed_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'FusionRowMixedCounterexample.explicit_missing_mixed_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'FanoMixedFour.four_pairs' depends on axioms: [propext, Classical.choice, Quot.sound]
'Plane3MixedFive.five_pairs' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The release check also reproduced every stratum of the independent labeled-antichain count, regenerated both screening streams for strata zero and one, and reran both final checkers over all 194 saved families. The complete 23,823,975-orbit exclusion is from the earlier all-stratum runs.

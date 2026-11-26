# Finite circuit and rectangle certificates

- [Two exact circuit sizes](mask-69/README.md). On five inputs, mask 69 needs seven gates. Its six-input extension needs eight.
- [Fourteen rectangles and two holes](rectangle-cover/README.md). Two explicit arrangements cover 334 of 336 required cells on a 21-by-21 board. A full cover with fifteen rectangles provides a control.

The proofs use Lean 4.36.0 and the definitions at [upstream revision e6bfe1a](https://github.com/open-goat/pequalnp-proofs/tree/e6bfe1a56efc768d244627b78f175b18de1acd6f). In a checkout of that revision with its pinned dependencies available, run `lake build PEqualNP.Defs` from its `lean/` directory. Then run the following from this directory, supplying the external checkout and the corresponding toolchain’s `bin` directory.

```sh
python3 replay.py /path/to/pequalnp-proofs /path/to/lean-4.36.0/bin
```

The driver compiles seven proof modules in a temporary directory and rechecks their declarations with the standalone kernel checker. Add `--fresh` to also recheck all imported declarations separately for each module. The rectangle case also includes a separate reproducible symmetry search.

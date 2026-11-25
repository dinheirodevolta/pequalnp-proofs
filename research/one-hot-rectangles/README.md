# A rectangle lower bound for one-hot bipartite graphs

Given a Boolean adjacency matrix, put one input wire on each row and each column. A circuit represents the graph if it returns the matrix entry whenever exactly one row and one column are selected. AND and OR gates have at most two inputs. Inputs are free and gates can be shared.

Count a row if it has a one in a column containing a zero. Count a column if it has a one in a row containing a zero. Write **k** for the number of vertices counted. Remove every all-one row and column in a single pass, taking universality in the original matrix. If a remaining 2-by-2 submatrix has exactly three ones, every representing circuit has **at least k gates**. Mask 301 has seven forced inputs and such a submatrix on rows 0 and 2 and columns 0 and 2.

The usual input-count bound is k − 1. At equality, each forced input labels one rectangle in the communication protocol induced by a read-once tree. The three-one pattern forces two distinct labels onto the same positive/negative pair. If the residual graph has no such pattern, its nontrivial components are disjoint bicliques. Their formulas and the universal literals give exactly k − 1 gates for a nonconstant table. The research note gives the proof of this converse.

## Lean results

The theorems are in namespace `PEqualNP.RectangleBound`. The module can be imported as `PEqualNP.Research.OneHotRectangles` from this branch. [Lean source](../../lean/PEqualNP/Research/OneHotRectangles.lean)

| Declaration | What it proves |
| --- | --- |
| `lower_of_clash` | A lower bound from conflicting forced rectangles on an arbitrary sample domain |
| `graph_lower_of_residual_path` | The graph-specific bound in terms of the adjacency matrix and its forced vertices |
| `mask301_lower` | The seven-gate lower bound as an application of the graph theorem |
| `hubIncidence_exact` | An explicit connected family has minimum size 2t + 5 for every t ≥ 1, with both bounds machine-checked |

To construct the family, start with a four-vertex path and t independent edges, then add a row adjacent to every column. Deleting this row exposes the path. The Lean proof also constructs a circuit attaining the bound.

## Reproduce

Run the following commands from the repository root with the pinned Lean toolchain and Mathlib dependencies available.

```sh
cd lean
lake build PEqualNP.Research.OneHotRectangles
```

From the repository root, Python 3.10 or later can analyze a single mask or enumerate read-once formulas for the 3-by-3 and 4-by-4 surveys. The script uses the standard library.

```sh
python research/one-hot-rectangles/rectangle_survey.py --rows 4 --cols 4 --mask 301
python research/one-hot-rectangles/rectangle_survey.py
```

Among 65,534 nonconstant 4-by-4 tables, 9,974 attain k − 1 and 55,560 have the obstruction. The formula enumeration and adjacency test agreed on every table. The latter count records a lower bound and can include tables whose minimum exceeds k.

The formalization builds on the project's earlier circuit-extraction and rectangle arguments and uses the project's definition of graph representation. [Research note with proofs and references](note.pdf) · [Original mask-301 pull request](https://github.com/open-goat/pequalnp-proofs/pull/11622)

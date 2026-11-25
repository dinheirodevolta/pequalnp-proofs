"""Check the one-hot graph criterion against exhaustive read-once formula tables.

Use Python 3.10 or later. Run with no arguments for the 3-by-3 and 4-by-4
surveys. Use --rows N --cols M to survey a small single dimension, or add
--mask 301 to analyze just one table without enumerating formulas. Bit i*M+j
is the adjacency entry in row i, column j. No external packages are needed.
"""

from argparse import ArgumentParser
from itertools import combinations


def input_tables(n, m):
    rows = [((1 << m) - 1) << (i * m) for i in range(n)]
    cols = [sum(1 << (i * m + j) for i in range(n)) for j in range(m)]
    return rows + cols


def read_once_tables(inputs):
    """DP indexed by the exact set of leaves; try all disjoint root splits."""
    tables = [set() for _ in range(1 << len(inputs))]
    for index, table in enumerate(inputs):
        tables[1 << index].add(table)
    for support in range(1, len(tables)):
        anchor = support & -support
        rest = support ^ anchor
        right = rest
        while right:
            left = support ^ right
            values = tables[support]
            for a in tables[left]:
                for b in tables[right]:
                    values.add(a & b)
                    values.add(a | b)
            right = (right - 1) & rest
    return tables


def graph_criterion(table, n, m, inputs):
    """Return forced input bitset and a P4 certificate, if one exists."""
    rows, cols = inputs[:n], inputs[n:]
    core_rows = [i for i, mask in enumerate(rows) if table & mask != mask]
    core_cols = [j for j, mask in enumerate(cols) if table & mask != mask]
    forced_rows = [i for i in range(n)
                   if any(table & (1 << (i * m + j)) for j in core_cols)]
    forced_cols = [j for j in range(m)
                   if any(table & (1 << (i * m + j)) for i in core_rows)]
    required = sum(1 << i for i in forced_rows) + sum(1 << (n+j) for j in forced_cols)
    for a, b in combinations(core_rows, 2):
        for c, d in combinations(core_cols, 2):
            cells = (a*m+c, a*m+d, b*m+c, b*m+d)
            if sum((table >> k) & 1 for k in cells) == 3:
                return required, ((a, b), (c, d))
    return required, None


def survey(n, m):
    inputs = input_tables(n, m)
    tables = read_once_tables(inputs)
    any_read_once = set().union(*tables)
    successes = failures = 0
    for table in range(1, (1 << (n*m)) - 1):
        support, obstruction = graph_criterion(table, n, m, inputs)
        has_formula = table in tables[support]
        if has_formula != (obstruction is None):
            raise AssertionError((n, m, table, support, obstruction, has_formula))
        if has_formula != (table in any_read_once):
            raise AssertionError(("extra leaves change representability", n, m, table))
        if has_formula:
            successes += 1
        else:
            failures += 1
    print(f"{n} x {m}: {successes+failures:,} nonconstant tables; "
          f"{successes:,} attain the input-count bound; "
          f"{failures:,} have a P4 obstruction; 0 disagreements")
    if (n, m) == (4, 4):
        support, certificate = graph_criterion(301, n, m, inputs)
        print(f"mask 301: {support.bit_count()} forced inputs; "
              f"witness rows and columns {certificate}")


def analyze(table, n, m):
    if not 0 <= table < (1 << (n*m)):
        raise ValueError("The mask must fit the row-by-column table.")
    if table == 0 or table == (1 << (n*m)) - 1:
        print("Constant table; the theorem assumes both a zero and a one.")
        return
    support, witness = graph_criterion(table, n, m, input_tables(n, m))
    print("Forced rows:", [i for i in range(n) if support & (1 << i)])
    print("Forced columns:", [j for j in range(m) if support & (1 << (n+j))])
    if witness is None:
        print("Exact gate count:", support.bit_count()-1)
    else:
        print("Induced path (row pair, column pair):", witness)
        print("Gate lower bound:", support.bit_count())


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--rows", type=int)
    parser.add_argument("--cols", type=int)
    parser.add_argument("--mask", type=lambda value: int(value, 0))
    args = parser.parse_args()
    if args.rows is None and args.cols is None and args.mask is None:
        survey(3, 3)
        survey(4, 4)
    elif args.rows is None or args.cols is None:
        parser.error("Specify both --rows and --cols.")
    elif min(args.rows, args.cols) < 1:
        parser.error("Both dimensions must be positive.")
    elif args.mask is not None:
        if not 0 <= args.mask < 1 << (args.rows*args.cols):
            parser.error("The mask must fit the row-by-column table.")
        analyze(args.mask, args.rows, args.cols)
    else:
        survey(args.rows, args.cols)

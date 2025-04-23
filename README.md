# Property based testing for compute_scc()

Geneate 1M small graphs (up to 32 vertexs). For each such graph verify
that SCCs computed by `compute_scc()` are correct:
- generate a small graph;
- use DFS to compute a matrix of vertexes reachable from each vertex;
- compute SCCs using `compute_scc()`;
- for each pair of vertexes `v` reachable from `u`:
  - if `u` is also reachable from `v` then `u` and `v` must be in a same SCC;
  - otherwise `u` and `v` must be in different SCCs.
- for each pair of vertexes `v` not reachable from `u`, `u` and `v` must
  be in different SCCs.

Mock kernel functions to allow copy-pasting `compute_scc()` as-is.

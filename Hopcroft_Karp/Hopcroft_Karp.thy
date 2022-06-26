theory Hopcroft_Karp
  imports
    Edmonds_Karp
begin

text \<open>
The goal of this project was to specify the Hopcroft-Karp algorithm, which solves the maximum
cardinality matching problem in bipartite graphs, and to verify its correctness.

The algorithmic idea is based on Berge's theorem (@{thm Berge}), which states that a matching
is maximum if and only if there is no augmenting path. The algorithm finds, in each iteration, a
maximal set of vertex-disjoint shortest augmenting paths and augments the matching until there is no
augmenting path.

Unfortunately, we had to cut the project short, and only specified and verified a shortest
augmenting path algorithm, which, in each iteration, finds a single shortest augmenting path instead
of a maximal set of such paths. We believe our formalization of the shortest augmenting path
algorithm could be extended to a formalization of the Hopcroft-Karp algorithm.
\<close>

end
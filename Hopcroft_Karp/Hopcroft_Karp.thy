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

Unfortunately, we had to cut the project short, and only specified and verified an adaption
(@{term edmonds_karp.edmonds_karp}) of the Edmonds-Karp algorithm to the maximum cadinality matching
problem in bipartite graphs, which, in each iteration, finds a single shortest augmenting path
instead of a maximal set of such paths. We believe this formalization of the Edmonds-Karp algorithm
can be extended to a formalization of the Hopcroft-Karp algorithm.
\<close>

text \<open>
More precisely, let G, L, R, s, t, M be the input of @{term edmonds_karp.loop'}, and let p be the
@{term shortest_alt_path} from s to t induced by the parent map output by @{term alt_bfs.alt_bfs}.
Then @{term "butlast (tl p)"} is a shortest augmenting path from a free vertex in L to a free vertex
in R.

To find a maximum set of such paths, we can iterate through all free vertices v in R, obtain the
unique (if any) @{term shortest_alt_path} p' from s to v induced by the parent map, and check if its
length is equal to the length of p minus one (as @{term "butlast p"} is a @{term shortest_alt_path}
from s to a free vertex in R). Then @{term "tl p'"} is a shortest augmenting path from a free vertex
in L to a free vertex in R.

To ensure that the augmenting paths found in this way are vertex-disjoint, every time we find a
@{term shortest_alt_path} from s to a free vertex in R, we remove this path from the parent map.
Hence, in addition to having to check if the length of the path to a free vertex v in R found is
equal to the length of p minus one, we have to check if the path found is indeed a path from s to v.
\<close>

end
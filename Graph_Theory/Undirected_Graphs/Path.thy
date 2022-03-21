theory Path
  imports
    Graph_Tbd
    "../../Misc_Tbd"
begin

text \<open>This theory extends the formalization of undirected paths.\<close>

section \<open>Paths\<close>

type_synonym 'a path = "'a list"

abbreviation path_length :: "'a path \<Rightarrow> nat" where
  "path_length p \<equiv> length (edges_of_path p)"

subsection \<open>\<close>

lemma path_snocD:
  assumes "path G (p @ [u, v])"
  shows "{u, v} \<in> G"
  using assms
  by (auto dest: path_suff)

lemma path_butlastI:
  assumes "path G p"
  shows "path G (butlast p)"
proof (cases p)
  case Nil
  thus ?thesis
    by simp
next
  case Cons
  hence "p \<noteq> []"
    by simp
  thus ?thesis
    using assms
    by (intro path_pref[where ?p1.0 = "butlast p" and ?p2.0 = "[last p]"]) simp
qed

lemma pathI:
  assumes "set (edges_of_path p) \<subseteq> G"
  assumes "set p \<subseteq> Vs G"
  shows "path G p"
  using assms
  by (induct p rule: edges_of_path.induct) simp+

subsection \<open>\<close>

lemma edges_of_path_tl:
  shows "edges_of_path (tl p) = tl (edges_of_path p)"
  by (induct p rule: edges_of_path.induct) simp+

lemma edges_of_path_butlast:
  shows "edges_of_path (butlast p) = butlast (edges_of_path p)"
  by (induct p rule: edges_of_path.induct) (auto elim: edges_of_path.elims)

lemma edges_of_path_append_4:
  assumes "p \<noteq> []"
  assumes "q \<noteq> []"
  assumes "last p = hd q"
  shows "edges_of_path (p @ tl q) = edges_of_path p @ edges_of_path q"
  using assms
  by (simp add: edges_of_path_append_3)

section \<open>Walks\<close>

subsection \<open>\<close>

lemma walk_betw_ConsI:
  assumes "walk_betw G v p w"
  assumes "{u, v} \<in> G"
  shows "walk_betw G u (u # p) w"
proof (standard, goal_cases)
  case 1
  show ?case
    using assms
  proof (induct p rule: edges_of_path.induct)
    case 1
    thus ?case
      by auto
  next
    case (2 v)
    thus ?case
      by (force dest: walk_between_nonempty_path(1, 3))
  next
    case (3 v v' l)
    thus ?case
      by (force dest: walk_between_nonempty_path(1, 3))
  qed
next
  case 4
  show ?case
    using assms(1)
    by fastforce
qed simp+

lemma walk_transitive_2:
  assumes "walk_betw G u p v"
  assumes "walk_betw G v q w"
  shows "walk_betw G u (butlast p @ q) w"
  using assms
  by (auto dest: walk_between_nonempty_path(2) simp add: walk_between_nonempty_path(3, 4) butlast_tl_conv intro: walk_transitive)

subsection \<open>Decomposing walks\<close>

subsubsection \<open>Splitting a walk at a vertex\<close>

fun is_path_vertex_decomp :: "'a graph \<Rightarrow> 'a path \<Rightarrow> 'a \<Rightarrow> 'a path \<times> 'a path \<Rightarrow> bool" where
  "is_path_vertex_decomp G p v (q, r) \<longleftrightarrow> p = q @ tl r \<and> (\<exists>u w. walk_betw G u q v \<and> walk_betw G v r w)"

definition path_vertex_decomp :: "'a graph \<Rightarrow> 'a path \<Rightarrow> 'a \<Rightarrow> 'a path \<times> 'a path" where
  "path_vertex_decomp G p v \<equiv> SOME qr. is_path_vertex_decomp G p v qr"

subsubsection \<open>\<close>

abbreviation closed_path :: "'a graph \<Rightarrow> 'a path \<Rightarrow> 'a \<Rightarrow> bool" where
  "closed_path G c v \<equiv> walk_betw G v c v \<and> Suc 0 < length c"

fun is_closed_path_decomp :: "'a graph \<Rightarrow> 'a path \<Rightarrow> 'a path \<times> 'a path \<times> 'a path \<Rightarrow> bool" where
  "is_closed_path_decomp G p (q, r, s) \<longleftrightarrow>
   p = q @ tl r @ tl s \<and>
   (\<exists>u v w. walk_betw G u q v \<and> closed_path G r v \<and> walk_betw G v s w) \<and>
   distinct q"

definition closed_path_decomp :: "'a graph \<Rightarrow> 'a path \<Rightarrow> 'a path \<times> 'a path \<times> 'a path" where
  "closed_path_decomp G p \<equiv> SOME qrs. is_closed_path_decomp G p qrs"

section \<open>Distinct paths\<close>

definition distinct_path :: "'a graph \<Rightarrow> 'a path \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "distinct_path G p u v \<equiv> walk_betw G u p v \<and> distinct p"

lemma distinct_pathD:
  assumes "distinct_path G p u v"
  shows
    "walk_betw G u p v"
    "distinct p"
  using assms
  by (simp_all add: distinct_path_def)

lemma distinct_pathI:
  assumes "walk_betw G u p v"
  assumes "distinct p"
  shows "distinct_path G p u v"
  using assms
  by (simp add: distinct_path_def)

section \<open>Reachability\<close>

definition reachable :: "'a graph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "reachable G u v \<equiv> \<exists>p. walk_betw G u p v"

end
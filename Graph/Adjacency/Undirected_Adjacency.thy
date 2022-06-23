subsubsection \<open>Undirected adjacency structure\<close>

theory Undirected_Adjacency
  imports
    Adjacency
    AGF.Berge
    "../Undirected_Graph/Graph_Ext"
begin

text \<open>If the adjacency structure is symmetric, then it induces an undirected graph.\<close>

locale adjacency' = adjacency where
  Map_update = Map_update for
  Map_update :: "'a::linorder \<Rightarrow> 't \<Rightarrow> 'm \<Rightarrow> 'm" +
  fixes G :: 'm
  assumes invar: "invar G"

locale symmetric_adjacency = adjacency' where
  Map_update = Map_update for
  Map_update :: "'a::linorder \<Rightarrow> 't \<Rightarrow> 'm \<Rightarrow> 'm" +
  assumes symmetric: "v \<in> set (adjacency_list G u) \<longleftrightarrow> u \<in> set (adjacency_list G v)"

lemmas \<^marker>\<open>tag invisible\<close> (in symmetric_adjacency) invar = invar

abbreviation \<^marker>\<open>tag invisible\<close> (in adjacency) symmetric_adjacency' :: "'m \<Rightarrow> bool" where
  "symmetric_adjacency' G \<equiv>
   symmetric_adjacency
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    G
    Map_update"

definition (in adjacency) E :: "'m \<Rightarrow> 'a set set" where
  "E G \<equiv> {{u, v} |u v. v \<in> set (adjacency_list G u)}"

definition (in adjacency) V :: "'m \<Rightarrow> 'a set" where
  "V G \<equiv> Vs (E G)"

lemma (in adjacency) finite_E:
  assumes "invar G"
  shows "finite (E G)"
proof (rule finite_subset)
  { fix u v
    assume "{u, v} \<in> E G"
    then consider (u_v) "v \<in> set (adjacency_list G u)" | (v_u) "u \<in> set (adjacency_list G v)"
      by (auto simp add: E_def doubleton_eq_iff)
    hence "{u, v} \<subseteq> M.dom G \<union> \<Union> (S.set ` M.ran G)"
    proof (cases)
      case u_v
      then obtain s where
        "Map_lookup G u = Some s"
        "v \<in> S.set s"
        by (elim mem_adjacencyE)
      hence
        "u \<in> M.dom G"
        "v \<in> \<Union> (S.set ` M.ran G)"
        by (auto simp add: M.mem_dom_iff M.ran_def)
      thus ?thesis
        by fast
    next
      case v_u
      then obtain s where
        "Map_lookup G v = Some s"
        "u \<in> S.set s"
        by (elim mem_adjacencyE)
      hence
        "v \<in> M.dom G"
        "u \<in> \<Union> (S.set ` M.ran G)"
        by (auto simp add: M.mem_dom_iff M.ran_def)
      thus ?thesis
        by fast
    qed }
  thus "E G \<subseteq> Pow (M.dom G \<union> \<Union> (S.set ` M.ran G))"
    by (auto simp add: E_def)
  show "finite ..."
    using assms
    by (auto simp add: S.set_def dest: invarD(1) intro: M.finite_dom M.finite_ran)
qed

lemma (in symmetric_adjacency) mem_adjacency_iff_edge:
  shows "v \<in> set (adjacency_list G u) \<longleftrightarrow> {u, v} \<in> E G"
proof (standard, goal_cases)
  case 1
  thus ?case
    by (auto simp add: E_def)
next
  case 2
  hence "v \<in> set (adjacency_list G u) \<or> u \<in> set (adjacency_list G v)"
    by (auto simp add: E_def doubleton_eq_iff)
  thus ?case
    by (simp add: symmetric)
qed

lemma (in symmetric_adjacency) mem_adjacency_iff_edge_2:
  shows "u \<in> set (adjacency_list G v) \<longleftrightarrow> {u, v} \<in> E G"
  by (simp add: symmetric mem_adjacency_iff_edge[symmetric])

lemma (in adjacency) finite_V:
  assumes "invar G"
  shows "finite (V G)"
  using assms
  by (fastforce simp add: V_def Vs_def E_def dest: finite_E)

context adjacency'
begin
sublocale finite_graph "E G"
proof (standard, goal_cases)
  case 1
  show ?case
    by (auto simp add: E_def)
next
  case 2
  show ?case
    using invar
    by (intro finite_E)
qed
end

text \<open>We redefine graph operation insert such that it maintains symmetry.\<close>

definition (in adjacency) insert_edge :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" where
  "insert_edge u v G \<equiv> insert' v u (insert' u v G)"

lemma (in adjacency) invar_insert_edge:
  assumes "invar G"
  shows "invar (insert_edge u v G)"
  using assms
  by (auto simp add: insert_edge_def intro: invar_insert')

lemma (in adjacency) adjacency_insert_edge_cong:
  assumes "invar G"
  shows
    "set (adjacency_list (insert_edge u v G) w) =
     set (adjacency_list G w) \<union> (if w = u then {v} else if w = v then {u} else {})"
  using assms invar_insert'
  by (simp add: insert_edge_def adjacency_insert'_cong)

lemma (in adjacency) E_insert_edge_cong:
  assumes "invar G"
  shows "E (insert_edge u v G) = E G \<union> {{u, v}}"
  using assms
proof -
  { fix x y
    have
      "{x, y} \<in> E (insert_edge u v G) \<longleftrightarrow>
       x \<in> set (adjacency_list (insert_edge u v G) y) \<or>
       y \<in> set (adjacency_list (insert_edge u v G) x)"
      by (auto simp add: E_def doubleton_eq_iff)
    also have
      "... \<longleftrightarrow>
       x \<in> set (adjacency_list G y) \<or> (y = u \<and> x = v) \<or>
       y \<in> set (adjacency_list G x) \<or> (x = u \<and> y = v)"
      using assms
      by (simp add: adjacency_insert_edge_cong)
    also have "... \<longleftrightarrow> {x, y} \<in> E G \<union> {{u, v}}"
      by (auto simp add: E_def doubleton_eq_iff)
    finally have "{x, y} \<in> E (insert_edge u v G) \<longleftrightarrow> {x, y} \<in> E G \<union> {{u, v}}"
      . }
  thus ?thesis
    by (intro graphs_eqI) (auto simp add: E_def graph_def)
qed

lemma (in adjacency) invar_fold_insert_edge:
  assumes "invar G"
  shows "invar (fold (insert_edge u) l G)"
  using assms
proof (induct l arbitrary: G)
  case Nil
  thus ?case
    by simp
next
  case Cons
  thus ?case
    by (auto intro: invar_insert_edge Cons.hyps)
qed

lemma (in adjacency) adjacency_fold_insert_edge_cong:
  assumes "invar G"
  shows
    "set (adjacency_list (fold (insert_edge u) l G) v) =
     set (adjacency_list G v) \<union>
     (\<Union>w\<in>set l. if v = u then {w} else if v = w then {u} else {})"
  using assms
proof (induct l arbitrary: G)
  case Nil
  thus ?case
    by simp
next
  case (Cons w ws)
  have
    "set (adjacency_list (fold (insert_edge u) (w # ws) G) v) =
     set (adjacency_list (fold (insert_edge u) ws (insert_edge u w G)) v)"
    by simp
  also have
    "... =
     set (adjacency_list (insert_edge u w G) v) \<union>
     (\<Union>w\<in>set ws. if v = u then {w} else if v = w then {u} else {})"
    using Cons.prems
    by (intro invar_insert_edge Cons.hyps)
  also have
    "... =
     set (adjacency_list G v) \<union>
     (if v = u then {w} else if v = w then {u} else {}) \<union>
     (\<Union>w\<in>set ws. if v = u then {w} else if v = w then {u} else {})"
    using Cons.prems
    by (simp add: adjacency_insert_edge_cong)
  also have
    "... =
     set (adjacency_list G v) \<union>
     (\<Union>w\<in>set (w # ws). if v = u then {w} else if v = w then {u} else {})"
    by auto
  finally show ?case
    .
qed

lemma (in adjacency) E_fold_insert_edge_cong:
  assumes "invar G"
  shows "E (fold (insert_edge u) l G) = E G \<union> {{u, v} |v. v \<in> set l}"
proof -
  { fix x y
    have
      "{x, y} \<in> E (fold (insert_edge u) l G) \<longleftrightarrow>
       x \<in> set (adjacency_list (fold (insert_edge u) l G) y) \<or>
       y \<in> set (adjacency_list (fold (insert_edge u) l G) x)"
      by (auto simp add: E_def doubleton_eq_iff)
    also have
      "... \<longleftrightarrow>
       x \<in> set (adjacency_list G y) \<or> (y = u \<and> x \<in> set l) \<or>
       y \<in> set (adjacency_list G x) \<or> (x = u \<and> y \<in> set l)"
      using assms
      by (simp add: adjacency_fold_insert_edge_cong)
    also have "... \<longleftrightarrow> {x, y} \<in> E G \<union> {{u, v} |v. v \<in> set l}"
      by (auto simp add: E_def doubleton_eq_iff)
    finally have "{x, y} \<in> E (fold (insert_edge u) l G) \<longleftrightarrow> {x, y} \<in> E G \<union> {{u, v} |v. v \<in> set l}"
      . }
  thus ?thesis
    by (intro graphs_eqI) (auto simp add: E_def graph_def)
qed

text \<open>
We show that graph operations union and difference correspond to the respective set operations in
terms of @{term adjacency.E}, and that they maintain symmetry.
\<close>

lemma (in adjacency) E_union_cong:
  assumes "invar G1"
  assumes "invar G2"
  shows "E (union G1 G2) = E G1 \<union> E G2"
  using assms
  by (auto simp add: E_def adjacency_union_cong)

lemma (in adjacency) V_union_cong:
  assumes "invar G1"
  assumes "invar G2"
  shows "V (union G1 G2) = V G1 \<union> V G2"
  using assms
  by (simp add: V_def Vs_def E_union_cong)

lemma (in adjacency) finite_V_union:
  assumes "invar G1"
  assumes "invar G2"
  shows "finite (V (union G1 G2))"
  using assms
  by (intro invar_union finite_V)

lemma (in adjacency) symmetric_adjacency_union:
  assumes "symmetric_adjacency' G1"
  assumes "symmetric_adjacency' G2"
  shows "symmetric_adjacency' (union G1 G2)"
proof (standard, goal_cases)
  case 1
  show ?case
    using assms
    by (intro symmetric_adjacency.invar invar_union)
next
  case (2 v u)
  have
    "v \<in> set (adjacency_list (union G1 G2) u) \<longleftrightarrow>
     v \<in> set (adjacency_list G1 u) \<union> set (adjacency_list G2 u)"
    using assms
    by (fastforce simp add: adjacency_union_cong dest: symmetric_adjacency.invar)
  also have "... \<longleftrightarrow> u \<in> set (adjacency_list G1 v) \<union> set (adjacency_list G2 v)"
    using assms
    by (simp add: symmetric_adjacency.symmetric)
  also have "... \<longleftrightarrow> u \<in> set (adjacency_list (union G1 G2) v)"
    using assms
    by (fastforce simp add: adjacency_union_cong dest: symmetric_adjacency.invar)
  finally show ?case
    .
qed

lemma (in adjacency) symmetric_adjacency_difference:
  assumes "symmetric_adjacency' G1"
  assumes "symmetric_adjacency' G2"
  shows "symmetric_adjacency' (difference G1 G2)"
proof (standard, goal_cases)
  case 1
  show ?case
    using assms
    by (intro symmetric_adjacency.invar invar_difference)
next
  case (2 v u)
  have
    "v \<in> set (adjacency_list (difference G1 G2) u) \<longleftrightarrow>
     v \<in> set (adjacency_list G1 u) - set (adjacency_list G2 u)"
    using assms
    by (fastforce simp add: adjacency_difference_cong dest: symmetric_adjacency.invar)
  also have "... \<longleftrightarrow> u \<in> set (adjacency_list G1 v) - set (adjacency_list G2 v)"
    using assms
    by (simp add: symmetric_adjacency.symmetric)
  also have "... \<longleftrightarrow> u \<in> set (adjacency_list (difference G1 G2) v)"
    using assms
    by (fastforce simp add: adjacency_difference_cong dest: symmetric_adjacency.invar)
  finally show ?case
    .
qed

lemma (in adjacency) E_difference_cong:
  assumes "symmetric_adjacency' G1"
  assumes "symmetric_adjacency' G2"
  shows "E (difference G1 G2) = E G1 - E G2"
proof -
  { fix u v
    have "{u, v} \<in> E (difference G1 G2) \<longleftrightarrow> v \<in> set (adjacency_list (difference G1 G2) u)"
      using assms
      by
        (intro symmetric_adjacency.mem_adjacency_iff_edge[symmetric])
        (auto intro: symmetric_adjacency_difference)
    also have "... \<longleftrightarrow> v \<in> set (adjacency_list G1 u) - set (adjacency_list G2 u)"
      using assms
      by (fastforce simp add: adjacency_difference_cong dest: symmetric_adjacency.invar)
    also have "... \<longleftrightarrow> {u, v} \<in> E G1 - E G2"
      using assms
      by (simp add: symmetric_adjacency.mem_adjacency_iff_edge)
    finally have "{u, v} \<in> E (difference G1 G2) \<longleftrightarrow> {u, v} \<in> E G1 - E G2"
      . }
  thus ?thesis
    by (intro graphs_eqI) (auto simp add: E_def graph_def)
qed

lemma (in adjacency) finite_V_difference:
  assumes "invar G1"
  assumes "invar G2"
  shows "finite (V (difference G1 G2))"
  using assms
  by (intro invar_difference finite_V)

end
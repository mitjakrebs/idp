theory Path
  imports
    Graph_Ext
    "../../Misc_Ext"
begin

text \<open>
A path (@{term path} and @{term walk_betw}) is a sequence $v_0,\dots,v_k$ of vertices such that
${v_{i-1},v_i}$ is an edge for every $i=1,\dots,k$.
\<close>

type_synonym 'a path = "'a list"

lemma \<^marker>\<open>tag invisible\<close> path_snocD:
  assumes "path G (p @ [u, v])"
  shows "{u, v} \<in> G"
  using assms
  by (auto dest: path_suff)

lemma \<^marker>\<open>tag invisible\<close> path_butlastI:
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

lemma \<^marker>\<open>tag invisible\<close> pathD_2:
  assumes "path G p"
  assumes "Suc i < length p"
  shows "{p ! i, p ! (Suc i)} \<in> G"
  using assms
proof (induct p arbitrary: i rule: edges_of_path.induct)
  case 3
  thus ?case
    by (auto simp add: less_Suc_eq_0_disj)
qed simp_all

lemma \<^marker>\<open>tag invisible\<close> edges_of_path_tl:
  shows "edges_of_path (tl p) = tl (edges_of_path p)"
  by (induct p rule: edges_of_path.induct) simp+

lemma \<^marker>\<open>tag invisible\<close> edges_of_path_butlast:
  shows "edges_of_path (butlast p) = butlast (edges_of_path p)"
  by (induct p rule: edges_of_path.induct) (auto elim: edges_of_path.elims)

lemma \<^marker>\<open>tag invisible\<close> edges_of_path_append_4:
  assumes "p \<noteq> []"
  assumes "q \<noteq> []"
  assumes "last p = hd q"
  shows "edges_of_path (p @ tl q) = edges_of_path p @ edges_of_path q"
  using assms
  by (simp add: edges_of_path_append_3)

lemma walk_betw_induct [consumes 1]:
  assumes "walk_betw G u p v"
  assumes "\<And>v. P [v]"
  assumes "\<And>u v vs. P (v # vs) \<Longrightarrow> P (u # v # vs)"
  shows "P p"
  using assms
  by (auto intro: induct_walk_betw)

lemma walk_betw_induct_2 [consumes 1]:
  assumes "walk_betw G u p v"
  assumes "P [v]"
  assumes "\<And>u. P [u, v]"
  assumes "\<And>u x xs. P (x # xs @ [v]) \<Longrightarrow> P (u # x # xs @ [v])"
  shows "P p"
  using assms
proof (induct arbitrary: u rule: walk_betw_induct[OF assms(1)])
  case 1
  thus ?case
    by (auto dest: walk_between_nonempty_path(3, 4))
next
  case (2 x y ys)
  show ?case
  proof (cases "ys = []")
    case True
    thus ?thesis
      using "2.prems"(1, 3)
      by (auto dest: walk_between_nonempty_path(4))
  next
    case False
    have "walk_betw G y (y # ys) v"
      using "2.prems"(1)
      by (auto intro: walk_suff[where ?pr = "[x]"])
    hence "P (y # ys)"
      using "2.prems"(2-4)
      by (intro "2.hyps")
    moreover have "ys = butlast ys @ [v]"
      using False "2.prems"(1)
      by (fastforce dest: walk_between_nonempty_path(4) intro: append_butlast_last_id)
    ultimately show ?thesis
      by (metis "2.prems"(4))
  qed
qed

lemma \<^marker>\<open>tag invisible\<close> walk_betwD:
  assumes "walk_betw G u p v"
  shows
    "u # tl p = p"
    "butlast p @ [v] = p"
proof (goal_cases)
  case 1
  show ?case
    using assms
    unfolding walk_between_nonempty_path(3)[OF assms, symmetric]
    by (intro walk_between_nonempty_path(2) hd_Cons_tl)
next
  case 2
  show ?case
    using assms
    unfolding walk_between_nonempty_path(4)[OF assms, symmetric]
    by (intro walk_between_nonempty_path(2) append_butlast_last_id)
qed

lemma \<^marker>\<open>tag invisible\<close> walk_betw_butlastI:
  assumes "walk_betw G u p v"
  assumes "2 \<le> length p"
  shows "walk_betw G u (butlast p) (last (butlast p))"
proof -
  have butlast_p_non_empty: "butlast p \<noteq> []"
    using assms(2)
    by (intro length_ge_2D(3))
  hence "butlast (butlast p) @ [last (butlast p)] @ [last p] = p"
    unfolding append.assoc[symmetric]
    using assms(1)
    by simp
  hence "walk_betw G u (butlast (butlast p) @ [last (butlast p)]) (last (butlast p))"
    using assms(1)
    by (auto intro: walk_pref[where ?pr = "butlast (butlast p)" and ?x = "last (butlast p)" and ?su = "[last p]"])
  thus ?thesis
    using butlast_p_non_empty
    by simp
qed

lemma \<^marker>\<open>tag invisible\<close> walk_betwD_2:
  assumes "walk_betw G u p v"
  assumes "2 \<le> length p"
  shows "u # tl (butlast p) @ [v] = p"
proof -
  have "u # tl (butlast p) @ [v] = butlast p @ [v]"
    using assms
    by (fastforce dest: walk_betwD(1) walk_betw_butlastI)
  also have "... = p"
    using assms(1)
    by (intro walk_betwD(2))
  finally show ?thesis
    .
qed

lemma \<^marker>\<open>tag invisible\<close> length_ge_2I:
  assumes "walk_betw G u p v"
  assumes "u \<noteq> v"
  shows "2 \<le> length p"
proof -
  { assume "length p < 2"
    hence "length p = 1"
      using assms(1)
      by (auto simp add: less_2_cases_iff dest: walk_nonempty)
    hence
      "p = [u]"
      "p = [v]"
      using assms(1)
      by (auto simp add: length_Suc_conv dest: walk_betwD)
    hence False
      using assms(2)
      by auto }
  thus ?thesis
    by fastforce
qed

lemma \<^marker>\<open>tag invisible\<close> walk_betw_imp_edge:
  assumes "walk_betw G u p w"
  assumes "2 \<le> length p"
  obtains v where
    "{u, v} \<in> G"
  using assms
proof (induct p rule: edges_of_path.induct)
  case 1
  thus ?case
    by (auto dest: walk_nonempty)
next
  case 2
  thus ?case
    using walk_between_nonempty_path(3, 4)
    by fastforce
next
  case 3
  thus ?case
    using walk_between_nonempty_path(3)
    by (fastforce dest: walk_between_nonempty_path(1))
qed

lemma \<^marker>\<open>tag invisible\<close> walk_betw_imp_edge_2:
  assumes "walk_betw G u p w"
  assumes "2 \<le> length p"
  obtains v where
    "{w, v} \<in> G"
proof -
  have "walk_betw G w (rev p) u"
    using assms(1)
    by (intro walk_symmetric)
  thus ?thesis
    using assms(2)
    by (auto elim: walk_betw_imp_edge intro: that)
qed

text \<open>We can concatenate paths.\<close>

lemma walk_betw_appendI:
  assumes "walk_betw G u p v"
  assumes "walk_betw G v p' w"
  shows "walk_betw G u ((butlast p @ [v]) @ tl p') w"
  using assms
  by (auto simp add: walk_betwD(2) intro: walk_transitive)
  
lemma \<^marker>\<open>tag invisible\<close> walk_betw_ConsI:
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

lemma \<^marker>\<open>tag invisible\<close> walk_betw_snocI:
  assumes "walk_betw G u p v"
  assumes "{v, w} \<in> G"
  shows "walk_betw G u (p @ [w]) w"
  using assms walk_transitive[where ?p = p and ?v = v and ?q = "[v, w]"]
  by (auto intro: edges_are_walks)

lemma \<^marker>\<open>tag invisible\<close> walk_betw_transitive_2:
  assumes "walk_betw G u p v"
  assumes "walk_betw G v q w"
  shows "walk_betw G u (butlast p @ q) w"
  using assms
  by (auto dest: walk_between_nonempty_path(2) simp add: walk_between_nonempty_path(3, 4) butlast_tl_conv intro: walk_transitive)

lemma edges_of_path_append:
  assumes "walk_betw G u p v"
  assumes "walk_betw G v p' w"
  shows "edges_of_path ((butlast p @ [v]) @ tl p') = edges_of_path p @ edges_of_path p'"
  using assms
  by (auto simp add: walk_betwD(2) dest: walk_between_nonempty_path(2-4) intro: edges_of_path_append_4)

lemma \<^marker>\<open>tag invisible\<close> edges_of_path_Cons:
  assumes "walk_betw G v p w"
  assumes "{u, v} \<in> G"
  shows "edges_of_path (u # p) = {u, v} # edges_of_path p"
  using assms edges_of_path_append[where ?p = "[u, v]" and ?v = v and ?p' = p]
  by (auto simp add: walk_betwD(1) intro: edges_are_walks)

lemma \<^marker>\<open>tag invisible\<close> edges_of_path_snoc:
  assumes "walk_betw G u p v"
  assumes "{v, w} \<in> G"
  shows "edges_of_path (p @ [w]) = edges_of_path p @ [{v, w}]"
  using assms edges_of_path_append[where ?p = p and ?v = v and ?p' = "[v, w]"]
  by (auto simp add: walk_betwD(2) intro: edges_are_walks)

lemma \<^marker>\<open>tag invisible\<close> set_edges_of_path_subset_append:
  shows "set (edges_of_path p) \<subseteq> set (edges_of_path (p @ p'))"
  by (induct p rule: edges_of_path.induct) auto

lemma walk_betw_Cons_snocI:
  assumes "walk_betw G v p x"
  assumes "{u, v} \<in> G"
  assumes "{x, y} \<in> G"
  shows
    "walk_betw G u (u # p @ [y]) y"
    "{u, v} \<in> set (edges_of_path (u # p @ [y]))"
    "{x, y} \<in> set (edges_of_path (u # p @ [y]))"
proof -
  have walk_betw_Cons: "walk_betw G u (u # p) x \<and> {u, v} \<in> set (edges_of_path (u # p))"
    using assms(1, 2)
    by (auto simp add: edges_of_path_Cons insert_commute intro: walk_betw_ConsI)
  thus "walk_betw G u (u # p @ [y]) y"
    using assms(3)
    by (fastforce dest: walk_betw_snocI)
  show "{u, v} \<in> set (edges_of_path (u # p @ [y]))"
    using walk_betw_Cons set_edges_of_path_subset_append
    by fastforce
  show "{x, y} \<in> set (edges_of_path (u # p @ [y]))"
    using walk_betw_Cons assms(3)
    by (fastforce simp add: edges_of_path_snoc[where ?p = "u # p" and ?v = x, unfolded append_Cons])
qed

lemma \<^marker>\<open>tag invisible\<close> walk_betw_in_set_edges_of_path:
  assumes "walk_betw G u p v"
  assumes "2 \<le> length p"
  shows "walk_betw (set (edges_of_path p)) u p v"
proof -
  obtain p' where
    "u # p' @ [v] = p"
    using assms
    by (blast intro: walk_betwD_2)
  thus ?thesis
  proof (induct p' arbitrary: u p)
    case Nil
    thus ?case
      by (auto intro: edges_are_walks)
  next
    case (Cons x xs)
    hence "walk_betw (set (edges_of_path (u # x # xs @ [v]))) x (x # xs @ [v]) v"
      by (fastforce intro: walk_subset)
    thus ?case
      by (auto simp add: Cons.prems[symmetric] intro: walk_betw_ConsI)
  qed
qed

lemma \<^marker>\<open>tag invisible\<close> set_edges_of_path_subset:
  assumes "walk_betw G u p v"
  shows "set (edges_of_path p) \<subseteq> G"
  using assms
  by (intro walk_between_nonempty_path(1) path_edges_subset)

text \<open>And we can split paths.\<close>

fun is_path_vertex_decomp :: "'a graph \<Rightarrow> 'a path \<Rightarrow> 'a \<Rightarrow> 'a path \<times> 'a path \<Rightarrow> bool" where
  "is_path_vertex_decomp G p v (q, r) \<longleftrightarrow> p = q @ tl r \<and> (\<exists>u w. walk_betw G u q v \<and> walk_betw G v r w)"

definition path_vertex_decomp :: "'a graph \<Rightarrow> 'a path \<Rightarrow> 'a \<Rightarrow> 'a path \<times> 'a path" where
  "path_vertex_decomp G p v \<equiv> SOME qr. is_path_vertex_decomp G p v qr"

abbreviation closed_path :: "'a graph \<Rightarrow> 'a path \<Rightarrow> 'a \<Rightarrow> bool" where
  "closed_path G c v \<equiv> walk_betw G v c v \<and> Suc 0 < length c"

fun is_closed_path_decomp :: "'a graph \<Rightarrow> 'a path \<Rightarrow> 'a path \<times> 'a path \<times> 'a path \<Rightarrow> bool" where
  "is_closed_path_decomp G p (q, r, s) \<longleftrightarrow>
   p = q @ tl r @ tl s \<and>
   (\<exists>u v w. walk_betw G u q v \<and> closed_path G r v \<and> walk_betw G v s w) \<and>
   distinct q"

definition closed_path_decomp :: "'a graph \<Rightarrow> 'a path \<Rightarrow> 'a path \<times> 'a path \<times> 'a path" where
  "closed_path_decomp G p \<equiv> SOME qrs. is_closed_path_decomp G p qrs"

definition distinct_path :: "'a graph \<Rightarrow> 'a path \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "distinct_path G p u v \<equiv> walk_betw G u p v \<and> distinct p"

text \<open>A simple path (@{term distinct_path}) is a path in which all vertices are distinct.\<close>

lemma \<^marker>\<open>tag invisible\<close> distinct_pathD:
  assumes "distinct_path G p u v"
  shows
    "walk_betw G u p v"
    "distinct p"
  using assms
  by (simp_all add: distinct_path_def)

lemma \<^marker>\<open>tag invisible\<close> distinct_pathI:
  assumes "walk_betw G u p v"
  assumes "distinct p"
  shows "distinct_path G p u v"
  using assms
  by (simp add: distinct_path_def)

text \<open>A vertex $v$ is reachable from a vertex $u$ if and only if there is a path from $u$ to $v$.\<close>

definition reachable :: "'a graph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "reachable G u v \<equiv> \<exists>p. walk_betw G u p v"

text \<open>The length of a @{type path} is the number of its edges.\<close>

abbreviation path_length :: "'a path \<Rightarrow> nat" where
  "path_length p \<equiv> length (edges_of_path p)"

end
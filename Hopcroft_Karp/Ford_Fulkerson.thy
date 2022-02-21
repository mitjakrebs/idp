theory Ford_Fulkerson
  imports
    "../BFS/Alternating_BFS"
    "../Graph_Theory/Undirected_Graphs/Augmenting_Path"
    "../Graph_Theory/Undirected_Graphs/Bipartite_Graph"
begin

locale ford_fulkerson =
  alt_bfs where
  Map_update = Map_update and
  P_update = P_update and
  Q_snoc = Q_snoc +
  M: Map_by_Ordered where
  empty = M_empty and
  update = M_update and
  delete = M_delete and
  lookup = M_lookup and
  inorder = M_inorder and
  inv = M_inv for
  Map_update :: "'a::linorder \<Rightarrow> 's \<Rightarrow> 'n \<Rightarrow> 'n" and
  P_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  Q_snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" and
  M_empty and
  M_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  M_delete and
  M_lookup and
  M_inorder and
  M_inv
begin

section \<open>Algorithm\<close>

definition free :: "'m \<Rightarrow> 'a \<Rightarrow> bool" where
  "free M v \<equiv> M_lookup M v = None"

definition free_vertices :: "'s \<Rightarrow> 'm \<Rightarrow> 'a list" where
  "free_vertices V M \<equiv> filter (free M) (Set_inorder V)"

definition f :: "'a \<times> 'a \<Rightarrow> 'n \<Rightarrow> 'n" where
  "f p G \<equiv>
   let u = fst p; v = snd p
   in case Map_lookup G u of
        None \<Rightarrow> Map_update u (Set_insert v Set_empty) G |
        Some s \<Rightarrow> Map_update u (Set_insert v s) G"

definition g :: "'a \<Rightarrow> 'a \<Rightarrow> 'n \<Rightarrow> 'n" where
  "g \<equiv> curry f"

definition h :: "'a \<Rightarrow> 'a \<Rightarrow> 'n \<Rightarrow> 'n" where
  "h v u \<equiv> g u v"

definition G2_1 :: "'m \<Rightarrow> 'n" where
  "G2_1 M \<equiv> List.fold f (M_inorder M) Map_empty"

definition G2_2 :: "'s \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'n" where
  "G2_2 U s M \<equiv> List.fold (g s) (free_vertices U M) (G2_1 M)"

definition G2_3 :: "'s \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'n" where
  "G2_3 U s M \<equiv> List.fold (h s) (free_vertices U M) (G2_2 U s M)"

definition G2_4 :: "'s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'n" where
  "G2_4 U V s t M \<equiv> List.fold (g t) (free_vertices V M) (G2_3 U s M)"

definition G2_5 :: "'s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'n" where
  "G2_5 U V s t M \<equiv> List.fold (h t) (free_vertices V M) (G2_4 U V s t M)"

abbreviation G2 :: "'s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'n" where
  "G2 \<equiv> G2_5"

abbreviation G1 :: "'n \<Rightarrow> 'n \<Rightarrow> 'n" where
  "G1 \<equiv> G.difference"

definition done_1 :: "'s \<Rightarrow> 's \<Rightarrow> 'm \<Rightarrow> bool" where
  "done_1 U V M \<equiv> free_vertices U M = [] \<or> free_vertices V M = []"

definition done_2 :: "'a \<Rightarrow> 'm \<Rightarrow> bool" where
  "done_2 t m \<equiv> P_lookup m t = None"

fun augment :: "'m \<Rightarrow> 'a path \<Rightarrow> 'm" where
  "augment M [] = M" |
  "augment M [u, v] = (M_update v u (M_update u v M))" |
  "augment M (u # v # w # ws) = augment (M_update v u (M_update u v (M_delete w M))) (w # ws)"

(* Should G1 be defined independently of G2? *)
(*
function (domintros) loop' where
  "loop' G U V s t M =
   (if done_1 U V M then M
    else let G2 = G2 U V s t M
         in let G1 = G1 G G2
            in let m = alt_bfs G1 G2 s
               in if done_2 t m then M else loop' G U V s t (augment M (butlast (tl (rev_follow m t)))))"
  by pat_completeness simp
*)

function (domintros) loop' where
  "loop' G U V s t M =
   (if done_1 U V M then M
    else if done_2 t (alt_bfs (G1 G (G2 U V s t M)) (G2 U V s t M) s) then M
         else loop' G U V s t (augment M (butlast (tl (rev_follow (alt_bfs (G1 G (G2 U V s t M)) (G2 U V s t M) s) t)))))"
  by pat_completeness simp

abbreviation ford_fulkerson :: "'n \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'm" where
  "ford_fulkerson G U V s t \<equiv> loop' G U V s t M_empty"

(* Take G1 G2 s as input? *)
abbreviation m_tbd :: "'n \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" where
  "m_tbd G U V s t M \<equiv> let G2 = G2 U V s t M in alt_bfs (G1 G G2) G2 s"

(* Take t m as input? *)
abbreviation p_tbd :: "'n \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'a path" where
  "p_tbd G U V s t M \<equiv> butlast (tl (rev_follow (m_tbd G U V s t M) t))"

abbreviation M_tbd :: "'m \<Rightarrow> 'a graph" where
  "M_tbd M \<equiv> {{u, v} |u v. M_lookup M u = Some v}"

abbreviation P_tbd :: "'a path \<Rightarrow> 'a graph" where
  "P_tbd p \<equiv> set (edges_of_path p)"

abbreviation symmetric_Map :: "'m \<Rightarrow> bool" where
  "symmetric_Map M \<equiv> \<forall>u v. M_lookup M u = Some v \<longleftrightarrow> M_lookup M v = Some u"

(**)
thm matching_def
thm symmetric_diff_def
thm augmenting_path_def
term augpath
term graph_matching
term Berge.alt_path

section \<open>Convenience Lemmas\<close>

subsection \<open>@{term free_vertices}\<close>

lemma mem_set_free_verticesI:
  assumes "v \<in> G.S.set V"
  assumes "free M v"
  shows "v \<in> set (free_vertices V M)"
  using assms
  by (simp add: free_vertices_def G.S.set_def)

lemma set_free_vertices_subset:
  shows "set (free_vertices V M) \<subseteq> G.S.set V"
  by (simp add: free_vertices_def G.S.set_def)

subsection \<open>@{term f}\<close>

lemma invar_f:
  assumes "G.invar G"
  shows "G.invar (f p G)"
proof (cases "Map_lookup G (fst p)")
  case None
  thus ?thesis
    using assms G.S.invar_empty
    by (auto simp add: f_def intro: G.S.invar_insert G.invar_update)
next
  case (Some s)
  hence "G.S.invar s"
    using assms(1)
    by (auto simp add: G.invar_def G.M.ran_def)
  thus ?thesis
    using assms(1)
    by (auto simp add: f_def Some intro: G.S.invar_insert G.invar_update)
qed

lemma f_cong:
  assumes "G.invar G"
  shows "set (G.adjacency (f p G) v) = set (G.adjacency G v) \<union> (if v = fst p then {snd p} else {})"
proof (cases "Map_lookup G (fst p)")
  case None
  let ?singleton = "Set_insert (snd p) Set_empty"
  { fix u
    have "u \<in> set (G.adjacency (f p G) v) \<longleftrightarrow> u \<in> set (G.adjacency (Map_update (fst p) ?singleton G) v)"
      by (simp add: f_def None)
    also have "... \<longleftrightarrow> (\<exists>s. Map_lookup (Map_update (fst p) ?singleton G) v = Some s \<and> u \<in> G.S.set s)"
      by (simp add: G.mem_adjacency_iff)
    also have "... \<longleftrightarrow> (\<exists>s. (Map_lookup G(fst p \<mapsto> ?singleton)) v = Some s \<and> u \<in> G.S.set s)"
      using assms(1)
      by (auto simp add: G.M.map_update dest: G.invarD(1))
    also have "... \<longleftrightarrow> u \<in> set (G.adjacency G v) \<union> (if v = fst p then {snd p} else {})"
      using G.S.invar_empty
      by (simp add: None G.mem_adjacency_iff G.S.set_insert G.S.set_empty)
    finally have
      "u \<in> set (G.adjacency (f p G) v) \<longleftrightarrow>
       u \<in> set (G.adjacency G v) \<union> (if v = fst p then {snd p} else {})"
      . }
  thus ?thesis
    by blast
next
  case (Some s)
  hence invar: "G.S.invar s"
    using assms(1)
    by (auto simp add: G.invar_def G.M.ran_def)
  let ?insert = "Set_insert (snd p) s"
  { fix u
    have "u \<in> set (G.adjacency (f p G) v) \<longleftrightarrow> u \<in> set (G.adjacency (Map_update (fst p) ?insert G) v)"
      by (simp add: f_def Some)
    also have "... \<longleftrightarrow> (\<exists>s. Map_lookup (Map_update (fst p) ?insert G) v = Some s \<and> u \<in> G.S.set s)"
      by (simp add: G.mem_adjacency_iff)
    also have "... \<longleftrightarrow> (\<exists>s. (Map_lookup G(fst p \<mapsto> ?insert)) v = Some s \<and> u \<in> G.S.set s)"
      using assms(1)
      by (auto simp add: G.M.map_update dest: G.invarD(1))
    also have "... \<longleftrightarrow> u \<in> set (G.adjacency G v) \<union> (if v = fst p then {snd p} else {})"
      using invar
      by (auto simp add: Some G.mem_adjacency_iff G.S.set_insert)
    finally have
      "u \<in> set (G.adjacency (f p G) v) \<longleftrightarrow>
       u \<in> set (G.adjacency G v) \<union> (if v = fst p then {snd p} else {})"
      . }
  thus ?thesis
    by blast
qed

subsection \<open>@{term g}\<close>

lemma invar_g:
  assumes "G.invar G"
  shows "G.invar (g u v G)"
  using assms
  by (auto simp add: g_def intro: invar_f)

lemma g_cong:
  assumes "G.invar G"
  shows "set (G.adjacency (g u v G) w) = set (G.adjacency G w) \<union> (if w = u then {v} else {})"
  using assms
  by (simp add: g_def f_cong)

subsection \<open>@{term h}\<close>

lemma invar_h:
  assumes "G.invar G"
  shows "G.invar (h v u G)"
  using assms
  by (auto simp add: h_def intro: invar_g)

lemma h_cong:
  assumes "G.invar G"
  shows "set (G.adjacency (h v u G) w) = set (G.adjacency G w) \<union> (if w = u then {v} else {})"
  using assms
  by (simp add: h_def g_cong)

subsection \<open>@{term "List.fold f"}\<close>

lemma invar_fold_f:
  assumes "G.invar G"
  shows "G.invar (List.fold f l G)"
  using assms
proof (induct l arbitrary: G)
  case Nil
  thus ?case
    by simp
next
  case Cons
  thus ?case
    by (auto intro: invar_f Cons.hyps)
qed

lemma fold_f_cong:
  assumes "G.invar G"
  shows
    "set (G.adjacency (List.fold f l G) v) =
     set (G.adjacency G v) \<union> (\<Union>p\<in>set l. if v = fst p then {snd p} else {})"
  using assms
proof (induct l arbitrary: G)
  case Nil
  thus ?case
    by simp
next
  case (Cons p ps)
  have "set (G.adjacency (List.fold f (p # ps) G) v) = set (G.adjacency (List.fold f ps (f p G)) v)"
    by simp
  also have "... = set (G.adjacency (f p G) v) \<union> (\<Union>p\<in>set ps. if v = fst p then {snd p} else {})"
    using Cons.prems
    by (intro invar_f Cons.hyps)
  also have
    "... =
     set (G.adjacency G v) \<union>
     (if v = fst p then {snd p} else {}) \<union>
     (\<Union>p\<in>set ps. if v = fst p then {snd p} else {})"
    using Cons.prems
    by (simp add: f_cong)
  also have "... = set (G.adjacency G v) \<union> (\<Union>p\<in>set (p # ps). if v = fst p then {snd p} else {})"
    by force
  finally show ?case
    .
qed

subsection \<open>@{term "List.fold (g u)"}\<close>

lemma invar_fold_g:
  assumes "G.invar G"
  shows "G.invar (List.fold (g u) l G)"
  using assms
proof (induct l arbitrary: G)
  case Nil
  thus ?case
    by simp
next
  case Cons
  thus ?case
    by (auto intro: invar_g Cons.hyps)
qed

lemma fold_g_cong:
  assumes "G.invar G"
  shows
    "set (G.adjacency (List.fold (g u) l G) v) =
     set (G.adjacency G v) \<union> (\<Union>w\<in>set l. if v = u then {w} else {})"
  using assms
proof (induct l arbitrary: G)
  case Nil
  thus ?case
    by simp
next
  case (Cons w ws)
  have
    "set (G.adjacency (List.fold (g u) (w # ws) G) v) =
     set (G.adjacency (List.fold (g u) ws (g u w G)) v)"
    by simp
  also have "... = set (G.adjacency (g u w G) v) \<union> (\<Union>x\<in>set ws. if v = u then {x} else {})"
    using Cons.prems
    by (intro invar_g Cons.hyps)
  also have
    "... =
     set (G.adjacency G v) \<union>
     (if v = u then {w} else {}) \<union>
     (\<Union>x\<in>set ws. if v = u then {x} else {})"
    using Cons.prems
    by (simp add: g_cong)
  also have "... = set (G.adjacency G v) \<union> (\<Union>x\<in>set (w # ws). if v = u then {x} else {})"
    by force
  finally show ?case
    .
qed

subsection \<open>@{term "List.fold (h u)"}\<close>

lemma invar_fold_h:
  assumes "G.invar G"
  shows "G.invar (List.fold (h u) l G)"
  using assms
proof (induct l arbitrary: G)
  case Nil
  thus ?case
    by simp
next
  case Cons
  thus ?case
    by (auto intro: invar_h Cons.hyps)
qed

lemma fold_h_cong:
  assumes "G.invar G"
  shows
    "set (G.adjacency (List.fold (h u) l G) v) =
     set (G.adjacency G v) \<union> (\<Union>w\<in>set l. if v = w then {u} else {})"
  using assms
proof (induct l arbitrary: G)
  case Nil
  thus ?case
    by simp
next
  case (Cons w ws)
  have
    "set (G.adjacency (List.fold (h u) (w # ws) G) v) =
     set (G.adjacency (List.fold (h u) ws (h u w G)) v)"
    by simp
  also have "... = set (G.adjacency (h u w G) v) \<union> (\<Union>x\<in>set ws. if v = x then {u} else {})"
    using Cons.prems
    by (intro invar_h Cons.hyps)
  also have
    "... =
     set (G.adjacency G v) \<union>
     (if v = w then {u} else {}) \<union>
     (\<Union>x\<in>set ws. if v = x then {u} else {})"
    using Cons.prems
    by (simp add: h_cong)
  also have "... = set (G.adjacency G v) \<union> (\<Union>x\<in>set (w # ws). if v = x then {u} else {})"
    by force
  finally show ?case
    .
qed

subsection \<open>@{term G2_1}\<close>

lemma invar_G2_1:
  shows "G.invar (G2_1 M)"
  using G.invar_empty
  by (auto simp add: G2_1_def intro: invar_fold_f)

lemma adjacency_G2_1_cong:
  assumes "M.invar M"
  shows "set (G.adjacency (G2_1 M) u) = (case M_lookup M u of None \<Rightarrow> {} | Some v \<Rightarrow> {v})"
proof -
  { fix v
    have
      "v \<in> set (G.adjacency (G2_1 M) u) \<longleftrightarrow>
       v \<in> set (G.adjacency Map_empty u) \<union> (\<Union>p\<in>set (M_inorder M). if u = fst p then {snd p} else {})"
      using G.invar_empty
      by (simp add: G2_1_def fold_f_cong)
    also have "... \<longleftrightarrow> v \<in> (\<Union>p\<in>set (M_inorder M). if u = fst p then {snd p} else {})"
      by (simp add: G.adjacency_def G.M.map_empty)
    also have "... \<longleftrightarrow> (\<exists>p\<in>set (M_inorder M). u = fst p \<and> v = snd p)"
      by auto
    also have "... \<longleftrightarrow> (u, v) \<in> set (M_inorder M)"
      by (metis prod.collapse fst_conv snd_conv)
    also have "... \<longleftrightarrow> M_lookup M u = Some v"
      using assms
      by (simp add: M.mem_inorder_iff_lookup_eq_Some)
    finally have "v \<in> set (G.adjacency (G2_1 M) u) \<longleftrightarrow> M_lookup M u = Some v"
      . }
  thus ?thesis
    by (force split: option.splits(2))
qed

lemma E2_1_cong:
  assumes "M.invar M"
  shows "G.E (G2_1 M) = M_tbd M"
proof -
  { fix u v
    have "{u, v} \<in> G.E (G2_1 M) \<longleftrightarrow> u \<in> set (G.adjacency (G2_1 M) v) \<or> v \<in> set (G.adjacency (G2_1 M) u)"
      by (auto simp add: G.E_def doubleton_eq_iff)
    also have "... \<longleftrightarrow> M_lookup M v = Some u \<or> M_lookup M u = Some v"
      using assms
      by (auto simp add: adjacency_G2_1_cong split: option.split)
    also have "... \<longleftrightarrow> {u, v} \<in> M_tbd M"
      by (auto simp add: doubleton_eq_iff)
    finally have "{u, v} \<in> G.E (G2_1 M) \<longleftrightarrow> {u, v} \<in> M_tbd M"
      . }
  thus ?thesis
    by (fastforce simp add: G.E_def doubleton_eq_iff)
qed

lemma symmetric_adjacency_G2_1:
  assumes "M.invar M"
  assumes "symmetric_Map M"
  shows "G.symmetric_adjacency' (G2_1 M)"
proof (standard, goal_cases)
  case 1
  show ?case
    using invar_G2_1
    .
next
  case 2
  show ?case
    using assms
    by (fastforce simp add: adjacency_G2_1_cong split: option.splits(2))
qed

subsection \<open>@{term G2_2}\<close>

lemma invar_G2_2:
  shows "G.invar (G2_2 U s M)"
  using invar_G2_1
  by (auto simp add: G2_2_def intro: invar_fold_g)

lemma adjacency_G2_2_cong:
  shows
    "set (G.adjacency (G2_2 U s M) u) =
     set (G.adjacency (G2_1 M) u) \<union> (\<Union>v\<in>set (free_vertices U M). if u = s then {v} else {})"
  using invar_G2_1
  by (simp add: G2_2_def fold_g_cong)

lemma E2_2_cong:
  shows "G.E (G2_2 U s M) = G.E (G2_1 M) \<union> {{s, v} |v. v \<in> set (free_vertices U M)}"
proof -
  { fix u v
    have
      "{u, v} \<in> G.E (G2_2 U s M) \<longleftrightarrow>
       u \<in> set (G.adjacency (G2_2 U s M) v) \<or> v \<in> set (G.adjacency (G2_2 U s M) u)"
      by (auto simp add: G.E_def doubleton_eq_iff)
    also have
      "... \<longleftrightarrow>
       u \<in> set (G.adjacency (G2_1 M) v) \<or> (v = s \<and> u \<in> set (free_vertices U M)) \<or>
       v \<in> set (G.adjacency (G2_1 M) u) \<or> (u = s \<and> v \<in> set (free_vertices U M))"
      by (simp add: adjacency_G2_2_cong)
    also have "... \<longleftrightarrow> {u, v} \<in> (G.E (G2_1 M) \<union> {{s, v} |v. v \<in> set (free_vertices U M)})"
      by (auto simp add: G.E_def doubleton_eq_iff)
    finally have "{u, v} \<in> G.E (G2_2 U s M) \<longleftrightarrow> {u, v} \<in> G.E (G2_1 M) \<union> {{s, v} |v. v \<in> set (free_vertices U M)}"
      . }
  thus ?thesis
    by (intro eqI) (auto simp add: G.E_def graph_def)
qed

subsection \<open>@{term G2_3}\<close>

lemma invar_G2_3:
  shows "G.invar (G2_3 U s M)"
  using invar_G2_2
  by (auto simp add: G2_3_def intro: invar_fold_h)

lemma adjacency_G2_3_cong:
  shows
    "set (G.adjacency (G2_3 U s M) u) =
     set (G.adjacency (G2_2 U s M) u) \<union> (\<Union>v\<in>set (free_vertices U M). if u = v then {s} else {})"
  using invar_G2_2
  by (simp add: G2_3_def fold_h_cong)

lemma adjacency_G2_3_G2_1_cong:
  shows
    "set (G.adjacency (G2_3 U s M) u) =
     set (G.adjacency (G2_1 M) u) \<union>
     (\<Union>v\<in>set (free_vertices U M). if u = s then {v} else if u = v then {s} else {})"
  by (auto simp add: adjacency_G2_3_cong adjacency_G2_2_cong)

lemma E2_3_cong:
  shows "G.E (G2_3 U s M) = G.E (G2_2 U s M) \<union> {{v, s} |v. v \<in> set (free_vertices U M)}"
proof -
  { fix u v
    have
      "{u, v} \<in> G.E (G2_3 U s M) \<longleftrightarrow>
       u \<in> set (G.adjacency (G2_3 U s M) v) \<or> v \<in> set (G.adjacency (G2_3 U s M) u)"
      by (auto simp add: G.E_def doubleton_eq_iff)
    also have
      "... \<longleftrightarrow>
       u \<in> set (G.adjacency (G2_2 U s M) v) \<or> (u = s \<and> v \<in> set (free_vertices U M)) \<or>
       v \<in> set (G.adjacency (G2_2 U s M) u) \<or> (v = s \<and> u \<in> set (free_vertices U M))"
      by (simp add: adjacency_G2_3_cong)
    also have "... \<longleftrightarrow> {u, v} \<in> (G.E (G2_2 U s M) \<union> {{v, s} |v. v \<in> set (free_vertices U M)})"
      by (auto simp add: G.E_def doubleton_eq_iff)
    finally have "{u, v} \<in> G.E (G2_3 U s M) \<longleftrightarrow> {u, v} \<in> G.E (G2_2 U s M) \<union> {{v, s} |v. v \<in> set (free_vertices U M)}"
      . }
  thus ?thesis
    by (intro eqI) (auto simp add: G.E_def graph_def)
qed

lemma symmetric_adjacency_G2_3:
  assumes "M.invar M"
  assumes "symmetric_Map M"
  shows "G.symmetric_adjacency' (G2_3 U s M)"
proof (standard, goal_cases)
  case 1
  show ?case
    using invar_G2_3
    .
next
  case (2 v u)
  have
    "v \<in> set (G.adjacency (G2_3 U s M) u) \<longleftrightarrow>
     v \<in> set (G.adjacency (G2_1 M) u) \<or>
     (v \<in> set (free_vertices U M) \<and> u = s) \<or>
     (u \<in> set (free_vertices U M) \<and> v = s)"
    by (auto simp add: adjacency_G2_3_G2_1_cong)
  also have
    "... \<longleftrightarrow>
     u \<in> set (G.adjacency (G2_1 M) v) \<or>
     (v \<in> set (free_vertices U M) \<and> u = s) \<or>
     (u \<in> set (free_vertices U M) \<and> v = s)"
    using assms
    by (simp add: symmetric_adjacency.symmetric[OF symmetric_adjacency_G2_1])
  also have "... \<longleftrightarrow> u \<in> set (G.adjacency (G2_3 U s M) v)"
    by (auto simp add: adjacency_G2_3_G2_1_cong)
  finally show ?case
    .
qed

subsection \<open>@{term G2_4}\<close>

lemma invar_G2_4:
  shows "G.invar (G2_4 U V s t M)"
  using invar_G2_3
  by (auto simp add: G2_4_def intro: invar_fold_g)

lemma adjacency_G2_4_cong:
  shows
    "set (G.adjacency (G2_4 U V s t M) u) =
     set (G.adjacency (G2_3 U s M) u) \<union> (\<Union>v\<in>set (free_vertices V M). if u = t then {v} else {})"
  using invar_G2_3
  by (simp add: G2_4_def fold_g_cong)

lemma E2_4_cong:
  shows "G.E (G2_4 U V s t M) = G.E (G2_3 U s M) \<union> {{t, v} |v. v \<in> set (free_vertices V M)}"
proof -
  { fix u v
    have
      "{u, v} \<in> G.E (G2_4 U V s t M) \<longleftrightarrow>
       u \<in> set (G.adjacency (G2_4 U V s t M) v) \<or> v \<in> set (G.adjacency (G2_4 U V s t M) u)"
      by (auto simp add: G.E_def doubleton_eq_iff)
    also have
      "... \<longleftrightarrow>
       u \<in> set (G.adjacency (G2_3 U s M) v) \<or> (v = t \<and> u \<in> set (free_vertices V M)) \<or>
       v \<in> set (G.adjacency (G2_3 U s M) u) \<or> (u = t \<and> v \<in> set (free_vertices V M))"
      by (simp add: adjacency_G2_4_cong)
    also have "... \<longleftrightarrow> {u, v} \<in> (G.E (G2_3 U s M) \<union> {{t, v} |v. v \<in> set (free_vertices V M)})"
      by (auto simp add: G.E_def doubleton_eq_iff)
    finally have "{u, v} \<in> G.E (G2_4 U V s t M) \<longleftrightarrow> {u, v} \<in> G.E (G2_3 U s M) \<union> {{t, v} |v. v \<in> set (free_vertices V M)}"
      . }
  thus ?thesis
    by (intro eqI) (auto simp add: G.E_def graph_def)
qed

subsection \<open>@{term G2_5}\<close>

lemma invar_G2_5:
  shows "G.invar (G2_5 U V s t M)"
  using invar_G2_4
  by (auto simp add: G2_5_def intro: invar_fold_h)

lemma adjacency_G2_5_cong:
  shows
    "set (G.adjacency (G2_5 U V s t M) u) =
     set (G.adjacency (G2_4 U V s t M) u) \<union> (\<Union>v\<in>set (free_vertices V M). if u = v then {t} else {})"
  using invar_G2_4
  by (simp add: G2_5_def fold_h_cong)

lemma adjacency_G2_5_G2_3_cong:
  shows
    "set (G.adjacency (G2_5 U V s t M) u) =
     set (G.adjacency (G2_3 U s M) u) \<union>
     (\<Union>v\<in>set (free_vertices V M). if u = t then {v} else if u = v then {t} else {})"
  by (auto simp add: adjacency_G2_5_cong adjacency_G2_4_cong)

lemma adjacency_G2_5_G2_1_cong:
  shows
    "set (G.adjacency (G2_5 U V s t M) u) =
     set (G.adjacency (G2_1 M) u) \<union>
     (\<Union>v\<in>set (free_vertices U M). if u = s then {v} else if u = v then {s} else {}) \<union>
     (\<Union>v\<in>set (free_vertices V M). if u = t then {v} else if u = v then {t} else {})"
  by (auto simp add: adjacency_G2_5_G2_3_cong adjacency_G2_3_G2_1_cong)

lemma E2_5_cong:
  shows "G.E (G2_5 U V s t M) = G.E (G2_4 U V s t M) \<union> {{v, t} |v. v \<in> set (free_vertices V M)}"
proof -
  { fix u v
    have
      "{u, v} \<in> G.E (G2_5 U V s t M) \<longleftrightarrow>
       u \<in> set (G.adjacency (G2_5 U V s t M) v) \<or> v \<in> set (G.adjacency (G2_5 U V s t M) u)"
      by (auto simp add: G.E_def doubleton_eq_iff)
    also have
      "... \<longleftrightarrow>
       u \<in> set (G.adjacency (G2_4 U V s t M) v) \<or> (u = t \<and> v \<in> set (free_vertices V M)) \<or>
       v \<in> set (G.adjacency (G2_4 U V s t M) u) \<or> (v = t \<and> u \<in> set (free_vertices V M))"
      by (simp add: adjacency_G2_5_cong)
    also have "... \<longleftrightarrow> {u, v} \<in> (G.E (G2_4 U V s t M) \<union> {{v, t} |v. v \<in> set (free_vertices V M)})"
      by (auto simp add: G.E_def doubleton_eq_iff)
    finally have "{u, v} \<in> G.E (G2_5 U V s t M) \<longleftrightarrow> {u, v} \<in> G.E (G2_4 U V s t M) \<union> {{v, t} |v. v \<in> set (free_vertices V M)}"
      . }
  thus ?thesis
    by (intro eqI) (auto simp add: G.E_def graph_def)
qed

lemma E2_5_E2_4_cong:
  shows "G.E (G2_5 U V s t M) = G.E (G2_4 U V s t M)"
  by (auto simp add: E2_5_cong E2_4_cong)

lemma E2_5_E2_3_cong:
  shows "G.E (G2_5 U V s t M) = G.E (G2_3 U s M) \<union> {{t, v} |v. v \<in> set (free_vertices V M)}"
  by (simp add: E2_5_E2_4_cong E2_4_cong)

lemma E2_5_E2_2_cong:
  shows "G.E (G2_5 U V s t M) = G.E (G2_2 U s M) \<union> {{s, v} |v. v \<in> set (free_vertices U M)} \<union> {{t, v} |v. v \<in> set (free_vertices V M)}"
  by (auto simp add: E2_5_E2_3_cong E2_3_cong)

lemma E2_5_E2_1_cong:
  shows "G.E (G2_5 U V s t M) = G.E (G2_1 M) \<union> {{s, v} |v. v \<in> set (free_vertices U M)} \<union> {{t, v} |v. v \<in> set (free_vertices V M)}"
  by (simp add: E2_5_E2_2_cong E2_2_cong)

lemma E2_5_M_tbd_cong:
  assumes "M.invar M"
  shows "G.E (G2_5 U V s t M) = M_tbd M \<union> {{s, v} |v. v \<in> set (free_vertices U M)} \<union> {{t, v} |v. v \<in> set (free_vertices V M)}"
  using assms
  by (simp add: E2_5_E2_1_cong E2_1_cong)

lemma symmetric_adjacency_G2_5:
  assumes "M.invar M"
  assumes "symmetric_Map M"
  shows "G.symmetric_adjacency' (G2_5 U V s t M)"
proof (standard, goal_cases)
  case 1
  show ?case
    using invar_G2_5
    .
next
  case (2 v u)
  have
    "v \<in> set (G.adjacency (G2_5 U V s t M) u) \<longleftrightarrow>
     v \<in> set (G.adjacency (G2_3 U s M) u) \<or>
     (v \<in> set (free_vertices V M) \<and> u = t) \<or>
     (u \<in> set (free_vertices V M) \<and> v = t)"
    by (auto simp add: adjacency_G2_5_G2_3_cong)
  also have
    "... \<longleftrightarrow>
     u \<in> set (G.adjacency (G2_3 U s M) v) \<or>
     (v \<in> set (free_vertices V M) \<and> u = t) \<or>
     (u \<in> set (free_vertices V M) \<and> v = t)"
    using assms
    by (simp add: symmetric_adjacency.symmetric[OF symmetric_adjacency_G2_3])
  also have "... \<longleftrightarrow> u \<in> set (G.adjacency (G2_5 U V s t M) v)"
    by (auto simp add: adjacency_G2_5_G2_3_cong)
  finally show ?case
    .
qed

subsection \<open>@{term G2}\<close>

lemma invar_G2:
  shows "G.invar (G2 U V s t M)"
  using invar_G2_5
  .

lemma adjacency_G2_cong:
  assumes "M.invar M"
  shows
    "set (G.adjacency (G2 U V s t M) u) =
     (case M_lookup M u of None \<Rightarrow> {} | Some v \<Rightarrow> {v}) \<union>
     (\<Union>v\<in>set (free_vertices U M). if u = s then {v} else if u = v then {s} else {}) \<union>
     (\<Union>v\<in>set (free_vertices V M). if u = t then {v} else if u = v then {t} else {})"
  using assms
  by (simp add: adjacency_G2_5_G2_1_cong adjacency_G2_1_cong)

lemma adjacency_G2_s_cong:
  assumes "s \<notin> G.S.set V"
  assumes "s \<noteq> t"
  assumes "M.invar M"
  assumes "M_lookup M s = None"
  shows "set (G.adjacency (G2 U V s t M) s) = set (free_vertices U M)"
  using assms set_free_vertices_subset
  by (auto simp add: adjacency_G2_cong)

lemma adjacency_G2_t_cong:
  assumes "t \<notin> G.S.set U"
  assumes "s \<noteq> t"
  assumes "M.invar M"
  assumes "M_lookup M t = None"
  shows "set (G.adjacency (G2 U V s t M) t) = set (free_vertices V M)"
  using assms set_free_vertices_subset
  by (auto simp add: adjacency_G2_cong)

lemma E2_cong:
  assumes "M.invar M"
  shows "G.E (G2 U V s t M) = M_tbd M \<union> {{s, v} |v. v \<in> set (free_vertices U M)} \<union> {{t, v} |v. v \<in> set (free_vertices V M)}"
  using assms
  by (intro E2_5_M_tbd_cong)

lemma symmetric_adjacency_G2:
  assumes "M.invar M"
  assumes "symmetric_Map M"
  shows "G.symmetric_adjacency' (G2 U V s t M)"
  using assms
  by (intro symmetric_adjacency_G2_5)

subsection \<open>@{term G1}\<close>

lemma invar_G1:
  assumes "G.invar G"
  assumes "G.invar G'"
  shows "G.invar (G1 G G')"
  using assms
  by (intro G.invar_difference)

lemma adjacency_G1_cong:
  assumes "G.invar G"
  assumes "G.invar G'"
  shows "set (G.adjacency (G1 G G') v) = set (G.adjacency G v) - set (G.adjacency G' v)"
  using assms
  by (intro G.adjacency_difference_cong)

lemma E1_cong:
  assumes "G.symmetric_adjacency' G"
  assumes "G.symmetric_adjacency' G'"
  shows "G.E (G1 G G') = G.E G - G.E G'"
  using assms
  by (intro G.E_difference_cong)

lemma symmetric_adjacency_G1:
  assumes "G.symmetric_adjacency' G"
  assumes "G.symmetric_adjacency' G'"
  shows "G.symmetric_adjacency' (G1 G G')"
  using assms
  by (intro G.symmetric_adjacency_difference)

subsection \<open>\<close>

lemma adjacency_union_G1_G2_cong:
  assumes "G.symmetric_adjacency' G"
  assumes "M.invar M"
  assumes "symmetric_Map M"
  assumes "M_tbd M \<subseteq> G.E G"
  shows
    "set (G.adjacency (G.union (G1 G (G2 U V s t M)) (G2 U V s t M)) u) =
     set (G.adjacency G u) \<union>
     (\<Union>v\<in>set (free_vertices U M). if u = s then {v} else if u = v then {s} else {}) \<union>
     (\<Union>v\<in>set (free_vertices V M). if u = t then {v} else if u = v then {t} else {})"
proof -
  have
    "set (G.adjacency (G.union (G1 G (G2 U V s t M)) (G2 U V s t M)) u) =
     set (G.adjacency (G1 G (G2 U V s t M)) u) \<union> set (G.adjacency (G2 U V s t M) u)"
    using assms(1) invar_G2
    by (intro invar_G1 G.adjacency_union_cong) (rule symmetric_adjacency.invar)
  also have "... = set (G.adjacency G u) \<union> set (G.adjacency (G2 U V s t M) u)"
    using assms(1) invar_G2
    by (auto simp add: adjacency_G1_cong dest: symmetric_adjacency.invar)
  also have
    "... =
     set (G.adjacency G u) \<union>
     (case M_lookup M u of None \<Rightarrow> {} | Some v \<Rightarrow> {v}) \<union>
     (\<Union>v\<in>set (free_vertices U M). if u = s then {v} else if u = v then {s} else {}) \<union>
     (\<Union>v\<in>set (free_vertices V M). if u = t then {v} else if u = v then {t} else {})"
    unfolding adjacency_G2_cong[OF assms(2)]
    by blast
  also have
    "... =
     set (G.adjacency G u) \<union>
     (\<Union>v\<in>set (free_vertices U M). if u = s then {v} else if u = v then {s} else {}) \<union>
     (\<Union>v\<in>set (free_vertices V M). if u = t then {v} else if u = v then {t} else {})"
    using assms(1, 4)
    by (fastforce simp add: symmetric_adjacency.mem_adjacency_iff_edge split: option.splits(2))
  finally show ?thesis
    .
qed

lemma E_union_G1_G2_cong:
  assumes "G.symmetric_adjacency' G"
  assumes "M.invar M"
  assumes "symmetric_Map M"
  assumes "M_tbd M \<subseteq> G.E G"
  shows
    "G.E (G.union (G1 G (G2 U V s t M)) (G2 U V s t M)) =
     G.E G \<union> {{s, v} |v. v \<in> set (free_vertices U M)} \<union> {{t, v} |v. v \<in> set (free_vertices V M)}"
proof -
  let ?G2 = "G2 U V s t M"
  let ?G1 = "G1 G ?G2"
  have "G.E (G.union ?G1 ?G2) = G.E ?G1 \<union> G.E ?G2"
    using assms(1) invar_G2
    by (intro invar_G1 G.E_union_cong) (rule symmetric_adjacency.invar)
  also have "... = G.E G \<union> G.E ?G2"
    using assms symmetric_adjacency_G2
    by (simp add: E1_cong)
  also have "... = G.E G \<union> M_tbd M \<union> {{s, v} |v. v \<in> set (free_vertices U M)} \<union> {{t, v} |v. v \<in> set (free_vertices V M)}"
    using assms(2)
    by (auto simp add: E2_5_M_tbd_cong)
  also have "... = G.E G \<union> {{s, v} |v. v \<in> set (free_vertices U M)} \<union> {{t, v} |v. v \<in> set (free_vertices V M)}"
    using assms(4)
    by auto
  finally show ?thesis
    .
qed

lemma symmetric_adjacency_union_G1_G2:
  assumes "G.symmetric_adjacency' G"
  assumes "M.invar M"
  assumes "symmetric_Map M"
  shows "G.symmetric_adjacency' (G.union (G1 G (G2 U V s t M)) (G2 U V s t M))"
  using assms
  by (intro symmetric_adjacency_G2 symmetric_adjacency_G1 G.symmetric_adjacency_union)

subsection \<open>@{term M_tbd}\<close>

lemma not_mem_Vs_M_tbd_if_free:
  assumes "symmetric_Map M"
  assumes "free M v"
  shows "v \<notin> Vs (M_tbd M)"
proof
  assume "v \<in> Vs (M_tbd M)"
  then obtain u where
    "{u, v} \<in> M_tbd M"
    by (auto simp add: Vs_def)
  hence "M_lookup M u = Some v"
    using assms(2)
    by (auto simp add: doubleton_eq_iff free_def)
  hence "M_lookup M v = Some u"
    by (simp add: assms(1))
  thus False
    using assms(2)
    by (simp add: free_def)
qed

lemma not_mem_Vs_M_tbd_imp_free:
  assumes "v \<notin> Vs (M_tbd M)"
  shows "free M v"
proof (rule ccontr, goal_cases)
  case 1
  then obtain u where
    "M_lookup M v = Some u"
    by (auto simp add: free_def)
  thus False
    using assms
    by auto
qed

lemma mem_M_tbd_iff_mem_E2:
  assumes "M.invar M"
  assumes "s \<notin> set p"
  assumes "t \<notin> set p"
  shows "\<forall>e\<in>P_tbd p. e \<in> G.E (G2 U V s t M) \<longleftrightarrow> e \<in> M_tbd M"
proof
  fix e
  assume "e \<in> P_tbd p"
  hence
    "s \<notin> e"
    "t \<notin> e"
    using assms(2, 3)
    by (auto dest: v_in_edge_in_path_gen)
  thus "e \<in> G.E (G2 U V s t M) \<longleftrightarrow> e \<in> M_tbd M"
    using assms(1)
    by (auto simp add: E2_cong)
qed

section \<open>Basic Lemmas\<close>

subsection \<open>@{term M_tbd}\<close>

sublocale graph "M_tbd M"
proof (standard, goal_cases)
  case 1
  then show ?case
    by auto
qed

lemma M_tbd_set_inorder_cong:
  assumes "M.invar M"
  shows "M_tbd M = {{u, v} |u v. (u, v) \<in> set (M_inorder M)}"
  using assms
  by (simp add: M.mem_inorder_iff_lookup_eq_Some)

lemma M_tbd_delete_cong:
  assumes "M.invar M"
  shows
    "M_tbd (M_delete u M) =
     M_tbd M -
     (case M_lookup M u of None \<Rightarrow> {} | Some v \<Rightarrow> if v \<noteq> u \<and> M_lookup M v = Some u then {} else {{u, v}})"
proof -
  { fix x y
    have
      "{x, y} \<in> M_tbd (M_delete u M) \<longleftrightarrow>
       M_lookup (M_delete u M) x = Some y \<or> M_lookup (M_delete u M) y = Some x"
      by (auto simp add: doubleton_eq_iff)
    also have
      "... \<longleftrightarrow>
       (x, y) \<in> set (M_inorder (M_delete u M)) \<or>
       (y, x) \<in> set (M_inorder (M_delete u M))"
      using assms M.invar_delete
      by (simp add: M.mem_inorder_iff_lookup_eq_Some)
    also have
      "... \<longleftrightarrow>
       (x, y) \<in> set (M_inorder M) - (case M_lookup M u of None \<Rightarrow> {} | Some v \<Rightarrow> {(u, v)}) \<or>
       (y, x) \<in> set (M_inorder M) - (case M_lookup M u of None \<Rightarrow> {} | Some v \<Rightarrow> {(u, v)})"
      using assms
      by (simp add: M.set_inorder_delete_cong)
    also have
      "... \<longleftrightarrow>
       {x, y} \<in> M_tbd M -
       (case M_lookup M u of None \<Rightarrow> {} | Some v \<Rightarrow> if v \<noteq> u \<and> M_lookup M v = Some u then {} else {{u, v}})"
    proof (cases "M_lookup M u")
      case None
      thus ?thesis
        using assms
        by (auto simp add: M.mem_inorder_iff_lookup_eq_Some doubleton_eq_iff)
    next
      case (Some v)
      show ?thesis
        using assms
        by (auto simp add: Some M.mem_inorder_iff_lookup_eq_Some doubleton_eq_iff)
    qed
    finally have
      "{x, y} \<in> M_tbd (M_delete u M) \<longleftrightarrow>
       {x, y} \<in> M_tbd M -
       (case M_lookup M u of None \<Rightarrow> {} | Some v \<Rightarrow> if v \<noteq> u \<and> M_lookup M v = Some u then {} else {{u, v}})"
      . }
  thus ?thesis
    by (intro eqI) (auto simp add: graph_def)
qed

lemma M_tbd_update_cong:
  assumes "M.invar M"
  shows
    "M_tbd (M_update u v M) =
     M_tbd M -
     (case M_lookup M u of None \<Rightarrow> {} | Some w \<Rightarrow> if w \<noteq> u \<and> M_lookup M w = Some u then {} else {{u, w}}) \<union>
     {{u, v}}"
proof -
  { fix x y
    have
      "{x, y} \<in> M_tbd (M_update u v M) \<longleftrightarrow>
       M_lookup (M_update u v M) x = Some y \<or> M_lookup (M_update u v M) y = Some x"
      by (auto simp add: doubleton_eq_iff)
    also have
      "... \<longleftrightarrow>
       (x, y) \<in> set (M_inorder (M_update u v M)) \<or>
       (y, x) \<in> set (M_inorder (M_update u v M))"
      using assms M.invar_update
      by (simp add: M.mem_inorder_iff_lookup_eq_Some)
    also have
      "... \<longleftrightarrow>
       (x, y) \<in> set (M_inorder M) - (case M_lookup M u of None \<Rightarrow> {} | Some w \<Rightarrow> {(u, w)}) \<union> {(u, v)} \<or>
       (y, x) \<in> set (M_inorder M) - (case M_lookup M u of None \<Rightarrow> {} | Some w \<Rightarrow> {(u, w)}) \<union> {(u, v)}"
      using assms
      by (simp add: M.set_inorder_update_cong)
    also have
      "... \<longleftrightarrow>
       {x, y} \<in> M_tbd M - (case M_lookup M u of None \<Rightarrow> {} | Some w \<Rightarrow> if w \<noteq> u \<and> M_lookup M w = Some u then {} else {{u, w}}) \<union> {{u, v}}"
    proof (cases "M_lookup M u")
      case None
      thus ?thesis
        using assms
        by (auto simp add: M.mem_inorder_iff_lookup_eq_Some doubleton_eq_iff)
    next
      case (Some v)
      show ?thesis
        using assms
        by (auto simp add: Some M.mem_inorder_iff_lookup_eq_Some doubleton_eq_iff)
    qed
    finally have
      "{x, y} \<in> M_tbd (M_update u v M) \<longleftrightarrow>
       {x, y} \<in> M_tbd M - (case M_lookup M u of None \<Rightarrow> {} | Some w \<Rightarrow> if w \<noteq> u \<and> M_lookup M w = Some u then {} else {{u, w}}) \<union> {{u, v}}"
      . }
  thus ?thesis
    by (intro eqI) (auto simp add: graph_def)
qed

lemma mem_Vs_M_tbd_iff:
  assumes "symmetric_Map M"
  shows "v \<notin> Vs (M_tbd M) \<longleftrightarrow> M_lookup M v = None"
proof -
  { have "v \<in> Vs (M_tbd M) \<longleftrightarrow> (\<exists>u. {v, u} \<in> M_tbd M)"
      using graph
      by (auto simp add: Vs_def)
    also have "... \<longleftrightarrow> (\<exists>u. M_lookup M v = Some u)"
      using assms
      by (auto simp add: doubleton_eq_iff)
    finally have "v \<in> Vs (M_tbd M) \<longleftrightarrow> (\<exists>u. M_lookup M v = Some u)"
      . }
  thus ?thesis
    by simp
qed

subsection \<open>@{term augment}\<close>

lemma invar_augment:
  assumes "M.invar M"
  assumes "even (length p)"
  shows "M.invar (augment M p)"
  using assms
proof (induct M p rule: augment.induct)
  case (2 M u v)
  thus ?case
    by (auto intro: M.invar_update)
next
  case (3 M u v w ws)
  hence "M.invar (M_update v u (M_update u v (M_delete w M)))"
    by (intro M.invar_delete M.invar_update)
  thus ?case
    using "3.prems"(2)
    by (auto intro: "3.hyps")
qed simp+

(**)
lemma augment_induct_case_2D:
  assumes "M.invar M"
  assumes "symmetric_Map M"
  assumes "augmenting_path (M_tbd M) [u, v]"
  assumes "distinct [u, v]"
  assumes "even (length [u, v])"
  shows
    "u \<noteq> v"
    "{u, v} \<notin> M_tbd M"
    "M.invar (M_update u v M)"
    "M.invar (M_update v u (M_update u v M))"
    "M_lookup M u = None"
    "M_lookup M v = None"
    "M_lookup (M_update u v M) u = Some v"
    "M_lookup (M_update u v M) v = None"
proof -
  show neq: "u \<noteq> v"
    using assms(4)
    by simp
  show "{u, v} \<notin> M_tbd M"
    using assms(3)
    by (auto simp add: alt_list_step dest: augmenting_pathD(2))
  show
    "M.invar (M_update u v M)"
    "M.invar (M_update v u (M_update u v M))"
    using assms(1)
    by (auto intro: M.invar_update)
  show
    "M_lookup M u = None"
    "M_lookup M v = None"
    using assms(2, 3)
    by (auto simp add: mem_Vs_M_tbd_iff dest: augmenting_pathD(3, 4))
  thus
    "M_lookup (M_update u v M) u = Some v"
    "M_lookup (M_update u v M) v = None"
    using assms(1) neq
    by (simp_all add: M.map_update)
qed

lemma augment_induct_case_3D:
  assumes "M.invar M"
  assumes "symmetric_Map M"
  assumes "augmenting_path (M_tbd M) (u # v # w # ws)"
  assumes "distinct (u # v # w # ws)"
  assumes "even (length (u # v # w # ws))"
  shows
    "u \<noteq> v"
    "v \<noteq> w"
    "u \<noteq> w"
    "{u, v} \<notin> M_tbd M"
    "{v, w} \<in> M_tbd M"
    "{u, v} \<notin> P_tbd (v # w # ws)"
    "{u, v} \<notin> P_tbd (w # ws)"
    "{v, w} \<notin> P_tbd (w # ws)"
    "M.invar (M_delete w M)"
    "M.invar (M_update u v (M_delete w M))"
    "M.invar (M_update v u (M_update u v (M_delete w M)))"
    "M_lookup M u = None"
    "M_lookup M v = Some w"
    "M_lookup M w = Some v"
    "M_lookup (M_delete w M) u = None"
    "M_lookup (M_delete w M) v = Some w"
    "M_lookup (M_delete w M) w = None"
    "M_lookup (M_update u v (M_delete w M)) v = Some w"
    "M_lookup (M_update u v (M_delete w M)) w = None"
    "M_lookup (M_update v u (M_update u v (M_delete w M))) w = None"
proof -
  show neq:
    "u \<noteq> v"
    "v \<noteq> w"
    "u \<noteq> w"
    using assms(4)
    by simp+
  show mem_M_tbd:
    "{u, v} \<notin> M_tbd M"
    "{v, w} \<in> M_tbd M"
    using assms(3)
    by (auto simp add: alt_list_step dest: augmenting_pathD(2))
  show
    "{u, v} \<notin> P_tbd (v # w # ws)"
    "{u, v} \<notin> P_tbd (w # ws)"
    "{v, w} \<notin> P_tbd (w # ws)"
    using assms(4)
    by (auto dest: v_in_edge_in_path)
  show invar:
    "M.invar (M_delete w M)"
    "M.invar (M_update u v (M_delete w M))"
    "M.invar (M_update v u (M_update u v (M_delete w M)))"
    using assms(1)
    by (auto intro: M.invar_delete M.invar_update)
  show
    "M_lookup M u = None"
    "M_lookup M v = Some w"
    "M_lookup M w = Some v"
    using assms(2, 3) mem_M_tbd(2)
    by (auto simp add: mem_Vs_M_tbd_iff doubleton_eq_iff dest: augmenting_pathD(3))
  thus
    "M_lookup (M_delete w M) u = None"
    "M_lookup (M_delete w M) v = Some w"
    "M_lookup (M_delete w M) w = None"
    using assms(1) neq(2-3)
    by (simp_all add: M.map_delete)
  thus
    "M_lookup (M_update u v (M_delete w M)) v = Some w"
    "M_lookup (M_update u v (M_delete w M)) w = None"
    using invar(1) neq(1, 3)
    by (simp_all add: M.map_update)
  thus
    "M_lookup (M_update v u (M_update u v (M_delete w M))) w = None"
    using invar(2) neq(2)
    by (simp add: M.map_update)
qed

lemma M_tbd_update_update_delete_cong:
  assumes "M.invar M"
  assumes "symmetric_Map M"
  assumes "augmenting_path (M_tbd M) (u # v # w # ws)"
  assumes "distinct (u # v # w # ws)"
  assumes "even (length (u # v # w # ws))"
  shows "M_tbd (M_update v u (M_update u v (M_delete w M))) = M_tbd M - {{v, w}} \<union> {{u, v}}"
proof -
  have "M_tbd (M_update v u (M_update u v (M_delete w M))) = M_tbd (M_update u v (M_delete w M)) - {{v, w}} \<union> {{u, v}}"
    using assms augment_induct_case_3D(10, 18, 19)
    by (simp add: M_tbd_update_cong insert_commute)
  also have "... = M_tbd (M_delete w M) \<union> {{u, v}} - {{v, w}} \<union> {{u, v}}"
    using augment_induct_case_3D(9, 15)[OF assms]
    by (simp add: M_tbd_update_cong)
  also have "... = M_tbd (M_delete w M) - {{v, w}} \<union> {{u, v}}"
    by (simp add: insert_Diff_if)
  also have "... = M_tbd M - {{v, w}} \<union> {{u, v}}"
    using assms(1) augment_induct_case_3D(13, 14)[OF assms]
    by (simp add: M_tbd_delete_cong)
  finally show ?thesis
    .
qed

lemma symmetric_Map_update_update_delete:
  assumes "M.invar M"
  assumes "symmetric_Map M"
  assumes "augmenting_path (M_tbd M) (u # v # w # ws)"
  assumes "distinct (u # v # w # ws)"
  assumes "even (length (u # v # w # ws))"
  shows "symmetric_Map (M_update v u (M_update u v (M_delete w M)))"
proof (standard, standard)
  fix x y
  have
    "M_lookup (M_update v u (M_update u v (M_delete w M))) x = Some y \<longleftrightarrow>
     (x, y) \<in> set (M_inorder (M_update v u (M_update u v (M_delete w M))))"
    using assms augment_induct_case_3D(11)
    by (intro M.mem_inorder_iff_lookup_eq_Some)
  also have "... \<longleftrightarrow> (x, y) \<in> set (M_inorder (M_update u v (M_delete w M))) - {(v, w)} \<union> {(v, u)}"
    using assms augment_induct_case_3D(10, 18)
    by (simp add: M.set_inorder_update_cong)
  also have "... \<longleftrightarrow> (x, y) \<in> set (M_inorder (M_delete w M)) \<union> {(u, v)} - {(v, w)} \<union> {(v, u)}"
    using assms augment_induct_case_3D(9, 15)
    by (simp add: M.set_inorder_update_cong)
  also have "... \<longleftrightarrow> (x, y) \<in> set (M_inorder M) - {(w, v)} \<union> {(u, v)} - {(v, w)} \<union> {(v, u)}"
    using assms(1) augment_induct_case_3D(14)[OF assms]
    by (simp add: M.set_inorder_delete_cong)
  also have "... \<longleftrightarrow> (y, x) \<in> set (M_inorder M) - {(w, v)} \<union> {(u, v)} - {(v, w)} \<union> {(v, u)}"
    using assms(1, 2)
    by (auto simp add: M.mem_inorder_iff_lookup_eq_Some)
  also have "... \<longleftrightarrow> (y, x) \<in> set (M_inorder (M_delete w M)) \<union> {(u, v)} - {(v, w)} \<union> {(v, u)}"
    using assms(1) augment_induct_case_3D(14)[OF assms]
    by (simp add: M.set_inorder_delete_cong)
  also have "... \<longleftrightarrow> (y, x) \<in> set (M_inorder (M_update u v (M_delete w M))) - {(v, w)} \<union> {(v, u)}"
    using assms augment_induct_case_3D(9, 15)
    by (simp add: M.set_inorder_update_cong)
  also have "... \<longleftrightarrow> (y, x) \<in> set (M_inorder (M_update v u (M_update u v (M_delete w M))))"
    using assms augment_induct_case_3D(10, 18)
    by (simp add: M.set_inorder_update_cong)
  also have "... \<longleftrightarrow> M_lookup (M_update v u (M_update u v (M_delete w M))) y = Some x"
    using assms
    by (intro augment_induct_case_3D(11) M.mem_inorder_iff_lookup_eq_Some[symmetric])
  finally show
    "M_lookup (M_update v u (M_update u v (M_delete w M))) x = Some y \<longleftrightarrow>
     M_lookup (M_update v u (M_update u v (M_delete w M))) y = Some x"
    .
qed

lemma augmenting_path_update_update_delete:
  assumes "M.invar M"
  assumes "symmetric_Map M"
  assumes "augmenting_path (M_tbd M) (u # v # w # ws)"
  assumes "distinct (u # v # w # ws)"
  assumes "even (length (u # v # w # ws))"
  shows "augmenting_path (M_tbd (M_update v u (M_update u v (M_delete w M)))) (w # ws)"
proof (rule augmenting_pathI, goal_cases)
  case 1
  show ?case
    using assms(5)
    by (auto simp add: Suc_le_eq)
next
  case 2
  have "Berge.alt_path (M_tbd M) (w # ws)"
    using assms(3)
    by (fastforce dest: augmenting_pathD(2) intro: alt_list_split_1[where ?l1.0 = "edges_of_path ([u, v] @ [hd (w # ws)])"])
  thus ?case
    using assms augment_induct_case_3D(7, 8)[OF assms]
    by (auto simp add: M_tbd_update_update_delete_cong intro: alt_list_cong)
next
  case 3
  show ?case
    using assms symmetric_Map_update_update_delete augment_induct_case_3D(20)
    by (simp add: mem_Vs_M_tbd_iff)
next
  case 4
  let ?x = "last (w # ws)"
  have neq:
    "?x \<noteq> u"
    "?x \<noteq> v"
    using assms(4)
    by auto
  have "M_lookup M ?x = None"
    using assms(2, 3)
    by (auto simp add: mem_Vs_M_tbd_iff dest: augmenting_pathD(4))
  hence "M_lookup (M_delete w M) ?x = None"
    using assms(1)
    by (simp add: M.map_delete)
  hence "M_lookup (M_update u v (M_delete w M)) ?x = None"
    using assms(1) M.invar_delete neq(1)
    by (simp add: M.map_update)
  hence "M_lookup (M_update v u (M_update u v (M_delete w M))) ?x = None"
    using assms(1) M.invar_delete M.invar_update neq(2)
    by (simp add: M.map_update)
  thus ?case
    using assms symmetric_Map_update_update_delete
    by (simp add: mem_Vs_M_tbd_iff)
qed

lemma symmetric_augment:
  assumes "M.invar M"
  assumes "symmetric_Map M"
  assumes "augmenting_path (M_tbd M) p"
  assumes "distinct p"
  assumes "even (length p)"
  shows "symmetric_Map (augment M p)"
  using assms
proof (induct M p rule: augment.induct)
  case (2 M u v)
  { fix x y
    have "M_lookup (augment M [u, v]) x = Some y \<longleftrightarrow> M_lookup (M_update v u (M_update u v M)) x = Some y"
      by simp
    also have "... \<longleftrightarrow> (x, y) \<in> set (M_inorder (M_update v u (M_update u v M)))"
      using "2.prems" augment_induct_case_2D(4)
      by (simp add: M.mem_inorder_iff_lookup_eq_Some)
    also have "... \<longleftrightarrow> (x, y) \<in> set (M_inorder (M_update u v M)) \<union> {(v, u)}"
      using "2.prems" augment_induct_case_2D(3, 8)
      by (simp add: M.set_inorder_update_cong)
    also have "... \<longleftrightarrow> (x, y) \<in> set (M_inorder M) \<union> {(u, v)} \<union> {(v, u)}"
      using "2.prems"(1) augment_induct_case_2D(5)[OF "2.prems"]
      by (simp add: M.set_inorder_update_cong)
    also have "... \<longleftrightarrow> (y, x) \<in> set (M_inorder M) \<union> {(u, v)} \<union> {(v, u)}"
      using "2.prems"(1, 2)
      by (auto simp add: M.mem_inorder_iff_lookup_eq_Some)
    also have "... \<longleftrightarrow> (y, x) \<in> set (M_inorder (M_update u v M)) \<union> {(v, u)}"
      using "2.prems"(1) augment_induct_case_2D(5)[OF "2.prems"]
      by (simp add: M.set_inorder_update_cong)
    also have "... \<longleftrightarrow> (y, x) \<in> set (M_inorder (M_update v u (M_update u v M)))"
      using "2.prems" augment_induct_case_2D(3, 8)
      by (simp add: M.set_inorder_update_cong)
    also have "... \<longleftrightarrow> M_lookup (M_update v u (M_update u v M)) y = Some x"
      using "2.prems" augment_induct_case_2D(4)
      by (simp add: M.mem_inorder_iff_lookup_eq_Some)
    also have "... \<longleftrightarrow> M_lookup (augment M [u, v]) y = Some x"
      by simp
    finally have "M_lookup (augment M [u, v]) x = Some y \<longleftrightarrow> M_lookup (augment M [u, v]) y = Some x"
      . }
  thus ?case
    by fast
next
  case (3 M u v w ws)
  { fix x y
    have
      "M_lookup (augment (M_update v u (M_update u v (M_delete w M))) (w # ws)) x = Some y \<longleftrightarrow>
       M_lookup (augment (M_update v u (M_update u v (M_delete w M))) (w # ws)) y = Some x"
      using "3.prems" augment_induct_case_3D(11) symmetric_Map_update_update_delete augmenting_path_update_update_delete
      by (simp add: "3.hyps") }
  thus ?case
    by simp
qed (simp_all add: augmenting_path_def)

(**)
lemma M_tbd_augment_cong:
  assumes "M.invar M"
  assumes "symmetric_Map M"
  assumes "augmenting_path (M_tbd M) p"
  assumes "distinct p"
  assumes "even (length p)"
  shows "M_tbd (augment M p) = M_tbd M \<oplus> P_tbd p"
  using assms
proof (induct rule: augment.induct)
  case (2 M u v)
  have "M_tbd (augment M [u, v]) = M_tbd (M_update v u (M_update u v M))"
    by simp
  also have "... = M_tbd (M_update u v M) \<union> {{u, v}}"
    using "2.prems" augment_induct_case_2D(3, 8)
    by (auto simp add: M_tbd_update_cong)
  also have "... = M_tbd M \<union> {{u, v}}"
    using "2.prems"(1) augment_induct_case_2D(1, 5)[OF "2.prems"]
    by (simp add: M_tbd_update_cong)
  also have "... = M_tbd M \<oplus> {{u, v}}"
    using augment_induct_case_2D(2)[OF "2.prems"]
    by (simp add: symmetric_diff_def)
  also have "... = M_tbd M \<oplus> P_tbd [u, v]"
    by simp
  finally show ?case
    .
next
  case (3 M u v w ws)
  have "M_tbd (augment M (u # v # w # ws)) = M_tbd (augment (M_update v u (M_update u v (M_delete w M))) (w # ws))"
    by simp
  also have "... = M_tbd (M_update v u (M_update u v (M_delete w M))) \<oplus> P_tbd (w # ws)"
  proof (rule "3.hyps", goal_cases)
    case 1
    show ?case
      using "3.prems"
      by (intro augment_induct_case_3D(11))
  next
    case 2
    show ?case
      using "3.prems"
      by (intro symmetric_Map_update_update_delete)
  next
    case 3
    show ?case
      using "3.prems"
      by (intro augmenting_path_update_update_delete)
  next
    case 4
    show ?case
      using "3.prems"(4)
      by force
  next
    case 5
    show ?case
      using "3.prems"(5)
      by force
  qed
  also have "... = M_tbd M - {{v, w}} \<union> {{u, v}} \<oplus> P_tbd (w # ws)"
    using "3.prems"
    by (simp add: M_tbd_update_update_delete_cong)
  also have "... = M_tbd M - {{v, w}} \<union> {{u, v}} \<union> {{v, w}} \<oplus> (P_tbd (w # ws) \<union> {{v, w}})"
    using augment_induct_case_3D(4, 5, 8)[OF "3.prems"]
    unfolding symmetric_diff_def
    by fastforce
  also have "... = M_tbd M \<union> {{u, v}} \<oplus> P_tbd (v # w # ws)"
    using "3.prems" augment_induct_case_3D(5)
    by (simp add: insert_commute insert_absorb)
  also have "... = M_tbd M \<oplus> (P_tbd (v # w # ws) \<union> {{u, v}})"
    using augment_induct_case_3D(4, 6)[OF "3.prems"]
    unfolding symmetric_diff_def
    by blast
  also have "... = M_tbd M \<oplus> P_tbd (u # v # w # ws)"
    by simp
  finally show ?case
    .
qed (simp_all add: augmenting_path_def)

(* TODO Prove with weaker assumptions via induction. *)
lemma lookup_augment_eq_NoneI:
  assumes "M.invar M"
  assumes "symmetric_Map M"
  assumes "augmenting_path (M_tbd M) p"
  assumes "distinct p"
  assumes "even (length p)"
  assumes "M_lookup M v = None"
  assumes "v \<notin> set p"
  shows "M_lookup (augment M p) v = None"
proof -
  { fix u
    assume assm: "M_lookup (augment M p) v = Some u"
    hence "{v, u} \<in> M_tbd (augment M p)"
      by blast
    hence "{v, u} \<in> M_tbd M \<oplus> P_tbd p"
      using assms
      by (simp add: M_tbd_augment_cong)
    hence "{v, u} \<in> M_tbd M"
      using assms(7)
      by (auto simp add: symmetric_diff_def intro: v_in_edge_in_path)
    hence False
      using assms(2, 6)
      by force }
  thus ?thesis
    by fastforce
qed

(* TODO Prove with weaker assumptions via induction. *)
lemma augment_subset_E:
  assumes "M.invar M"
  assumes "symmetric_Map M"
  assumes "M_tbd M \<subseteq> G.E G"
  assumes "augpath (G.E G) (M_tbd M) p"
  assumes "distinct p"
  assumes "even (length p)"
  shows "M_tbd (augment M p) \<subseteq> G.E G"
proof (rule subset_trans[where ?B = "M_tbd M \<union> P_tbd p"], goal_cases)
  case 1
  show ?case
    using assms
    by (simp add: M_tbd_augment_cong sym_diff_subset)
next
  case 2
  show ?case
    using assms(3, 4)
    by (simp add: path_edges_subset)
qed

end

section \<open>Input\<close>

subsection \<open>Definitions\<close>

locale ford_fulkerson_valid_input = ford_fulkerson where
  Map_update = Map_update and
  P_update = P_update and
  Q_snoc = Q_snoc and
  M_update = M_update for
  Map_update :: "'a::linorder \<Rightarrow> 's \<Rightarrow> 'n \<Rightarrow> 'n" and
  P_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  Q_snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" and
  M_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" +
  fixes G :: 'n
  fixes U V :: 's
  fixes s t :: 'a
  assumes symmetric_adjacency_G: "G.symmetric_adjacency' G"
  assumes bipartite_graph: "bipartite_graph (G.E G) (G.S.set U) (G.S.set V)"
  assumes s_not_mem_Vs: "s \<notin> G.V G"
  assumes t_not_mem_Vs: "t \<notin> G.V G"
  assumes s_neq_t: "s \<noteq> t"

abbreviation (in ford_fulkerson) ford_fulkerson_valid_input' :: "'n \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "ford_fulkerson_valid_input' G U V s t \<equiv>
   ford_fulkerson_valid_input
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    P_empty P_delete P_lookup P_invar
    Q_empty Q_is_empty Q_head Q_tail Q_invar Q_list
    M_empty M_delete M_lookup M_inorder M_inv Map_update
    P_update Q_snoc M_update
    G U V s t"

subsection \<open>Convenience Lemmas\<close>

lemma (in ford_fulkerson_valid_input) invar_G:
  shows "G.invar G"
  using symmetric_adjacency_G
  by (intro symmetric_adjacency.invar)

lemma (in ford_fulkerson_valid_input) symmetric_G:
  shows "v \<in> set (G.adjacency G u) \<longleftrightarrow> u \<in> set (G.adjacency G v)"
  using symmetric_adjacency_G
  by (intro symmetric_adjacency.symmetric)

lemma (in ford_fulkerson_valid_input) finite_E:
  shows "finite (G.E G)"
  using invar_G
  by (intro G.finite_E)

lemma (in ford_fulkerson_valid_input) finite_Vs:
  shows "finite (G.V G)"
  using invar_G
  by (intro G.finite_V)

lemma (in ford_fulkerson_valid_input) graph_G:
  shows "\<forall>e\<in>G.E G. \<exists>u v. e = {u, v} \<and> u \<noteq> v"
proof -
  have "\<forall>e\<in>G.E G. \<exists>u v. e = {u, v}"
    using bipartite_graph
    by (intro bipartite_graph.axioms(1) graph.graph)
  thus ?thesis
    using bipartite_graph
    by (fastforce dest: bipartite_graph.no_loop)
qed

lemma (in ford_fulkerson_valid_input) U_union_V_eq_Vs:
  shows "G.S.set U \<union> G.S.set V = G.V G"
  using bipartite_graph
  by (intro bipartite_graph.U_union_V_eq_Vs)

lemma (in ford_fulkerson_valid_input) U_V_disjoint:
  shows "G.S.set U \<inter> G.S.set V = {}"
  using bipartite_graph
  by (intro bipartite_graph.U_V_disjoint)

lemma (in ford_fulkerson_valid_input) U_subset_Vs:
  shows "G.S.set U \<subseteq> G.V G"
  using bipartite_graph
  by (intro bipartite_graph.U_subset_Vs)

lemma (in ford_fulkerson_valid_input) V_subset_Vs:
  shows "G.S.set V \<subseteq> G.V G"
  using bipartite_graph
  by (intro bipartite_graph.V_subset_Vs)

lemma (in ford_fulkerson_valid_input) s_not_mem_U:
  shows "s \<notin> G.S.set U"
  using U_subset_Vs s_not_mem_Vs
  by blast

lemma (in ford_fulkerson_valid_input) s_not_mem_V:
  shows "s \<notin> G.S.set V"
  using V_subset_Vs s_not_mem_Vs
  by blast

lemma (in ford_fulkerson_valid_input) t_not_mem_U:
  shows "t \<notin> G.S.set U"
  using U_subset_Vs t_not_mem_Vs
  by blast

lemma (in ford_fulkerson_valid_input) t_not_mem_V:
  shows "t \<notin> G.S.set V"
  using V_subset_Vs t_not_mem_Vs
  by blast

section \<open>Invariants\<close>

subsection \<open>Definitions\<close>

locale ford_fulkerson_invar = ford_fulkerson_valid_input where
  Map_update = Map_update and
  P_update = P_update and
  Q_snoc = Q_snoc and
  M_update = M_update for
  Map_update :: "'a::linorder \<Rightarrow> 's \<Rightarrow> 'n \<Rightarrow> 'n" and
  P_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  Q_snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" and
  M_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" +
  fixes M :: 'm
  assumes invar_M: "M.invar M"
  assumes symmetric_M: "symmetric_Map M"
  assumes match_imp_edge: "M_lookup M u = Some v \<Longrightarrow> {u, v} \<in> G.E G"

locale ford_fulkerson_invar_not_done_1 = ford_fulkerson_invar where
  Map_update = Map_update and
  P_update = P_update and
  Q_snoc = Q_snoc and
  M_update = M_update for
  Map_update :: "'a::linorder \<Rightarrow> 's \<Rightarrow> 'n \<Rightarrow> 'n" and
  P_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  Q_snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" and
  M_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" +
  assumes not_done_1: "\<not> done_1 U V M"

locale ford_fulkerson_invar_done_1 = ford_fulkerson_invar where
  Map_update = Map_update and
  P_update = P_update and
  Q_snoc = Q_snoc and
  M_update = M_update for
  Map_update :: "'a::linorder \<Rightarrow> 's \<Rightarrow> 'n \<Rightarrow> 'n" and
  P_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  Q_snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" and
  M_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" +
  assumes done_1: "done_1 U V M"

locale ford_fulkerson_invar_not_done_2 = ford_fulkerson_invar_not_done_1 where
  Map_update = Map_update and
  P_update = P_update and
  Q_snoc = Q_snoc and
  M_update = M_update for
  Map_update :: "'a::linorder \<Rightarrow> 's \<Rightarrow> 'n \<Rightarrow> 'n" and
  P_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  Q_snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" and
  M_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" +
  assumes not_done_2: "\<not> done_2 t (m_tbd G U V s t M)"

locale ford_fulkerson_invar_done_2 = ford_fulkerson_invar_not_done_1 where
  Map_update = Map_update and
  P_update = P_update and
  Q_snoc = Q_snoc and
  M_update = M_update for
  Map_update :: "'a::linorder \<Rightarrow> 's \<Rightarrow> 'n \<Rightarrow> 'n" and
  P_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" and
  Q_snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q" and
  M_update :: "'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> 'm" +
  assumes done_2: "done_2 t (m_tbd G U V s t M)"

abbreviation (in ford_fulkerson) ford_fulkerson_invar' :: "'n \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> bool" where
  "ford_fulkerson_invar' G U V s t M \<equiv>
   ford_fulkerson_invar
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    P_empty P_delete P_lookup P_invar
    Q_empty Q_is_empty Q_head Q_tail Q_invar Q_list
    M_empty M_delete M_lookup M_inorder M_inv
    G U V s t
    Map_update P_update Q_snoc M_update
    M"

abbreviation (in ford_fulkerson_valid_input) ford_fulkerson_invar'' :: "'m \<Rightarrow> bool" where
  "ford_fulkerson_invar'' \<equiv> ford_fulkerson_invar' G U V s t"

abbreviation (in ford_fulkerson) ford_fulkerson_invar_not_done_1' :: "'n \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> bool" where
  "ford_fulkerson_invar_not_done_1' G U V s t M \<equiv>
   ford_fulkerson_invar_not_done_1
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    P_empty P_delete P_lookup P_invar
    Q_empty Q_is_empty Q_head Q_tail Q_invar Q_list
    M_empty M_delete M_lookup M_inorder M_inv
    G U V s t M
    Map_update P_update Q_snoc M_update"

abbreviation (in ford_fulkerson_valid_input) ford_fulkerson_invar_not_done_1'' :: "'m \<Rightarrow> bool" where
  "ford_fulkerson_invar_not_done_1'' \<equiv> ford_fulkerson_invar_not_done_1' G U V s t"

abbreviation (in ford_fulkerson) ford_fulkerson_invar_done_1' :: "'n \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> bool" where
  "ford_fulkerson_invar_done_1' G U V s t M \<equiv>
   ford_fulkerson_invar_done_1
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    P_empty P_delete P_lookup P_invar
    Q_empty Q_is_empty Q_head Q_tail Q_invar Q_list
    M_empty M_delete M_lookup M_inorder M_inv
    G U V s t M
    Map_update P_update Q_snoc M_update"

abbreviation (in ford_fulkerson_valid_input) ford_fulkerson_invar_done_1'' :: "'m \<Rightarrow> bool" where
  "ford_fulkerson_invar_done_1'' \<equiv> ford_fulkerson_invar_done_1' G U V s t"

abbreviation (in ford_fulkerson) ford_fulkerson_invar_not_done_2' :: "'n \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> bool" where
  "ford_fulkerson_invar_not_done_2' G U V s t M \<equiv>
   ford_fulkerson_invar_not_done_2
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    P_empty P_delete P_lookup P_invar
    Q_empty Q_is_empty Q_head Q_tail Q_invar Q_list
    M_empty M_delete M_lookup M_inorder M_inv
    G U V s t M
    Map_update P_update Q_snoc M_update"

abbreviation (in ford_fulkerson_valid_input) ford_fulkerson_invar_not_done_2'' :: "'m \<Rightarrow> bool" where
  "ford_fulkerson_invar_not_done_2'' \<equiv> ford_fulkerson_invar_not_done_2' G U V s t"

abbreviation (in ford_fulkerson) ford_fulkerson_invar_done_2' :: "'n \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'm \<Rightarrow> bool" where
  "ford_fulkerson_invar_done_2' G U V s t M \<equiv>
   ford_fulkerson_invar_done_2
    Map_empty Map_delete Map_lookup Map_inorder Map_inv
    Set_empty Set_insert Set_delete Set_isin Set_inorder Set_inv
    P_empty P_delete P_lookup P_invar
    Q_empty Q_is_empty Q_head Q_tail Q_invar Q_list
    M_empty M_delete M_lookup M_inorder M_inv
    G U V s t M
    Map_update P_update Q_snoc M_update"

abbreviation (in ford_fulkerson_valid_input) ford_fulkerson_invar_done_2'' :: "'m \<Rightarrow> bool" where
  "ford_fulkerson_invar_done_2'' \<equiv> ford_fulkerson_invar_done_2' G U V s t"

subsection \<open>Convenience Lemmas\<close>

subsubsection \<open>@{term ford_fulkerson}\<close>

lemma (in ford_fulkerson) ford_fulkerson_invar_not_done_1I:
  assumes "ford_fulkerson_invar' G U V s t M"
  assumes "\<not> done_1 U V M"
  shows "ford_fulkerson_invar_not_done_1' G U V s t M"
  using assms
  by (simp add: ford_fulkerson_invar_not_done_1_def ford_fulkerson_invar_not_done_1_axioms_def)

lemma (in ford_fulkerson) ford_fulkerson_invar_done_1I:
  assumes "ford_fulkerson_invar' G U V s t M"
  assumes "done_1 U V M"
  shows "ford_fulkerson_invar_done_1' G U V s t M"
  using assms
  by (simp add: ford_fulkerson_invar_done_1_def ford_fulkerson_invar_done_1_axioms_def)

lemma (in ford_fulkerson) ford_fulkerson_invar_not_done_2I:
  assumes "ford_fulkerson_invar_not_done_1' G U V s t M"
  assumes "\<not> done_2 t (m_tbd G U V s t M)"
  shows "ford_fulkerson_invar_not_done_2' G U V s t M"
  using assms
  by (simp add: ford_fulkerson_invar_not_done_2_def ford_fulkerson_invar_not_done_2_axioms_def)

lemma (in ford_fulkerson) ford_fulkerson_invar_not_done_2I_2:
  assumes "ford_fulkerson_invar' G U V s t M"
  assumes "\<not> done_1 U V M"
  assumes "\<not> done_2 t (m_tbd G U V s t M)"
  shows "ford_fulkerson_invar_not_done_2' G U V s t M"
  using assms
  by
    (simp add:
     ford_fulkerson_invar_not_done_1_def ford_fulkerson_invar_not_done_1_axioms_def
     ford_fulkerson_invar_not_done_2_def ford_fulkerson_invar_not_done_2_axioms_def)

lemma (in ford_fulkerson) ford_fulkerson_invar_done_2I:
  assumes "ford_fulkerson_invar_not_done_1' G U V s t M"
  assumes "done_2 t (m_tbd G U V s t M)"
  shows "ford_fulkerson_invar_done_2' G U V s t M"
  using assms
  by (simp add: ford_fulkerson_invar_done_2_def ford_fulkerson_invar_done_2_axioms_def)

lemma (in ford_fulkerson) ford_fulkerson_invar_done_2I_2:
  assumes "ford_fulkerson_invar' G U V s t M"
  assumes "\<not> done_1 U V M"
  assumes "done_2 t (m_tbd G U V s t M)"
  shows "ford_fulkerson_invar_done_2' G U V s t M"
  using assms
  by
    (simp add:
     ford_fulkerson_invar_not_done_1_def ford_fulkerson_invar_not_done_1_axioms_def
     ford_fulkerson_invar_done_2_def ford_fulkerson_invar_done_2_axioms_def)

subsection \<open>Basic Lemmas\<close>

subsubsection \<open>@{term ford_fulkerson_invar}\<close>

lemma (in ford_fulkerson_invar) matching_M_tbd:
  shows "matching (M_tbd M)"
proof -
  { fix u v x y
    assume assm:
      "{u, v} \<in> M_tbd M"
      "{x, y} \<in> M_tbd M"
      "{u, v} \<noteq> {x, y}"
      "{u, v} \<inter> {x, y} \<noteq> {}"
    hence
      "M_lookup M u = Some v"
      "M_lookup M x = Some y"
      using assm(1, 2) symmetric_M
      by (auto simp add: doubleton_eq_iff)
    moreover hence "u = x"
      using assm(3, 4) symmetric_M
      by force
    moreover hence "v \<noteq> y"
      using assm(3)
      by fast
    ultimately have False
      by simp }
  thus ?thesis
    unfolding matching_def
    using graph
    by blast
qed

lemma (in ford_fulkerson_invar) M_tbd_subset_E:
  shows "M_tbd M \<subseteq> G.E G"
proof -
  { fix u v
    assume "{u, v} \<in> M_tbd M"
    hence "M_lookup M u = Some v"
      using symmetric_M
      by (auto simp add: doubleton_eq_iff)
    hence "{u, v} \<in> G.E G"
      by (intro match_imp_edge) }
  thus ?thesis
    using graph
    by blast
qed

lemma (in ford_fulkerson_invar) graph_matching_M_tbd:
  shows "graph_matching (G.E G) (M_tbd M)"
  using matching_M_tbd M_tbd_subset_E
  by fastforce

lemma (in ford_fulkerson_invar) finite_M_tbd:
  shows "finite (M_tbd M)"
  using M_tbd_subset_E finite_E
  by (rule finite_subset)

lemma (in ford_fulkerson_invar) E_union_G1_G2_cong:
  shows
    "G.E (G.union (G1 G (G2 U V s t M)) (G2 U V s t M)) =
     G.E G \<union> {{s, v} |v. v \<in> set (free_vertices U M)} \<union> {{t, v} |v. v \<in> set (free_vertices V M)}"
  using symmetric_adjacency_G invar_M symmetric_M M_tbd_subset_E
  by (intro E_union_G1_G2_cong)

lemma (in ford_fulkerson_invar) lookup_s_eq_None:
  shows "M_lookup M s = None"
proof -
  { fix v
    assume "M_lookup M s = Some v"
    hence "{s, v} \<in> G.E G"
      by (intro match_imp_edge)
    hence "s \<in> G.V G"
      by (intro edges_are_Vs)
    hence False
      using s_not_mem_Vs
      by auto }
  thus ?thesis
    by fastforce
qed

lemma (in ford_fulkerson_invar) lookup_t_eq_None:
  shows "M_lookup M t = None"
proof -
  { fix v
    assume "M_lookup M t = Some v"
    hence "{t, v} \<in> G.E G"
      by (intro match_imp_edge)
    hence "t \<in> G.V G"
      by (intro edges_are_Vs)
    hence False
      using t_not_mem_Vs
      by auto }
  thus ?thesis
    by fastforce
qed

lemma (in ford_fulkerson_invar) adjacency_union_G1_G2_s_cong:
  shows "set (G.adjacency (G.union (G1 G (G2 U V s t M)) (G2 U V s t M)) s) = set (free_vertices U M)"
proof -
  have
    "set (G.adjacency (G.union (G1 G (G2 U V s t M)) (G2 U V s t M)) s) =
     set (G.adjacency (G1 G (G2 U V s t M)) s) \<union> set (G.adjacency (G2 U V s t M) s)"
    using invar_G invar_G2
    by (intro invar_G1 G.adjacency_union_cong)
  also have "... = set (G.adjacency G s) \<union> set (G.adjacency (G2 U V s t M) s)"
    using invar_G invar_G2
    by (simp add: adjacency_G1_cong)
  also have "... = set (G.adjacency (G2 U V s t M) s)"
  proof -
    { fix v
      assume "v \<in> set (G.adjacency G s)"
      hence "{s, v} \<in> G.E G"
        using symmetric_adjacency_G
        by (simp add: symmetric_adjacency.mem_adjacency_iff_edge)
      hence "s \<in> G.V G"
        by (intro edges_are_Vs)
      hence False
        using s_not_mem_Vs
        by auto }
    thus ?thesis
      by blast
  qed
  also have "... = set (free_vertices U M)"
    using s_not_mem_V s_neq_t invar_M lookup_s_eq_None
    by (intro adjacency_G2_s_cong)
  finally show ?thesis
    .
qed

lemma (in ford_fulkerson_invar) adjacency_union_G1_G2_t_cong:
  shows "set (G.adjacency (G.union (G1 G (G2 U V s t M)) (G2 U V s t M)) t) = set (free_vertices V M)"
proof -
  have
    "set (G.adjacency (G.union (G1 G (G2 U V s t M)) (G2 U V s t M)) t) =
     set (G.adjacency (G1 G (G2 U V s t M)) t) \<union> set (G.adjacency (G2 U V s t M) t)"
    using invar_G invar_G2
    by (intro invar_G1 G.adjacency_union_cong)
  also have "... = set (G.adjacency G t) \<union> set (G.adjacency (G2 U V s t M) t)"
    using invar_G invar_G2
    by (simp add: adjacency_G1_cong)
  also have "... = set (G.adjacency (G2 U V s t M) t)"
  proof -
    { fix v
      assume "v \<in> set (G.adjacency G t)"
      hence "{t, v} \<in> G.E G"
        using symmetric_adjacency_G
        by (simp add: symmetric_adjacency.mem_adjacency_iff_edge)
      hence "t \<in> G.V G"
        by (intro edges_are_Vs)
      hence False
        using t_not_mem_Vs
        by auto }
    thus ?thesis
      by blast
  qed
  also have "... = set (free_vertices V M)"
    using t_not_mem_U s_neq_t invar_M lookup_t_eq_None
    by (intro adjacency_G2_t_cong)
  finally show ?thesis
    .
qed

subsubsection \<open>@{term ford_fulkerson_invar_not_done_1}\<close>

lemma (in ford_fulkerson_invar_not_done_1) V2_cong:
  shows "G.V (G2 U V s t M) = Vs (M_tbd M) \<union> {s} \<union> set (free_vertices U M) \<union> {t} \<union> set (free_vertices V M)"
proof -
  let ?G2 = "G2 U V s t M"
  have "G.E ?G2 = M_tbd M \<union> {{s, v} |v. v \<in> set (free_vertices U M)} \<union> {{t, v} |v. v \<in> set (free_vertices V M)}"
    using invar_M
    by (intro E2_cong)
  moreover have "Vs {{s, v} |v. v \<in> set (free_vertices U M)} = {s} \<union> set (free_vertices U M)"
  proof -
    have "set (free_vertices U M) \<noteq> {}"
      using not_done_1
      by (simp add: done_1_def)
    thus ?thesis
      unfolding ex_in_conv[symmetric] Vs_def
      by auto
  qed
  moreover have "Vs {{t, v} |v. v \<in> set (free_vertices V M)} = {t} \<union> set (free_vertices V M)"
  proof -
    have "set (free_vertices V M) \<noteq> {}"
      using not_done_1
      by (simp add: done_1_def)
    thus ?thesis
      unfolding ex_in_conv[symmetric] Vs_def
      by auto
  qed
  ultimately show ?thesis
    by (simp add: Vs_def)
qed

lemma (in ford_fulkerson_invar_not_done_1) V_union_G1_G2_cong:
  shows "G.V (G.union (G1 G (G2 U V s t M)) (G2 U V s t M)) = G.V G \<union> {s} \<union> {t}"
proof -
  let ?G2 = "G2 U V s t M"
  let ?G1 = "G1 G (G2 U V s t M)"
  have
    "G.V (G.union ?G1 ?G2) =
     G.V G \<union> {s} \<union> set (free_vertices U M) \<union> {t} \<union> set (free_vertices V M)"
  proof -
    have
      "G.E (G.union ?G1 ?G2) =
       G.E G \<union> {{s, v} |v. v \<in> set (free_vertices U M)} \<union> {{t, v} |v. v \<in> set (free_vertices V M)}"
      using E_union_G1_G2_cong
      .
    moreover have "Vs {{s, v} |v. v \<in> set (free_vertices U M)} = {s} \<union> set (free_vertices U M)"
    proof -
      have "set (free_vertices U M) \<noteq> {}"
        using not_done_1
        by (simp add: done_1_def)
      thus ?thesis
        unfolding ex_in_conv[symmetric] Vs_def
        by auto
    qed
    moreover have "Vs {{t, v} |v. v \<in> set (free_vertices V M)} = {t} \<union> set (free_vertices V M)"
    proof -
      have "set (free_vertices V M) \<noteq> {}"
        using not_done_1
        by (simp add: done_1_def)
      thus ?thesis
        unfolding ex_in_conv[symmetric] Vs_def
        by auto
    qed
    ultimately show ?thesis
      by (simp add: Vs_def)
  qed
  moreover have "set (free_vertices U M) \<subseteq> G.V G"
    using set_free_vertices_subset U_subset_Vs
    by (rule subset_trans)
  moreover have "set (free_vertices V M) \<subseteq> G.V G"
    using set_free_vertices_subset V_subset_Vs
    by (rule subset_trans)
  ultimately show ?thesis
    by auto
qed

lemma (in ford_fulkerson_invar_not_done_1) alt_bfs_invar_tbd:
  shows "alt_bfs_invar_tbd' (G1 G (G2 U V s t M)) (G2 U V s t M) s"
proof (standard, goal_cases)
  case 1
  show ?case
    using invar_G invar_G2
    by (intro invar_G1)
next
  case 2
  show ?case
    using invar_G2
    .
next
  case (3 v u)
  show ?case
    using symmetric_adjacency_G invar_M symmetric_M
    by (auto intro: symmetric_adjacency_G2 dest: symmetric_adjacency_G1 symmetric_adjacency.symmetric)
next
  case (4 v u)
  show ?case
    using invar_M symmetric_M
    by (auto dest: symmetric_adjacency_G2 symmetric_adjacency.symmetric)
next
  case 5
  show ?case
    using symmetric_adjacency_G invar_M symmetric_M symmetric_adjacency_G2
    by (auto simp add: E1_cong)
next
  case 6
  have "bipartite_graph (G.E (G.union (G1 G (G2 U V s t M)) (G2 U V s t M))) (G.S.set U \<union> {t}) (G.S.set V \<union> {s})"
  proof (standard, goal_cases)
    case 1
    show ?case
      by (auto simp add: G.E_def)
  next
    case 2
    have "G.V (G.union (G1 G (G2 U V s t M)) (G2 U V s t M)) = G.V G \<union> {s} \<union> {t}"
      by (intro U_subset_Vs V_subset_Vs V_union_G1_G2_cong)
    thus ?case
      by (auto simp add: U_union_V_eq_Vs)
  next
    case 3
    show ?case
      using s_not_mem_U t_not_mem_V s_neq_t
      by (simp add: U_V_disjoint)
  next
    case (4 u v)
    then consider
      (1) "{u, v} \<in> G.E G" |
      (2) "{u, v} \<in> {{s, v} |v. v \<in> set (free_vertices U M)}" |
      (3) "{u, v} \<in> {{t, v} |v. v \<in> set (free_vertices V M)}"
      by (auto simp add: E_union_G1_G2_cong)
    thus ?case
    proof (cases)
      case 1
      hence "u \<in> G.S.set U \<union> {t} \<longleftrightarrow> u \<in> G.S.set U"
        using t_not_mem_Vs
        by auto
      also have "... \<longleftrightarrow> v \<in> G.S.set V"
        using bipartite_graph 1
        by (intro bipartite_graph.tbd)
      also have "... \<longleftrightarrow> v \<in> G.S.set V \<union> {s}"
        using 1 s_not_mem_Vs
        by auto
      finally show ?thesis
        .
    next
      case 2
      hence "u \<in> G.S.set U \<union> {t} \<longleftrightarrow> u \<in> set (free_vertices U M) \<and> v = s"
        using s_not_mem_U s_neq_t set_free_vertices_subset
        by (auto simp add: doubleton_eq_iff)
      also have "... \<longleftrightarrow> v \<in> G.S.set V \<union> {s}"
        using 2 set_free_vertices_subset U_V_disjoint
        by (auto simp add: doubleton_eq_iff)
      finally show ?thesis
        .
    next
      case 3
      hence "u \<in> G.S.set U \<union> {t} \<longleftrightarrow> u = t \<and> v \<in> set (free_vertices V M)"
        using set_free_vertices_subset U_V_disjoint
        by (auto simp add: doubleton_eq_iff)
      also have "... \<longleftrightarrow> v \<in> G.S.set V \<union> {s}"
        using 3 t_not_mem_V s_neq_t set_free_vertices_subset
        by (auto simp add: doubleton_eq_iff)
      finally show ?thesis
        .
    qed
  qed
  thus ?case
    by (intro bipartite_graph.no_odd_cycle)
next
  case 7
  obtain v where
    "v \<in> set (free_vertices U M)"
    using not_done_1
    by (fastforce simp add: done_1_def)
  thus ?case
    using invar_M
    by (intro edges_are_Vs) (auto simp add: E2_cong)
qed

lemma (in ford_fulkerson_invar_not_done_1) parent:
  shows "Tbd.parent (P_lookup (m_tbd G U V s t M))"
proof -
  have "alt_bfs_invar' (G1 G (G2 U V s t M)) (G2 U V s t M) s (alt_loop (G1 G (G2 U V s t M)) (G2 U V s t M) s (init s))"
    using alt_bfs_invar_tbd
    by (intro alt_bfs_invar_alt_loop_init)
  thus ?thesis
    by (metis alt_bfs_invar.axioms(2))
qed

lemma (in ford_fulkerson_invar_not_done_1) hd_rev_follow_eq_s:
  assumes "P_lookup (m_tbd G U V s t M) v \<noteq> None"
  shows "hd (rev_follow (m_tbd G U V s t M) v) = s"
proof -
  have "alt_bfs_invar' (G1 G (G2 U V s t M)) (G2 U V s t M) s (alt_loop (G1 G (G2 U V s t M)) (G2 U V s t M) s (init s))"
    using alt_bfs_invar_tbd
    by (intro alt_bfs_invar_alt_loop_init)
  thus ?thesis
    using assms
    by (meson discovered_def alt_bfs_invar.hd_rev_follow_eq_src)
qed


lemma (in ford_fulkerson_invar_not_done_1) shortest_alt_path_rev_follow:
  assumes "P_lookup (m_tbd G U V s t M) v \<noteq> None"
  shows
    "shortest_alt_path
      (\<lambda>e. e \<in> G.E (G2 U V s t M)) (Not \<circ> (\<lambda>e. e \<in> G.E (G2 U V s t M)))
      (G.E (G.union (G1 G (G2 U V s t M)) (G2 U V s t M)))
      (rev_follow (m_tbd G U V s t M) v) s v"
  using alt_bfs_invar_tbd assms
  by (metis alt_bfs_invar_tbd.alt_bfs_invar_init discovered_def alt_bfs_invar_tbd.soundness)

subsubsection \<open>@{term ford_fulkerson_invar_not_done_2}\<close>

(* TODO Move. *)
lemma list_split_tbd:
  assumes "l \<noteq> []"
  assumes "hd l \<noteq> last l"
  obtains l' where
    "l = hd l # l' @ [last l]"
proof
  have tl_non_empty: "tl l \<noteq> []"
    using assms
    by (auto intro: singleton_hd_last)
  have "l = hd l # tl l"
    using assms(1)
    by simp
  also have "... = hd l # (butlast (tl l) @ [last (tl l)])"
    using tl_non_empty
    by simp
  finally show "l = hd l # (butlast (tl l) @ [last l])"
    using tl_non_empty
    by (simp add: last_tl)
qed

lemma (in ford_fulkerson_invar_not_done_2) rev_followE:
  obtains p u v where
    "rev_follow (m_tbd G U V s t M) t = s # u # p @ [v, t]"
proof (cases "rev_follow (m_tbd G U V s t M) t")
  case Nil
  thus ?thesis
    using parent
    by (auto dest: rev_follow_non_empty)
next
  case p: (Cons x xs)
  let ?G = "G.union (G1 G (G2 U V s t M)) (G2 U V s t M)"
  let ?p = "rev_follow (m_tbd G U V s t M) t"
  have path_p: "path (G.E ?G) ?p"
    using not_done_2
    unfolding done_2_def
    by (intro shortest_alt_pathD(2) alt_pathD(2) walk_between_nonempty_path(1)) (rule shortest_alt_path_rev_follow)
  have hd_p_eq_s: "hd ?p = s"
    using not_done_2
    by (auto simp add: done_2_def intro: hd_rev_follow_eq_s)
  have last_p_eq_t: "last ?p = t"
    using parent
    by (intro last_rev_follow)
  show ?thesis
  proof (cases xs)
    case Nil
    hence "?p = [x]"
      by (simp add: p)
    hence
      "x = s"
      "x = t"
      using hd_p_eq_s last_p_eq_t
      by simp+
    thus ?thesis
      using s_neq_t
      by force
  next
    case xs: (Cons y ys)
    show ?thesis
    proof (cases "rev ys")
      case Nil
      hence "?p = [x, y]"
        by (simp add: p xs)
      moreover hence
        "x = s"
        "y = t"
        using hd_p_eq_s last_p_eq_t
        by simp+
      ultimately have "{s, t} \<in> (G.E ?G)"
        using path_p
        by simp
      then consider
        (1) "{s, t} \<in> G.E G" |
        (2) "{s, t} \<in> {{s, v} |v. v \<in> set (free_vertices U M)}" |
        (3) "{s, t} \<in> {{t, v} |v. v \<in> set (free_vertices V M)}"
        by (auto simp add: E_union_G1_G2_cong)
      thus ?thesis
      proof (cases)
        case 1
        thus ?thesis
          using s_not_mem_Vs
          by (auto intro: edges_are_Vs)
      next
        case 2
        thus ?thesis
          using t_not_mem_U set_free_vertices_subset
          by (force simp add: doubleton_eq_iff)
      next
        case 3
        thus ?thesis
          using s_not_mem_V set_free_vertices_subset
          by (force simp add: doubleton_eq_iff)
      qed
    next
      case (Cons z zs)
      hence ys: "ys = rev zs @ [z]"
        by simp
      show ?thesis
      proof (cases zs)
        case Nil
        hence "?p = x # y # [z]"
          by (simp add: p xs ys)
        moreover hence
          "x = s"
          "z = t"
          using hd_p_eq_s last_p_eq_t
          by simp+
        ultimately have
          "{s, y} \<in> (G.E ?G)"
          "{y, t} \<in> (G.E ?G)"
          using path_p
          by simp+
        hence
          "{s, y} \<in> (G.E ?G)"
          "{t, y} \<in> (G.E ?G)"
          by (metis doubleton_eq_iff)+
        hence
          "y \<in> set (G.adjacency ?G s)"
          "y \<in> set (G.adjacency ?G t)"
          unfolding symmetric_adjacency.mem_adjacency_iff_edge[OF symmetric_adjacency_union_G1_G2[OF symmetric_adjacency_G invar_M symmetric_M]]
          .
        hence
          "y \<in> set (free_vertices U M)"
          "y \<in> set (free_vertices V M)"
          by (simp_all add: adjacency_union_G1_G2_s_cong adjacency_union_G1_G2_t_cong)
        hence
          "y \<in> G.S.set U"
          "y \<in> G.S.set V"
          using set_free_vertices_subset
          by blast+
        thus ?thesis
          using U_V_disjoint
          by blast
      next
        case (Cons z' zs')
        hence "ys = rev zs' @ [z', z]"
          by (simp add: ys)
        hence "?p = x # y # rev zs' @ [z', z]"
          by (simp add: p xs)
        moreover hence
          "x = s"
          "z = t"
          using hd_p_eq_s last_p_eq_t
          by simp+
        ultimately show ?thesis
          by (blast intro: that)
      qed
    qed
  qed
qed

lemma (in ford_fulkerson_invar_not_done_2) length_rev_follow_geq_4:
  shows "4 \<le> length (rev_follow (m_tbd G U V s t M) t)"
  using rev_followE
  by fastforce

(* TODO Move. *)
lemma length_geq_2E:
  assumes "2 \<le> length l"
  obtains x xs y where
    "l = x # xs @ [y]"
proof (cases l)
  case Nil
  thus ?thesis
    using assms
    by simp
next
  case (Cons a l)
  hence "l \<noteq> []"
    using assms
    by force
  hence "l = butlast l @ [last l]"
    by simp
  hence "a # l = a # butlast l @ [last l]"
    by fast
  thus ?thesis
    by (auto simp add: Cons[symmetric] intro: that)
qed

(* TODO Move. *)
lemma length_butlast_tl:
  assumes "2 \<le> length l"
  shows "length (butlast (tl l)) = length l - 2"
  using assms
  by (auto simp add: tl_def elim: length_geq_2E)

lemma (in ford_fulkerson_invar_not_done_2) length_p_tbd_geq_2:
  shows "2 \<le> length (p_tbd G U V s t M)"
proof -
  have "4 \<le> length (rev_follow (m_tbd G U V s t M) t)"
    using length_rev_follow_geq_4
    .
  moreover hence "length (p_tbd G U V s t M) = length (rev_follow (m_tbd G U V s t M) t) - 2"
    by (intro length_butlast_tl) simp
  ultimately show ?thesis
    by linarith
qed

lemma (in ford_fulkerson_invar_not_done_2) p_tbd_non_empty:
  shows "p_tbd G U V s t M \<noteq> []"
  using length_p_tbd_geq_2
  by force

lemma (in ford_fulkerson_invar_not_done_2)
  shows
    hd_p_tbd_mem_adjacency_G2_s: "hd (p_tbd G U V s t M) \<in> set (G.adjacency (G2 U V s t M) s)" and
    last_p_tbd_mem_adjacency_G2_t: "last (p_tbd G U V s t M) \<in> set (G.adjacency (G2 U V s t M) t)"
proof -
  let ?G = "G.union (G1 G (G2 U V s t M)) (G2 U V s t M)"
  let ?p = "rev_follow (m_tbd G U V s t M) t"
  have path_p: "path (G.E ?G) ?p"
    using not_done_2
    unfolding done_2_def
    by (intro shortest_alt_pathD(2) alt_pathD(2) walk_between_nonempty_path(1)) (rule shortest_alt_path_rev_follow)
  obtain p u v where
    p: "?p = s # u # p @ [v, t]"
    using rev_followE
    .
  hence
    "{s, u} \<in> (G.E ?G)"
    "{v, t} \<in> (G.E ?G)"
    using path_p
    by (auto intro: path_snocD[where ?p = "s # u # p"])
  hence
    "{s, u} \<in> (G.E ?G)"
    "{t, v} \<in> (G.E ?G)"
    by (metis doubleton_eq_iff)+
  hence
    "u \<in> set (G.adjacency ?G s)"
    "v \<in> set (G.adjacency ?G t)"
    unfolding symmetric_adjacency.mem_adjacency_iff_edge[OF symmetric_adjacency_union_G1_G2[OF symmetric_adjacency_G invar_M symmetric_M]]
    .
  hence
    "u \<in> set (free_vertices U M)"
    "v \<in> set (free_vertices V M)"
    by (simp_all add: adjacency_union_G1_G2_s_cong adjacency_union_G1_G2_t_cong)
  hence
    "u \<in> set (G.adjacency (G2 U V s t M) s)"
    "v \<in> set (G.adjacency (G2 U V s t M) t)"
  proof -
    assume "u \<in> set (free_vertices U M)"
    thus "u \<in> set (G.adjacency (G2 U V s t M) s)"
      using lookup_s_eq_None s_not_mem_V s_neq_t invar_M
      by (subst adjacency_G2_s_cong) blast+
    assume "v \<in> set (free_vertices V M)"
    thus "v \<in> set (G.adjacency (G2 U V s t M) t)"
      using lookup_t_eq_None t_not_mem_U s_neq_t invar_M
      by (subst adjacency_G2_t_cong) blast+
  qed
  thus
    "hd (p_tbd G U V s t M) \<in> set (G.adjacency (G2 U V s t M) s)"
    "last (p_tbd G U V s t M) \<in> set (G.adjacency (G2 U V s t M) t)"
    by (simp_all add: p butlast_append)
qed

lemma (in ford_fulkerson_invar_not_done_2) hd_p_tbd_not_mem_Vs_M:
  shows "hd (p_tbd G U V s t M) \<notin> Vs (M_tbd M)"
proof -
  have "hd (p_tbd G U V s t M) \<in> set (G.adjacency (G2 U V s t M) s)"
    using hd_p_tbd_mem_adjacency_G2_s
    .
  hence "hd (p_tbd G U V s t M) \<in> set (free_vertices U M)"
    using s_not_mem_V s_neq_t invar_M lookup_s_eq_None
    by (simp add: adjacency_G2_s_cong)
  hence "free M (hd (p_tbd G U V s t M))"
    by (simp add: free_vertices_def)
  thus ?thesis
    using symmetric_M
    by (intro not_mem_Vs_M_tbd_if_free)
qed

lemma (in ford_fulkerson_invar_not_done_2) last_p_tbd_not_mem_Vs_M:
  shows "last (p_tbd G U V s t M) \<notin> Vs (M_tbd M)"
proof -
  have "last (p_tbd G U V s t M) \<in> set (G.adjacency (G2 U V s t M) t)"
    using last_p_tbd_mem_adjacency_G2_t
    .
  hence "last (p_tbd G U V s t M) \<in> set (free_vertices V M)"
    using t_not_mem_U s_neq_t invar_M lookup_t_eq_None
    by (simp add: adjacency_G2_t_cong)
  hence "free M (last (p_tbd G U V s t M))"
    by (simp add: free_vertices_def)
  thus ?thesis
    using symmetric_M
    by (intro not_mem_Vs_M_tbd_if_free)
qed

(* TODO Move. *)
lemma distinct_imp_hd_not_mem_set_tl:
  assumes "l \<noteq> []"
  assumes "distinct l"
  shows "hd l \<notin> set (tl l)"
  using assms
  by (induct l) simp+

(* TODO Move. *)
lemma distinct_imp_last_not_mem_set_butlast:
  assumes "l \<noteq> []"
  assumes "distinct l"
  shows "last l \<notin> set (butlast l)"
  using assms
  by (induct l) auto

lemma (in ford_fulkerson_invar_not_done_2) s_not_mem_p_tbd:
  shows "s \<notin> set (p_tbd G U V s t M)"
proof -
  have "hd (rev_follow (m_tbd G U V s t M) t) \<notin> set (tl (rev_follow (m_tbd G U V s t M) t))"
    using parent
    by (intro rev_follow_non_empty distinct_rev_follow distinct_imp_hd_not_mem_set_tl)
  hence "s \<notin> set (tl (rev_follow (m_tbd G U V s t M) t))"
    using not_done_2
    by (simp add: done_2_def hd_rev_follow_eq_s)
  thus ?thesis
    by (auto dest: in_set_butlastD)
qed

lemma (in ford_fulkerson_invar_not_done_2) t_not_mem_p_tbd:
  shows "t \<notin> set (p_tbd G U V s t M)"
proof -
  have tl_non_empty: "tl (rev_follow (m_tbd G U V s t M) t) \<noteq> []"
  proof -
    have "4 \<le> length (rev_follow (m_tbd G U V s t M) t)"
      using length_rev_follow_geq_4
      .
    hence "3 \<le> length (tl (rev_follow (m_tbd G U V s t M) t))"
      by force
    thus ?thesis
      by force
  qed
  have "last (tl (rev_follow (m_tbd G U V s t M) t)) \<notin> set (p_tbd G U V s t M)"
    using tl_non_empty parent
    by (intro distinct_rev_follow distinct_tl distinct_imp_last_not_mem_set_butlast) force+
  moreover have "last (tl (rev_follow (m_tbd G U V s t M) t)) = t"
  proof -
    have "last (rev_follow (m_tbd G U V s t M) t) = t"
      using parent
      by (intro last_rev_follow)
    thus ?thesis
      using tl_non_empty
      by (subst last_tl) force+
  qed
  ultimately show ?thesis
    by force
qed

lemma (in ford_fulkerson_invar_not_done_2) mem_M_tbd_iff_mem_E2:
  shows "\<forall>e\<in>P_tbd (p_tbd G U V s t M). e \<in> G.E (G2 U V s t M) \<longleftrightarrow> e \<in> M_tbd M"
  using invar_M s_not_mem_p_tbd t_not_mem_p_tbd
  by (intro mem_M_tbd_iff_mem_E2)

lemma (in ford_fulkerson_invar_not_done_2) augmenting_path_p_tbd:
  shows "augmenting_path (M_tbd M) (p_tbd G U V s t M)"
proof (rule augmenting_pathI, goal_cases)
  case 1
  show ?case
    using length_p_tbd_geq_2
    .
next
  case 2
  let ?p = "rev_follow (m_tbd G U V s t M) t"
  have non_empty:
    "edges_of_path (p_tbd G U V s t M) \<noteq> []"
    "edges_of_path (tl ?p) \<noteq> []"
    "edges_of_path ?p \<noteq> []"
  proof -
    have "2 \<le> length (p_tbd G U V s t M)"
      using length_p_tbd_geq_2
      .
    hence
      "2 \<le> length (p_tbd G U V s t M)"
      "3 \<le> length (tl ?p)"
      "4 \<le> length ?p"
      by simp+
    hence
      "1 \<le> length (edges_of_path (p_tbd G U V s t M))"
      "2 \<le> length (edges_of_path (tl ?p))"
      "3 \<le> length (edges_of_path ?p)"
      by (simp_all add: edges_of_path_length)
    thus
      "edges_of_path (p_tbd G U V s t M) \<noteq> []"
      "edges_of_path (tl ?p) \<noteq> []"
      "edges_of_path ?p \<noteq> []"
      by fastforce+
  qed
  
  have "alt_list (\<lambda>e. e \<in> (G.E (G2 U V s t M))) (Not \<circ> (\<lambda>e. e \<in> (G.E (G2 U V s t M)))) (edges_of_path ?p)"
    using not_done_2
    unfolding done_2_def
    by (intro shortest_alt_pathD(2) alt_pathD(1)) (rule shortest_alt_path_rev_follow)
  hence "alt_list (Not \<circ> (\<lambda>e. e \<in> (G.E (G2 U V s t M)))) (\<lambda>e. e \<in> (G.E (G2 U V s t M))) (edges_of_path (tl ?p))"
    using non_empty(2)
    by (auto simp add: edges_of_path_tl intro: alt_list_tl)
  hence "alt_list (Not \<circ> (\<lambda>e. e \<in> (G.E (G2 U V s t M)))) (\<lambda>e. e \<in> (G.E (G2 U V s t M))) (edges_of_path (butlast (tl ?p)))"
    using non_empty(1)
    by (auto simp add: edges_of_path_butlast intro: alt_list_butlast)
  thus ?case
    using mem_M_tbd_iff_mem_E2
    by (auto intro: alt_list_cong)
next
  case 3
  show ?case
    using hd_p_tbd_not_mem_Vs_M
    .
next
  case 4
  show ?case
    using last_p_tbd_not_mem_Vs_M
    .
qed

lemma (in ford_fulkerson_invar_not_done_2) P_tbd_subset_E:
  shows "P_tbd (p_tbd G U V s t M) \<subseteq> G.E G"
proof
  let ?G = "G.union (G1 G (G2 U V s t M)) (G2 U V s t M)"
  let ?p = "rev_follow (m_tbd G U V s t M) t"
  fix e
  assume assm: "e \<in> P_tbd (p_tbd G U V s t M)"
  have "path (G.E ?G) ?p"
    using not_done_2
    unfolding done_2_def
    by (intro shortest_alt_pathD(2) alt_pathD(2) walk_between_nonempty_path(1)) (rule shortest_alt_path_rev_follow)
  hence "path (G.E ?G) (tl ?p)"
    by (intro tl_path_is_path)
  hence "path (G.E ?G) (p_tbd G U V s t M)"
    by (intro path_butlast)
  hence "P_tbd (p_tbd G U V s t M) \<subseteq> G.E ?G"
    by (intro path_edges_subset)
  hence "e \<in> G.E ?G"
    using assm
    by (rule set_mp)
  then consider
    (1) "e \<in> G.E G" |
    (2) "e \<in> {{s, v} |v. v \<in> set (free_vertices U M)}" |
    (3) "e \<in> {{t, v} |v. v \<in> set (free_vertices V M)}"
    by (auto simp add: E_union_G1_G2_cong)
  thus "e \<in> G.E G"
  proof (cases)
    case 1
    thus ?thesis
      .
  next
    case 2
    thus ?thesis
      using assm s_not_mem_p_tbd
      by (auto dest: v_in_edge_in_path_gen)
  next
    case 3
    thus ?thesis
      using assm t_not_mem_p_tbd
      by (auto dest: v_in_edge_in_path_gen)
  qed
qed

lemma (in ford_fulkerson_invar_not_done_2) set_p_tbd_subset_Vs:
  shows "set (p_tbd G U V s t M) \<subseteq> G.V G"
proof
  let ?G = "G.union (G1 G (G2 U V s t M)) (G2 U V s t M)"
  let ?p = "rev_follow (m_tbd G U V s t M) t"
  fix v
  assume assm: "v \<in> set (p_tbd G U V s t M)"
  have "path (G.E ?G) ?p"
    using not_done_2
    unfolding done_2_def
    by (intro shortest_alt_pathD(2) alt_pathD(2) walk_between_nonempty_path(1)) (rule shortest_alt_path_rev_follow)
  hence "path (G.E ?G) (tl ?p)"
    by (intro tl_path_is_path)
  hence "path (G.E ?G) (p_tbd G U V s t M)"
    by (intro path_butlast)
  hence "set (p_tbd G U V s t M) \<subseteq> G.V ?G"
    by (intro mem_path_Vs subsetI)
  hence "v \<in> G.V ?G"
    using assm
    by (rule set_mp)
  then consider
    (1) "v \<in> G.V G" |
    (2) "v \<in> {s}" |
    (3) "v \<in> {t}"
    by (auto simp add: V_union_G1_G2_cong)
  thus "v \<in> G.V G"
  proof (cases)
    case 1
    thus ?thesis
      .
  next
    case 2
    thus ?thesis
      using assm s_not_mem_p_tbd
      by force
  next
    case 3
    thus ?thesis
      using assm t_not_mem_p_tbd
      by force
  qed
qed

lemma (in ford_fulkerson_invar_not_done_2) distinct_p_tbd:
  shows "distinct (p_tbd G U V s t M)"
  using parent
  by (intro distinct_rev_follow distinct_tl distinct_butlast)

lemma (in ford_fulkerson_invar_not_done_2) augpath_p_tbd:
  shows "augpath (G.E G) (M_tbd M) (p_tbd G U V s t M)"
proof (rule augpathI, goal_cases)
  case 1
  thus ?case
    using P_tbd_subset_E set_p_tbd_subset_Vs
    by (intro path_tbd)
next
  case 2
  show ?case
    using distinct_p_tbd
    .
next
  case 3
  show ?case
    using augmenting_path_p_tbd
    .
qed

lemma (in ford_fulkerson_invar_not_done_2) even_length_p_tbd:
  shows "even (length (p_tbd G U V s t M))"
proof -
  let ?p = "p_tbd G U V s t M"
  have "path (G.E G) ?p"
    using P_tbd_subset_E set_p_tbd_subset_Vs
    by (intro path_tbd)
  moreover have "hd ?p \<in> G.S.set U"
  proof -
    have "hd ?p \<in> set (G.adjacency (G2 U V s t M) s)"
      using hd_p_tbd_mem_adjacency_G2_s
      .
    hence "hd ?p \<in> set (free_vertices U M)"
      using s_not_mem_V s_neq_t invar_M lookup_s_eq_None
      by (simp add: adjacency_G2_s_cong)
    thus ?thesis
      using set_free_vertices_subset
      by (rule set_rev_mp)
  qed
  moreover have "length ?p - 1 < length ?p"
    using p_tbd_non_empty
    by (fastforce intro: diff_less)
  moreover have "?p ! (length ?p - 1) \<notin> G.S.set U"
  proof -
    have "last ?p \<in> set (G.adjacency (G2 U V s t M) t)"
      using last_p_tbd_mem_adjacency_G2_t
      .
    hence "last ?p \<in> set (free_vertices V M)"
      using t_not_mem_U s_neq_t invar_M lookup_t_eq_None
      by (simp add: adjacency_G2_t_cong)
    hence "last ?p \<in> G.S.set V"
      using set_free_vertices_subset
      by (rule set_rev_mp)
    hence "last ?p \<notin> G.S.set U"
      using bipartite_graph
      by (intro bipartite_graph.mem_V_imp_not_mem_U)
    thus ?thesis
      using p_tbd_non_empty
      by (simp add: last_conv_nth)
  qed
  ultimately show ?thesis
    using bipartite_graph
    by (simp add: bipartite_graph.xexe)
qed

subsection \<open>\<close>

lemma (in ford_fulkerson_valid_input) ford_fulkerson_invar_empty:
  shows "ford_fulkerson_invar'' M_empty"
proof (standard, goal_cases)
  case 1
  show ?case
    using M.invar_empty
    .
next
  case 2
  show ?case
    by (simp add: M.map_empty)
next
  case (3 u v)
  thus ?case
    by (simp add: M.map_empty)
qed

subsection \<open>@{term ford_fulkerson.augment}\<close>

lemma (in ford_fulkerson_invar_not_done_2) ford_fulkerson_invar_augment:
  shows "ford_fulkerson_invar'' (augment M (p_tbd G U V s t M))"
proof (standard, goal_cases)
  case 1
  show ?case
    using invar_M even_length_p_tbd
    by (intro invar_augment)
next
  case 2
  show ?case
    using invar_M symmetric_M augmenting_path_p_tbd distinct_p_tbd even_length_p_tbd
    by (intro symmetric_augment)
next
  case (3 u v)
  let ?p = "p_tbd G U V s t M"
  have "{u, v} \<in> M_tbd (augment M ?p)"
    using 3
    by blast
  hence "{u, v} \<in> M_tbd M \<oplus> P_tbd ?p"
    using invar_M symmetric_M augmenting_path_p_tbd distinct_p_tbd even_length_p_tbd
    by (simp add: M_tbd_augment_cong[symmetric])
  hence "{u, v} \<in> M_tbd M \<union> P_tbd ?p"
    using sym_diff_subset
    by fast
  thus ?case
    using M_tbd_subset_E P_tbd_subset_E
    by blast
qed

section \<open>Termination\<close>

lemma (in ford_fulkerson_valid_input) loop'_dom:
  assumes "ford_fulkerson_invar'' M"
  shows "loop'_dom (G, U, V, s, t, M)"
  using assms
proof (induct "card (G.E G) - card (M_tbd M)" arbitrary: M rule: less_induct)
  case less
  let ?G2 = "G2 U V s t M"
  let ?G1 = "G1 G ?G2"
  let ?m = "alt_bfs ?G1 ?G2 s"
  have m: "?m = m_tbd G U V s t M"
    by metis
  show ?case
  proof (cases "done_1 U V M")
    case True
    thus ?thesis
      by (blast intro: loop'.domintros)
  next
    case not_done_1: False
    show ?thesis
    proof (cases "done_2 t ?m")
      case True
      thus ?thesis
        by (blast intro: loop'.domintros)
    next
      case False
      let ?p = "butlast (tl (rev_follow ?m t))"
      have p: "?p = p_tbd G U V s t M"
        by metis
      let ?M = "augment M ?p"
      have ford_fulkerson_invar_not_done_2: "ford_fulkerson_invar_not_done_2'' M"
        using less.prems not_done_1 False
        unfolding m
        by (intro ford_fulkerson_invar_not_done_2I_2)
      hence augpath_p: "augpath (G.E G) (M_tbd M) ?p"
        unfolding m
        by (intro ford_fulkerson_invar_not_done_2.augpath_p_tbd)
      show ?thesis
      proof (rule loop'.domintros, rule less.hyps, goal_cases)
        case 1
        have "card (M_tbd M) < card (M_tbd ?M)"
        proof -
          have "card (M_tbd M) < card (M_tbd M \<oplus> P_tbd ?p)"
            using finite_E less.prems augpath_p
            by
              (auto
               dest: augpathD(2, 3) ford_fulkerson_invar.M_tbd_subset_E finite_subset
               intro: new_matching_bigger)
          also have "... = card (M_tbd ?M)"
          proof -
            have
              "M.invar M"
              "symmetric_Map M"
              using less.prems
              by (auto dest: ford_fulkerson_invar.invar_M ford_fulkerson_invar.symmetric_M)
            moreover have
              "augmenting_path (M_tbd M) ?p"
              "distinct ?p"
              using augpath_p
              by (auto dest: augpathD(2, 3))
            moreover have "even (length ?p)"
              unfolding p
              using ford_fulkerson_invar_not_done_2
              by (intro ford_fulkerson_invar_not_done_2.even_length_p_tbd)
            ultimately show ?thesis
              by (simp add: M_tbd_augment_cong)
          qed
          finally show ?thesis
            .
        qed
        moreover have "card (M_tbd ?M) \<le> card (G.E G)"
        proof (intro augment_subset_E card_mono, goal_cases)
          case 1
          show ?case
            using finite_E
            .
        next
          case 2
          show ?case
            using less.prems
            by (intro ford_fulkerson_invar.invar_M)
        next
          case 3
          show ?case
            using less.prems
            by (intro ford_fulkerson_invar.symmetric_M)
        next
          case 4
          show ?case
            using less.prems
            by (intro ford_fulkerson_invar.M_tbd_subset_E)
        next
          case 5
          show ?case
            using augpath_p
            .
        next
          case 6
          show ?case
            using augpath_p
            by (intro augpathD(2))
        next
          case 7
          show ?case
            unfolding p
            using ford_fulkerson_invar_not_done_2
            by (intro ford_fulkerson_invar_not_done_2.even_length_p_tbd)
        qed
        ultimately show ?case
          by linarith
      next
        case 2
        thus ?case
          unfolding p
          using ford_fulkerson_invar_not_done_2
          by (intro ford_fulkerson_invar_not_done_2.ford_fulkerson_invar_augment)
      qed
    qed
  qed
qed

section \<open>Correctness\<close>

subsection \<open>Definitions\<close>

abbreviation (in ford_fulkerson) maximum_matching :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> bool" where
  "maximum_matching G M \<equiv> graph_matching G M \<and> (\<forall>M'. graph_matching G M' \<longrightarrow> card M' \<le> card M)"

subsection \<open>Convenience Lemmas\<close>

lemma (in ford_fulkerson_invar) loop'_dom:
  shows "loop'_dom (G, U, V, s, t, M)"
  using ford_fulkerson_invar_axioms
  by (intro loop'_dom)

lemma (in ford_fulkerson_invar) loop'_psimps:
  shows
    "loop' G U V s t M =
     (if done_1 U V M then M
      else if done_2 t (m_tbd G U V s t M) then M
           else loop' G U V s t (augment M (p_tbd G U V s t M)))"
proof -
  let ?G2 = "G2 U V s t M"
  let ?G1 = "G1 G ?G2"
  let ?m = "alt_bfs ?G1 ?G2 s"
  have m: "?m = m_tbd G U V s t M"
    by metis
  show ?thesis
    unfolding m[symmetric]
    using loop'_dom
    by (intro loop'.psimps)
qed

lemma (in ford_fulkerson_invar_done_1) loop'_psimps:
  shows "loop' G U V s t M = M"
  using done_1
  by (simp add: loop'_psimps)

lemma (in ford_fulkerson_invar_done_2) loop'_psimps:
  shows "loop' G U V s t M = M"
  using not_done_1 done_2
  by (simp add: loop'_psimps)

lemma (in ford_fulkerson_invar_not_done_2) loop'_psimps:
  shows "loop' G U V s t M = loop' G U V s t (augment M (p_tbd G U V s t M))"
  using not_done_1 not_done_2
  by (simp add: loop'_psimps)

lemma (in ford_fulkerson) ford_fulkerson_induct:
  assumes "ford_fulkerson_invar' G U V s t M"
  assumes
    "\<And>G U V s t M.
      loop'_dom (G, U, V, s, t, M) \<Longrightarrow>
      (\<not> done_1 U V M \<Longrightarrow>
       \<not> done_2 t (m_tbd G U V s t M) \<Longrightarrow>
       Q G U V s t (augment M (p_tbd G U V s t M))) \<Longrightarrow>
      Q G U V s t M"
  shows "Q G U V s t M"
proof (rule loop'.pinduct, goal_cases)
  case 1
  show ?case
    using assms(1)
    thm assms(2)
    by (intro ford_fulkerson_invar.loop'_dom)
next
  case (2 G U V s t M)
  let ?G2 = "G2 U V s t M"
  let ?G1 = "G1 G ?G2"
  let ?m = "alt_bfs ?G1 ?G2 s"
  have m: "?m = m_tbd G U V s t M"
    by metis
  show ?case
    using "2"
    unfolding m
    by (rule assms(2))
qed

subsection \<open>\<close>

lemma (in ford_fulkerson_invar_done_1) maximum_matching_M_tbd:
  shows "maximum_matching (G.E G) (M_tbd M)"
proof -
  { fix M'
    assume assm: "graph_matching (G.E G) M' \<and> card (M_tbd M) < card M'"
    obtain p where
      augpath_p: "augpath (G.E G) (M_tbd M) p"
    proof -
      have "\<exists>M'\<subseteq>(G.E G). matching M' \<and> card (M_tbd M) < card M'"
        using assm
        by blast
      hence "\<exists>p. augmenting_path (M_tbd M) p \<and> path (G.E G) p \<and> distinct p"
        using finite_M_tbd graph_matching_M_tbd graph_G finite_Vs
        by (simp add: Berge)
      thus ?thesis
        by (auto intro: that)
    qed
    have p_non_empty: "p \<noteq> []"
      using augpath_p
      by (auto dest: augmenting_pathD(1))
    have free:
      "free M (hd p)"
      "free M (last p)"
      using augpath_p
      by (auto dest: augmenting_pathD(3, 4) intro: not_mem_Vs_M_tbd_imp_free)
    have mem_Vs:
      "hd p \<in> G.V G"
      "last p \<in> G.V G"
      using augpath_p p_non_empty
      by (fastforce intro: mem_path_Vs)+
    have even_length: "even (length p)"
      using augpath_p
      by (auto simp add: edges_of_path_length dest: augmenting_path_odd_length)
    hence False
    proof (cases "hd p \<in> G.S.set U")
      case True
      have "last p \<in> G.S.set V"
      proof -
        have "length p - 1 < length p"
          using p_non_empty
          by (fastforce intro: diff_less)
        moreover have "odd (length p - 1)"
          using p_non_empty even_length
          by simp
        ultimately have "p ! (length p - 1) \<notin> G.S.set U"
          using bipartite_graph augpath_p True
          by (simp add: bipartite_graph.xexe)
        hence "last p \<notin> G.S.set U"
          using p_non_empty
          by (simp add: last_conv_nth)
        with bipartite_graph mem_Vs(2)
        show ?thesis
          by (rule bipartite_graph.not_mem_U_imp_mem_V)
      qed
      hence
        "hd p \<in> set (free_vertices U M)"
        "last p \<in> set (free_vertices V M)"
        using True free
        by (simp_all add: G.S.set_def free_vertices_def)
      thus ?thesis
        using done_1
        by (auto simp add: done_1_def)
    next
      case False
      with bipartite_graph mem_Vs(1)
      have hd_mem_V: "hd p \<in> G.S.set V"
        by (rule bipartite_graph.not_mem_U_imp_mem_V)
      have "last p \<in> G.S.set U"
      proof -
        have "length p - 1 < length p"
          using p_non_empty
          by (fastforce intro: diff_less)
        moreover have "odd (length p - 1)"
          using p_non_empty even_length
          by simp
        ultimately have "p ! (length p - 1) \<notin> G.S.set V"
          using bipartite_graph augpath_p hd_mem_V
          by (simp add: bipartite_graph.xuxu)
        hence "last p \<notin> G.S.set V"
          using p_non_empty
          by (simp add: last_conv_nth)
        with bipartite_graph mem_Vs(2)
        show ?thesis
          by (rule bipartite_graph.not_mem_V_imp_mem_U)
      qed
      hence
        "hd p \<in> set (free_vertices V M)"
        "last p \<in> set (free_vertices U M)"
        using hd_mem_V free
        by (simp_all add: G.S.set_def free_vertices_def)
      thus ?thesis
        using done_1
        by (auto simp add: done_1_def)
    qed }
  thus ?thesis
    using graph_matching_M_tbd
    by force
qed

lemma (in ford_fulkerson_invar_done_2) maximum_matching_M_tbd:
  shows "maximum_matching (G.E G) (M_tbd M)"
proof -
  { fix M'
    let ?G2 = "G2 U V s t M"
    let ?G1 = "G1 G ?G2"
    let ?G = "G.union ?G1 ?G2"
    assume assm: "graph_matching (G.E G) M' \<and> card (M_tbd M) < card M'"
    obtain p where
      augpath_p: "augpath (G.E G) (M_tbd M) p"
    proof -
      have "\<exists>M'\<subseteq>(G.E G). matching M' \<and> card (M_tbd M) < card M'"
        using assm
        by blast
      hence "\<exists>p. augmenting_path (M_tbd M) p \<and> path (G.E G) p \<and> distinct p"
        using finite_M_tbd graph_matching_M_tbd graph_G finite_Vs
        by (simp add: Berge)
      thus ?thesis
        by (auto intro: that)
    qed
    have p_non_empty: "p \<noteq> []"
      using augpath_p
      by (auto dest: augmenting_pathD(1))
    have free:
      "free M (hd p)"
      "free M (last p)"
      using augpath_p
      by (auto dest: augmenting_pathD(3, 4) intro: not_mem_Vs_M_tbd_imp_free)
    have mem_Vs:
      "hd p \<in> G.V G"
      "last p \<in> G.V G"
      using augpath_p p_non_empty
      by (fastforce intro: mem_path_Vs)+
    have even_length: "even (length p)"
      using augpath_p
      by (auto simp add: edges_of_path_length dest: augmenting_path_odd_length)
    obtain p' where
      augpath_p': "augpath (G.E G) (M_tbd M) p'" and
      hd_p': "hd p' \<in> set (free_vertices U M)" and
      last_p': "last p' \<in> set (free_vertices V M)"
    proof (cases "hd p \<in> G.S.set U")
      case True
      have "last p \<in> G.S.set V"
      proof -
        have "length p - 1 < length p"
          using p_non_empty
          by (fastforce intro: diff_less)
        moreover have "odd (length p - 1)"
          using p_non_empty even_length
          by simp
        ultimately have "p ! (length p - 1) \<notin> G.S.set U"
          using bipartite_graph augpath_p True
          by (simp add: bipartite_graph.xexe)
        hence "last p \<notin> G.S.set U"
          using p_non_empty
          by (simp add: last_conv_nth)
        with bipartite_graph mem_Vs(2)
        show ?thesis
          by (rule bipartite_graph.not_mem_U_imp_mem_V)
      qed
      hence
        "hd p \<in> set (free_vertices U M)"
        "last p \<in> set (free_vertices V M)"
        using True free
        by (simp_all add: G.S.set_def free_vertices_def)
      thus ?thesis
        using augpath_p
        by (intro that)
    next
      case False
      with bipartite_graph mem_Vs(1)
      have hd_mem_V: "hd p \<in> G.S.set V"
        by (rule bipartite_graph.not_mem_U_imp_mem_V)
      have "last p \<in> G.S.set U"
      proof -
        have "length p - 1 < length p"
          using p_non_empty
          by (fastforce intro: diff_less)
        moreover have "odd (length p - 1)"
          using p_non_empty even_length
          by simp
        ultimately have "p ! (length p - 1) \<notin> G.S.set V"
          using bipartite_graph augpath_p hd_mem_V
          by (simp add: bipartite_graph.xuxu)
        hence "last p \<notin> G.S.set V"
          using p_non_empty
          by (simp add: last_conv_nth)
        with bipartite_graph mem_Vs(2)
        show ?thesis
          by (rule bipartite_graph.not_mem_V_imp_mem_U)
      qed
      hence
        "hd p \<in> set (free_vertices V M)"
        "last p \<in> set (free_vertices U M)"
        using hd_mem_V free
        by (simp_all add: G.S.set_def free_vertices_def)
      hence
        "hd (rev p) \<in> set (free_vertices U M)"
        "last (rev p) \<in> set (free_vertices V M)"
        using p_non_empty
        by (simp_all add: hd_rev last_rev)
      thus ?thesis
        using augpath_p
        by (intro that) (rule augpath_rev_if_augpath)
    qed
    have "alt_path (\<lambda>e. e \<in> G.E ?G2) (Not \<circ> (\<lambda>e. e \<in> G.E ?G2)) (G.E ?G) (s # p' @ [t]) s t"
    proof -
      have "alt_path (Not \<circ> (\<lambda>e. e \<in> G.E ?G2)) (\<lambda>e. e \<in> G.E ?G2) (G.E ?G) p' (hd p') (last p')"
      proof (intro alt_pathI, goal_cases)
        case 1
        have
          "s \<notin> set p'"
          "t \<notin> set p'"
          using augpath_p' s_not_mem_Vs t_not_mem_Vs
          by (auto intro: mem_path_Vs)
        hence "\<forall>e\<in>P_tbd p'. e \<in> G.E ?G2 \<longleftrightarrow> e \<in> M_tbd M"
          using invar_M
          by (intro mem_M_tbd_iff_mem_E2)
        thus ?case
          using augpath_p'
          by (force dest: augmenting_pathD(2) intro: alt_list_cong)
      next
        case 2
        show ?case
        proof (rule nonempty_path_walk_between, goal_cases)
          case 1
          have "path (G.E G) p'"
            using augpath_p'
            ..
          thus ?case
            by (auto simp add: E_union_G1_G2_cong intro: path_subset)
        next
          case 2
          show ?case
            using augpath_p'
            by (auto dest: augmenting_pathD(1))
        qed simp+
      qed
      hence "alt_path (Not \<circ> (\<lambda>e. e \<in> G.E ?G2)) (\<lambda>e. e \<in> G.E ?G2) (G.E ?G) (p' @ [t]) (hd p') t"
      proof (rule alt_path_snoc_oddI, goal_cases)
        case 1
        show ?case
          using augpath_p'
          by (intro augmenting_path_odd_length) force
      next
        case 2
        show ?case
          using last_p'
          by (auto simp add: E_union_G1_G2_cong)
      next
        case 3
        show ?case
          using invar_M last_p'
          by (auto simp add: E2_cong)
      qed
      thus ?thesis
        thm alt_path_ConsI[where ?p = "p' @ [t]"]
      proof (rule alt_path_ConsI, goal_cases)
        case 1
        show ?case
          using hd_p'
          by (auto simp add: E_union_G1_G2_cong)
      next
        case 2
        show ?case
          using invar_M hd_p'
          by (auto simp add: E2_cong)
      qed
    qed
    hence "alt_reachable (\<lambda>e. e \<in> G.E ?G2) (Not \<circ> (\<lambda>e. e \<in> G.E ?G2)) (G.E ?G) s t"
      by (auto simp add: alt_reachable_def)
    hence False
      using alt_bfs_invar_tbd s_neq_t done_2
      unfolding done_2_def
      by (metis alt_bfs_invar_tbd.alt_bfs_invar_init discovered_def alt_bfs_invar_tbd.completeness) }
  thus ?thesis
    using graph_matching_M_tbd
    by force
qed

lemma (in ford_fulkerson_valid_input) correctness:
  assumes "ford_fulkerson_invar'' M"
  shows "maximum_matching (G.E G) (M_tbd (loop' G U V s t M))"
  using assms
proof (induct rule: ford_fulkerson_induct[OF assms])
  case (1 G U V s t M)
  show ?case
  proof (cases "done_1 U V M")
    case True
    with "1.prems"
    have "ford_fulkerson_invar_done_1' G U V s t M"
      by (intro ford_fulkerson_invar_done_1I)
    thus ?thesis
      by
        (intro ford_fulkerson_invar_done_1.maximum_matching_M_tbd)
        (simp add: ford_fulkerson_invar_done_1.loop'_psimps)
  next
    case not_done_1: False
    show ?thesis
    proof (cases "done_2 t (m_tbd G U V s t M)")
      case True
      with "1.prems" not_done_1
      have "ford_fulkerson_invar_done_2' G U V s t M"
        by (intro ford_fulkerson_invar_done_2I_2)
      thus ?thesis
        by
          (intro ford_fulkerson_invar_done_2.maximum_matching_M_tbd)
          (simp add: ford_fulkerson_invar_done_2.loop'_psimps)
    next
      case False
      with "1.prems" not_done_1
      have "ford_fulkerson_invar_not_done_2' G U V s t M"
        by (intro ford_fulkerson_invar_not_done_2I_2)
      thus ?thesis
        using not_done_1 False
        by
          (auto
           simp add: ford_fulkerson_invar_not_done_2.loop'_psimps
           dest: "1.hyps"(2)
           intro: ford_fulkerson_invar_not_done_2.ford_fulkerson_invar_augment)
    qed
  qed
qed

theorem (in ford_fulkerson_valid_input) ford_fulkerson_correct:
  shows "maximum_matching (G.E G) (M_tbd (ford_fulkerson G U V s t))"
  using ford_fulkerson_invar_empty
  by (intro correctness)

corollary (in ford_fulkerson) ford_fulkerson_correct:
  assumes "ford_fulkerson_valid_input' G U V s t"
  shows "maximum_matching (G.E G) (M_tbd (ford_fulkerson G U V s t))"
  using assms
  by (intro ford_fulkerson_valid_input.ford_fulkerson_correct)

end
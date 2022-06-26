theory \<^marker>\<open>tag invisible\<close> Parent_Relation
  imports
    Main
begin

text \<^marker>\<open>tag invisible\<close> \<open>We (redefine and) extend the formalization of a well-founded parent relation.\<close>

(* Adapted from session @{session Berge}. *)

definition \<^marker>\<open>tag invisible\<close> follow_invar :: "('a \<rightharpoonup> 'a) \<Rightarrow> bool" where
  "follow_invar parent \<equiv> wf {(u, v). parent v = Some u}"

locale \<^marker>\<open>tag invisible\<close> parent = 
  fixes parent :: "'a \<rightharpoonup> 'a"
  assumes follow_invar: "follow_invar parent"

function \<^marker>\<open>tag invisible\<close> (in parent) (domintros) follow :: "'a \<Rightarrow> 'a list" where
  "follow v = (case parent v of None \<Rightarrow> [v] | Some u \<Rightarrow> v # follow u)"
  by pat_completeness auto

lemma \<^marker>\<open>tag invisible\<close> (in parent)
  assumes "parent v = None"
  shows "follow_dom v"
  using assms
  by (auto intro: follow.domintros)

lemma \<^marker>\<open>tag invisible\<close> (in parent)
  assumes "parent v = Some u"
  assumes "follow_dom u"
  shows "Wellfounded.accp follow_rel v"
  using assms
  by (auto intro: follow.domintros)

lemma \<^marker>\<open>tag invisible\<close> (in parent) follow_dom_if_wfP_follow_rel:
  assumes "wfP follow_rel"
  shows "follow_dom v"
  using assms
  by (intro accp_wfPD)

lemma \<^marker>\<open>tag invisible\<close> (in parent) follow_dom_if_wf_follow_rel:
  assumes "wf {(u, v). follow_rel u v}"
  shows "follow_dom v"
  using assms
  by (intro follow_dom_if_wfP_follow_rel) (simp add: wfP_def)

lemma \<^marker>\<open>tag invisible\<close> (in parent) follow_rel_eq_parent:
  shows "follow_rel = (\<lambda>u v. parent v = Some u)"
  by (fastforce simp add: follow_rel.simps)

lemma \<^marker>\<open>tag invisible\<close> (in parent) wf_follow_rel:
  shows "wf {(u, v). follow_rel u v}"
  using follow_invar
  by (simp add: follow_invar_def follow_rel_eq_parent)

lemma \<^marker>\<open>tag invisible\<close> (in parent) follow_dom:
  shows "follow_dom v"
  using wf_follow_rel
  by (intro follow_dom_if_wf_follow_rel)

lemma \<^marker>\<open>tag invisible\<close> (in parent) follow_pinduct:
  assumes "\<And>v. (\<And>u. parent v = Some u \<Longrightarrow> P u) \<Longrightarrow> P v"
  shows "P v"
  using follow_dom assms
  by (rule follow.pinduct)

lemma \<^marker>\<open>tag invisible\<close> (in parent) follow_psimps:
  shows "follow v = (case parent v of None \<Rightarrow> [v] | Some u \<Rightarrow> v # follow u)"
  using follow_dom
  by (intro follow.psimps)

lemma \<^marker>\<open>tag invisible\<close> (in parent) follow_non_empty:
  shows "follow v \<noteq> []"
  by (simp add: follow_psimps split: option.split)

lemma \<^marker>\<open>tag invisible\<close> (in parent) follow_ConsD:
  assumes "follow u = v # p"
  shows "v = u"
  using assms
  by (simp add: follow_psimps split: option.splits(2))

lemma \<^marker>\<open>tag invisible\<close> (in parent) follow_Cons_ConsD:
  assumes "follow v = v # u # p"
  shows
    "follow u = u # p"
    "parent v = Some u"
  using assms
  by (auto simp add: follow_psimps split: option.splits(2))

lemma \<^marker>\<open>tag invisible\<close> (in parent) follow_Cons_ConsE:
  assumes "follow v = v # p"
  assumes "p \<noteq> []"
  obtains u where "follow u = p"
  using assms
  by (simp add: follow_psimps split: option.splits(2))

lemma \<^marker>\<open>tag invisible\<close> (in parent) follow_appendD:
  assumes "follow v = p @ u # p'"
  shows "follow u = u # p'"
  using assms
  by (induct p arbitrary: v) (auto dest: follow_ConsD elim: follow_Cons_ConsE)

lemma \<^marker>\<open>tag invisible\<close> (in parent) parent_last_follow_eq_None:
  shows "parent (last (follow v)) = None"
proof -
  have "follow v = butlast (follow v) @ [last (follow v)]"
    using follow_non_empty
    by (intro append_butlast_last_id[symmetric])
  hence "follow (last (follow v)) = [last (follow v)]"
    by (simp add: follow_appendD)
  thus ?thesis
    by (simp add: follow_psimps split: option.splits(2))
qed

lemma \<^marker>\<open>tag invisible\<close> (in parent) parent_eq_SomeE:
  assumes "parent v = Some u"
  obtains p where "follow v = v # u # p"
  using assms
  by (fastforce simp add: follow_psimps split: option.split)

lemma \<^marker>\<open>tag invisible\<close> (in parent) parent_eq_SomeD:
  assumes "parent v = Some u"
  shows
    "u \<noteq> v"
    "v \<notin> set (follow u)"
proof (goal_cases)
  case 1
  show ?case
  proof
    assume "u = v"
    then obtain p where
      "follow v = v # v # p"
      using assms
      by (elim parent_eq_SomeE) simp
    moreover hence "follow v = v # p"
      by (blast intro: follow_Cons_ConsD(1))
    ultimately show False
      using not_Cons_self
      by simp
  qed
next
  case 2
  show ?case
  proof
    assume "v \<in> set (follow u)"
    then obtain p p' where
      "follow u = p @ v # p'"
      by (blast dest: split_list)
    hence
      "follow v = v # (p @ v # p')"
      "follow v = v # p'"
      using assms
      by (fastforce simp add: follow_psimps dest: follow_appendD)+
    thus False
      by simp
  qed
qed

lemma \<^marker>\<open>tag invisible\<close> (in parent) distinct_follow:
  shows "distinct (follow v)"
proof (induct v rule: follow_pinduct)
  case (1 v)
  show ?case
  proof (cases "parent v")
    case None
    thus ?thesis
      by (simp add: follow_psimps)
  next
    case (Some u)
    hence "distinct (follow u)"
      by (intro "1.hyps")
    thus ?thesis
      using Some
      by (auto simp add: follow_psimps dest: parent_eq_SomeD)
  qed
qed

lemma \<^marker>\<open>tag invisible\<close> (in parent) two_followsD:
  assumes "follow v1 = p1 @ u # p1'"
  assumes "follow v2 = p2 @ u # p2'"
  shows "p1' = p2'"
  using follow_appendD[OF assms(1)] follow_appendD[OF assms(2)]
  by simp

end \<^marker>\<open>tag invisible\<close> 
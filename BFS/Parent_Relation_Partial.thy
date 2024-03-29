theory \<^marker>\<open>tag invisible\<close> Parent_Relation_Partial
  imports
    Parent_Relation
begin

partial_function \<^marker>\<open>tag invisible\<close> (tailrec) rev_follow_partial where
  "rev_follow_partial a m v = (case m v of None \<Rightarrow> v # a | Some u \<Rightarrow> rev_follow_partial (v # a) m u)"

definition \<^marker>\<open>tag invisible\<close> rev_follow :: "('a \<Rightarrow> 'a option) \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "rev_follow \<equiv> rev_follow_partial []"

lemma \<^marker>\<open>tag invisible\<close> rev_follow_partial_eq_rev_follow:
  assumes "parent m"
  shows "rev_follow_partial a m v = rev (parent.follow m v) @ a"
proof (induct arbitrary: a rule: parent.follow_pinduct[OF assms])
  case (1 v)
  show ?case
  proof (cases "m v")
    case None
    thus ?thesis
      using assms
      by (simp add: rev_follow_partial.simps parent.follow_psimps)
  next
    case (Some u)
    hence "rev_follow_partial a m v = rev_follow_partial (v # a) m u"
      by (simp add: rev_follow_partial.simps)
    also have "... = rev (parent.follow m u) @ (v # a)"
      using Some
      by (intro "1.hyps")
    also have "... = rev (parent.follow m v) @ a"
      using assms Some
      by (simp add: parent.follow_psimps)
    finally show ?thesis
      .
  qed
qed

lemma \<^marker>\<open>tag invisible\<close> rev_follow_eq_rev_follow:
  assumes "parent m"
  shows "rev_follow m v = rev (parent.follow m v)"
  using assms
  by (simp add: rev_follow_def rev_follow_partial_eq_rev_follow)

(*
partial_function (in parent) (tailrec) rev_follow_partial where
  "rev_follow_partial a v = (case parent v of None \<Rightarrow> v # a | Some u \<Rightarrow> rev_follow_partial (v # a) u)"

lemma (in parent) rev_follow_partial_eq_rev_follow:
  shows "rev_follow_partial a v = rev (follow v) @ a"
proof (induct arbitrary: a rule: follow_pinduct)
  case (1 v)
  show ?case
  proof (cases "parent v")
    case None
    thus ?thesis
      by (simp add: rev_follow_partial.simps follow_psimps)
  next
    case (Some u)
    hence "rev_follow_partial a v = rev_follow_partial (v # a) u"
      by (simp add: rev_follow_partial.simps)
    also have "... = rev (follow u) @ (v # a)"
      using Some
      by (intro "1.hyps")
    also have "... = rev (follow v) @ a"
      using Some
      by (simp add: follow_psimps)
    finally show ?thesis
      .
  qed
qed
*)

end \<^marker>\<open>tag invisible\<close> 
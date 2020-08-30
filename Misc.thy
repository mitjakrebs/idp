theory Misc
  imports
    Queue_Specs
begin

section \<open>Queues\<close>

lemma (in Queue) size_tail:
  assumes "invar q"
  assumes "mset q \<noteq> {#}"
  shows "size (mset (tail q)) = size (mset q) - 1"
  using assms mset_head
  by (simp add: mset_tail size_Diff_singleton)

end
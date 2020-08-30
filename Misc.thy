theory Misc
  imports
    Queue_Specs
begin

section \<open>Queues\<close>

lemma (in Queue) length_tail:
  assumes "invar q"
  assumes "list q \<noteq> Nil"
  shows "length (list (tail q)) = length (list q) - 1"
  using assms list_head
  by (simp add: list_tail)

end
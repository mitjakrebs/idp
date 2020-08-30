theory Queue_Specs
  imports "HOL-Library.Multiset"
begin

locale Queue =
  fixes empty :: "'q"
  fixes is_empty :: "'q \<Rightarrow> bool"
  fixes snoc :: "'q \<Rightarrow> 'a \<Rightarrow> 'q"
  fixes head :: "'q \<Rightarrow> 'a"
  fixes tail :: "'q \<Rightarrow> 'q"
  fixes invar :: "'q \<Rightarrow> bool"
  fixes mset :: "'q \<Rightarrow> 'a multiset"
  assumes mset_empty: "mset empty = {#}"
  assumes is_empty: "invar q \<Longrightarrow> is_empty q = (mset q = {#})"
  assumes mset_snoc: "invar q \<Longrightarrow> mset (snoc q x) = mset q + {#x#}"
  assumes mset_head: "\<lbrakk> invar q; mset q \<noteq> {#} \<rbrakk> \<Longrightarrow> head q \<in># mset q" (* TODO *)
  assumes mset_tail: "\<lbrakk> invar q; mset q \<noteq> {#} \<rbrakk> \<Longrightarrow> mset (tail q) = mset q - {#head q#}"
  assumes invar_empty: "invar empty"
  assumes invar_snoc: "invar q \<Longrightarrow> invar (snoc q x)"
  assumes invar_tail: "\<lbrakk> invar q; mset q \<noteq> {#} \<rbrakk> \<Longrightarrow> invar (tail q)"

end
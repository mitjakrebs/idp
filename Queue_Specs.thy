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
  fixes list :: "'q \<Rightarrow> 'a list"
  assumes list_empty: "list empty = Nil"
  assumes is_empty: "invar q \<Longrightarrow> is_empty q = (list q = Nil)"
  assumes list_snoc: "invar q \<Longrightarrow> list (snoc q x) = list q @ [x]"
  assumes list_head: "\<lbrakk> invar q; list q \<noteq> Nil \<rbrakk> \<Longrightarrow> head q = hd (list q)"
  assumes list_tail: "\<lbrakk> invar q; list q \<noteq> Nil \<rbrakk> \<Longrightarrow> list (tail q) = tl (list q)"
  assumes invar_empty: "invar empty"
  assumes invar_snoc: "invar q \<Longrightarrow> invar (snoc q x)"
  assumes invar_tail: "\<lbrakk> invar q; list q \<noteq> Nil \<rbrakk> \<Longrightarrow> invar (tail q)"

end
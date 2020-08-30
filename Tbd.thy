theory Tbd
  imports "HOL-Data_Structures.Set_Specs"
begin

(* locale tbd = Set where insert = insert for insert :: "'a \<Rightarrow> 's \<Rightarrow> 's" (* for typing purposes only *) +
  fixes fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 's \<Rightarrow> 'b \<Rightarrow> 'b" *)

locale tbd =
  fixes fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"

end
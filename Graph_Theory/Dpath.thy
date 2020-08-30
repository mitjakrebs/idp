theory Dpath
  imports
    Dgraph
    Ports.Berge_to_DDFS
begin

type_synonym 'v dpath = "'v list"

abbreviation dpath_length :: "'v dpath \<Rightarrow> nat" where
  "dpath_length p \<equiv> length (edges_of_dpath p)"

end
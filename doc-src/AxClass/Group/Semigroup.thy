theory Semigroup = Main:;

consts
  times :: "'a \\<Rightarrow> 'a \\<Rightarrow> 'a"    (infixl "\<Otimes>" 70);
axclass
  semigroup < "term"
  assoc: "(x \<Otimes> y) \<Otimes> z = x \<Otimes> (y \<Otimes> z)";

end;
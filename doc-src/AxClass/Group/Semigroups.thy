theory Semigroups = Main:;

constdefs
  is_assoc :: "('a \\<Rightarrow> 'a \\<Rightarrow> 'a) \\<Rightarrow> bool"
  "is_assoc f \\<equiv> \\<forall>x y z. f (f x y) z = f x (f y z)";

consts
  plus :: "'a \\<Rightarrow> 'a \\<Rightarrow> 'a"    (infixl "\<Oplus>" 65);
axclass
  plus_semigroup < "term"
  assoc: "is_assoc (op \<Oplus>)";

consts
  times :: "'a \\<Rightarrow> 'a \\<Rightarrow> 'a"    (infixl "\<Otimes>" 65);
axclass
  times_semigroup < "term"
  assoc: "is_assoc (op \<Otimes>)";

end;
theory Semigroups = Main:;

text {*
 \noindent Associativity of binary operations:
*};
constdefs
  is_assoc :: "('a \\<Rightarrow> 'a \\<Rightarrow> 'a) \\<Rightarrow> bool"
  "is_assoc f == \\<forall>x y z. f (f x y) z = f x (f y z)";

text {*
 \medskip\noindent Semigroups over \isa{(op~{\isasymOplus})}:
 %term (latex xsymbols symbols) "op \<Oplus>";
*};

consts
  plus :: "'a \\<Rightarrow> 'a \\<Rightarrow> 'a"    (infixl "\<Oplus>" 65);
axclass
  plus_semigroup < "term"
  assoc: "is_assoc (op \<Oplus>)";

text {*
 \medskip\noindent Semigroups over \isa{(op~{\isasymOtimes})}:
 %term (latex xsymbols symbols) "op \<Otimes>";
*};

consts
  times :: "'a \\<Rightarrow> 'a \\<Rightarrow> 'a"    (infixl "\<Otimes>" 65);
axclass
  times_semigroup < "term"
  assoc: "is_assoc (op \<Otimes>)";

end;
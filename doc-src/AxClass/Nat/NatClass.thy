theory NatClass = FOL:;

consts
  zero :: 'a    ("0")
  Suc :: "'a \\<Rightarrow> 'a"
  rec :: "'a \\<Rightarrow> 'a \\<Rightarrow> ('a \\<Rightarrow> 'a \\<Rightarrow> 'a) \\<Rightarrow> 'a";

axclass
  nat < "term"
  induct:     "P(0) \\<Longrightarrow> (\\<And>x. P(x) \\<Longrightarrow> P(Suc(x))) \\<Longrightarrow> P(n)"
  Suc_inject: "Suc(m) = Suc(n) \\<Longrightarrow> m = n"
  Suc_neq_0:  "Suc(m) = 0 \\<Longrightarrow> R"
  rec_0:      "rec(0, a, f) = a"
  rec_Suc:    "rec(Suc(m), a, f) = f(m, rec(m, a, f))";

constdefs
  add :: "'a::nat \\<Rightarrow> 'a \\<Rightarrow> 'a"    (infixl "+" 60)
  "m + n \\<equiv> rec(m, n, \\<lambda>x y. Suc(y))";

end;
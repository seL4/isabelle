
(***  Section 10.4  ***)

Ex1 = LCF +

consts
  P	:: "'a => tr"
  G	:: "'a => 'a"
  H	:: "'a => 'a"
  K	:: "('a => 'a) => ('a => 'a)"

rules
  P_strict	"P(UU) = UU"
  K		"K = (%h x. P(x) => x | h(h(G(x))))"
  H		"H = FIX(K)"

end

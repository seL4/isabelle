
(***  Example 3.8  ***)

Ex2 = LCF +

consts
  P	:: "'a => tr"
  F	:: "'a => 'a"
  G	:: "'a => 'a"
  H	:: "'a => 'b => 'b"
  K	:: "('a => 'b => 'b) => ('a => 'b => 'b)"

rules
  F_strict	"F(UU) = UU"
  K		"K = (%h x y. P(x) => y | F(h(G(x),y)))"
  H		"H = FIX(K)"

end

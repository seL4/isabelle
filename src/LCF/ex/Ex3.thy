
(*** Addition with fixpoint of successor ***)

Ex3 = LCF +

consts
  s	:: "'a => 'a"
  p	:: "'a => 'a => 'a"

rules
  p_strict	"p(UU) = UU"
  p_s		"p(s(x),y) = s(p(x,y))"

end

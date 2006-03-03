(*  ID:         $Id$

Temporary test of nbe module.
*)

theory nbe
imports Main
begin

(*ML"set Toplevel.timing"*)
norm_by_eval "exp (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) (Suc (Suc  (Suc (Suc (Suc 0)))))"
norm_by_eval "0 + (n::nat)"
norm_by_eval "0 + Suc(n)"
norm_by_eval "Suc(n) + Suc m"
norm_by_eval "[] @ xs"
norm_by_eval "(x#xs) @ ys"
norm_by_eval "[x,y,z] @ [a,b,c]"
norm_by_eval "%(xs, ys). xs @ ys"
norm_by_eval "(%(xs, ys). xs @ ys) ([a, b, c], [d, e, f])"
norm_by_eval "%x. case x of None \<Rightarrow> False | Some y \<Rightarrow> True"
norm_by_eval "map (%x. case x of None \<Rightarrow> False | Some y \<Rightarrow> True) [None, Some ()]"
norm_by_eval "rev [a, b, c]"

end

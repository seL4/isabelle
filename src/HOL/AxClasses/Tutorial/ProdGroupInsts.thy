(*  Title:      HOL/AxClasses/Tutorial/ProdGroupInsts.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Lift constant "<*>" to cartesian products, then prove that the
'functor' "*" maps semigroups into semigroups.
*)

ProdGroupInsts = Prod + Group +

(* direct products of semigroups *)

defs
  prod_prod_def "p <*> q == (fst p <*> fst q, snd p <*> snd q)"

instance
  "*" :: (semigroup, semigroup) semigroup
    {| SIMPSET' (fn ss => simp_tac (ss addsimps [assoc])) 1 |}

end

(*  Title:      HOL/Quot/PER0.thy
    ID:         $Id$
    Author:     Oscar Slotosch
    Copyright   1997 Technische Universitaet Muenchen

Definition of classes per and er for (partial) equivalence classes
The polymorphic constant eqv is only for the definition of PERs
The characteristic constant === (sim) is available on the class per

*)

PER0 = Set + (* partial equivalence relations *)

consts  (* polymorphic constant for (partial) equivalence relations *)
        eqv    :: "'a::term => 'a => bool" 

axclass per < term
	(* axioms for partial equivalence relations *)
        ax_per_trans    "[|eqv x y; eqv y z|] ==> eqv x z"
        ax_per_sym      "eqv x y ==> eqv y x"

axclass er < per
	ax_er_refl	"eqv x x"

consts  (* characteristic constant and Domain for per *)
        "==="     :: "'a::per => 'a => bool" (infixl 55)
        D         :: "'a::per set"
defs
        per_def         "(op ===) == eqv"
        Dom             "D=={x.x===x}"
(* define ==== on and function type => *)
        fun_per_def     "eqv f g == !x y.x:D & y:D & x===y --> f x === g y"

syntax (symbols)
  "op ==="   :: "['a,'a::per] => bool"        (infixl "\\<sim>" 50)

end

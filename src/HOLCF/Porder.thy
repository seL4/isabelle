(*  Title: 	HOLCF/porder.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Definition of class porder (partial order)

The prototype theory for this class is void.thy 

*)

Porder = Void +

(* Introduction of new class. The witness is type void. *)

classes po < term

(* default type is still term ! *)
(* void is the prototype in po *)

arities void :: po

consts	"<<"	::	"['a,'a::po] => bool"	(infixl 55)

	"<|"	::	"['a set,'a::po] => bool"	(infixl 55)
	"<<|"	::	"['a set,'a::po] => bool"	(infixl 55)
	lub	::	"'a set => 'a::po"
	is_tord	::	"'a::po set => bool"
	is_chain ::	"(nat=>'a::po) => bool"
	max_in_chain :: "[nat,nat=>'a::po]=>bool"
	finite_chain :: "(nat=>'a::po)=>bool"

rules

(* class axioms: justification is theory Void *)

refl_less	"x << x"	
				(* witness refl_less_void    *)

antisym_less	"[|x<<y ; y<<x |] ==> x = y"	
				(* witness antisym_less_void *)

trans_less	"[|x<<y ; y<<z |] ==> x<<z"
				(* witness trans_less_void   *)

(* instance of << for the prototype void *)

inst_void_po	"(op <<)::[void,void]=>bool = less_void"

(* class definitions *)

is_ub		"S  <| x == ! y.y:S --> y<<x"
is_lub		"S <<| x == S <| x & (! u. S <| u  --> x << u)"

lub		"lub(S) = (@x. S <<| x)"

(* Arbitrary chains are total orders    *)                  
is_tord		"is_tord(S) == ! x y. x:S & y:S --> (x<<y | y<<x)"


(* Here we use countable chains and I prefer to code them as functions! *)
is_chain	"is_chain(F) == (! i.F(i) << F(Suc(i)))"


(* finite chains, needed for monotony of continouous functions *)

max_in_chain_def "max_in_chain(i,C) == ! j. i <= j --> C(i) = C(j)" 

finite_chain_def "finite_chain(C) == is_chain(C) & (? i. max_in_chain(i,C))"

end 

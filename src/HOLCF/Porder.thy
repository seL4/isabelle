(*  Title:      HOLCF/porder.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Conservative extension of theory Porder0 by constant definitions 

*)

Porder = Porder0 +

consts  
        "<|"    ::      "['a set,'a::po] => bool"       (infixl 55)
        "<<|"   ::      "['a set,'a::po] => bool"       (infixl 55)
        lub     ::      "'a set => 'a::po"
        is_tord ::      "'a::po set => bool"
        is_chain ::     "(nat=>'a::po) => bool"
        max_in_chain :: "[nat,nat=>'a::po]=>bool"
        finite_chain :: "(nat=>'a::po)=>bool"

syntax

  "@LUB"	:: "(('b::term) => 'a) => 'a"	(binder "LUB " 10)

translations

  "LUB x. t"	== "lub(range(%x. t))"

syntax (symbols)

  "LUB "	:: "[idts, 'a] => 'a"		("(3\\<Squnion>_./ _)"[0,10] 10)

defs

(* class definitions *)
is_ub           "S  <| x == ! y. y:S --> y<<x"
is_lub          "S <<| x == S <| x & (! u. S <| u  --> x << u)"

(* Arbitrary chains are total orders    *)                  
is_tord         "is_tord S == ! x y. x:S & y:S --> (x<<y | y<<x)"

(* Here we use countable chains and I prefer to code them as functions! *)
is_chain        "is_chain F == (! i. F(i) << F(Suc(i)))"

(* finite chains, needed for monotony of continouous functions *)
max_in_chain_def "max_in_chain i C == ! j. i <= j --> C(i) = C(j)" 
finite_chain_def "finite_chain C == is_chain(C) & (? i. max_in_chain i C)"

lub_def          "lub S == (@x. S <<| x)"

end 



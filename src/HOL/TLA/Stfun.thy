(* 
    File:	 TLA/Stfun.thy
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    Theory Name: Stfun
    Logic Image: HOL

States and state functions for TLA
*)

Stfun  =  Prod +

types
    state
    'a stfun = "state => 'a"
    stpred   = "bool stfun"

arities
    state :: term

consts
  (* For simplicity, we do not syntactically distinguish between state variables
     and state functions, and treat "state" as an anonymous type. But we need a 
     "meta-predicate" to identify "base" state variables that represent the state
     components of a system, in particular to define the enabledness of actions.
  *)
  base_var  :: "'a stfun => bool"

  (* lift tupling to state functions *)
  pairSF    :: "['a stfun, 'b stfun] => ('a * 'b) stfun"

syntax
  "@tupleSF"     :: "args => ('a * 'b) stfun"  ("(1<_>)")

translations
  "<x,y,z>"   == "<x, <y,z> >"
  "<x,y>"     == "pairSF x y"
  "<x>"       => "x"

rules
  (* tupling *)
  pairSF_def  "<v,w>(s) = (v(s),w(s))"

  (* "base" variables may be assigned arbitrary values by states.
     NB: It's really stronger than that because "u" doesn't depend 
         on either c or v. In particular, if "==>" were replaced
         with "==", base_pair would (still) not be derivable.
  *)
  base_var    "base_var v ==> EX u. v u = c"

  (* a tuple of variables is "base" if each variable is "base" *)
  base_pair   "base_var <v,w> = (base_var v & base_var w)"
end

ML

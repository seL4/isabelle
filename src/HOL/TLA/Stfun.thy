(* 
    File:	 TLA/Stfun.thy
    Author:      Stephan Merz
    Copyright:   1998 University of Munich

    Theory Name: Stfun
    Logic Image: HOL

States and state functions for TLA as an "intensional" logic.
*)

Stfun  =  Intensional +

types
    state
    'a stfun = "state => 'a"
    stpred   = "bool stfun"

arities
  state :: type

instance
  state :: world

consts
  (* Formalizing type "state" would require formulas to be tagged with
     their underlying state space and would result in a system that is
     much harder to use. (Unlike Hoare logic or Unity, TLA has quantification
     over state variables, and therefore one usually works with different
     state spaces within a single specification.) Instead, "state" is just
     an anonymous type whose only purpose is to provide "Skolem" constants.
     Moreover, we do not define a type of state variables separate from that
     of arbitrary state functions, again in order to simplify the definition
     of flexible quantification later on. Nevertheless, we need to distinguish
     state variables, mainly to define the enabledness of actions. The user
     identifies (tuples of) "base" state variables in a specification via the
     "meta predicate" basevars, which is defined here.
  *)
  stvars    :: "'a stfun => bool"

syntax
  "PRED"    :: lift => 'a                          ("PRED _")
  "_stvars" :: lift => bool                        ("basevars _")

translations
  "PRED P"   =>  "(P::state => _)"
  "_stvars"  ==  "stvars"

defs
  (* Base variables may be assigned arbitrary (type-correct) values. 
     Note that vs may be a tuple of variables. The correct identification
     of base variables is up to the user who must take care not to
     introduce an inconsistency. For example, "basevars (x,x)" would
     definitely be inconsistent.
  *)
  basevars_def	"stvars vs == range vs = UNIV"

end

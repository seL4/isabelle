(*  Title:      ZF/ex/PropLog.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Lawrence C Paulson
    Copyright   1993  University of Cambridge

Datatype definition of propositional logic formulae and inductive definition
of the propositional tautologies.
*)

PropLog = Finite + Datatype +

(** The datatype of propositions; note mixfix syntax **)
consts
  prop     :: i

datatype
  "prop" = Fls
         | Var ("n: nat")                       ("#_" [100] 100)
         | "=>" ("p: prop", "q: prop")          (infixr 90)

(** The proof system **)
consts
  thms     :: i => i

syntax
  "|-"     :: [i,i] => o                        (infixl 50)

translations
  "H |- p" == "p : thms(H)"

inductive
  domains "thms(H)" <= "prop"
  intrs
    H  "[| p:H;  p:prop |] ==> H |- p"
    K  "[| p:prop;  q:prop |] ==> H |- p=>q=>p"
    S  "[| p:prop;  q:prop;  r:prop |] ==> H |- (p=>q=>r) => (p=>q) => p=>r"
    DN "p:prop ==> H |- ((p=>Fls) => Fls) => p"
    MP "[| H |- p=>q;  H |- p;  p:prop;  q:prop |] ==> H |- q"
  type_intrs "prop.intrs"


(** The semantics **)
consts
  "|="        :: [i,i] => o                        (infixl 50)
  hyps        :: [i,i] => i
  is_true_fun :: [i,i] => i

constdefs (*this definitionis necessary since predicates can't be recursive*)
  is_true     :: [i,i] => o
    "is_true(p,t) == is_true_fun(p,t)=1"

defs
  (*Logical consequence: for every valuation, if all elements of H are true
     then so is p*)
  logcon_def  "H |= p == ALL t. (ALL q:H. is_true(q,t)) --> is_true(p,t)"

primrec (** A finite set of hypotheses from t and the Vars in p **)
  "hyps(Fls, t)    = 0"
  "hyps(Var(v), t) = (if v:t then {#v} else {#v=>Fls})"
  "hyps(p=>q, t)   = hyps(p,t) Un hyps(q,t)"
 
primrec (** Semantics of propositional logic **)
  "is_true_fun(Fls, t)    = 0"
  "is_true_fun(Var(v), t) = (if v:t then 1 else 0)"
  "is_true_fun(p=>q, t)   = (if is_true_fun(p,t)=1 then is_true_fun(q,t)
			     else 1)"

end

(*  Title:      ZF/ex/PropLog.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Lawrence C Paulson
    Copyright   1993  University of Cambridge

Datatype definition of propositional logic formulae and inductive definition
of the propositional tautologies.
*)

PropLog = Main +

(** The datatype of propositions; note mixfix syntax **)
consts
  prop     :: i

datatype
  "prop" = Fls
         | Var ("n \\<in> nat")                       ("#_" [100] 100)
         | "=>" ("p \\<in> prop", "q \\<in> prop")          (infixr 90)

(** The proof system **)
consts
  thms     :: i => i

syntax
  "|-"     :: [i,i] => o                        (infixl 50)

translations
  "H |- p" == "p \\<in> thms(H)"

inductive
  domains "thms(H)" <= "prop"
  intrs
    H  "[| p \\<in> H;  p \\<in> prop |] ==> H |- p"
    K  "[| p \\<in> prop;  q \\<in> prop |] ==> H |- p=>q=>p"
    S  "[| p \\<in> prop;  q \\<in> prop;  r \\<in> prop |] ==> H |- (p=>q=>r) => (p=>q) => p=>r"
    DN "p \\<in> prop ==> H |- ((p=>Fls) => Fls) => p"
    MP "[| H |- p=>q;  H |- p;  p \\<in> prop;  q \\<in> prop |] ==> H |- q"
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
  logcon_def  "H |= p == \\<forall>t. (\\<forall>q \\<in> H. is_true(q,t)) --> is_true(p,t)"

primrec (** A finite set of hypotheses from t and the Vars in p **)
  "hyps(Fls, t)    = 0"
  "hyps(Var(v), t) = (if v \\<in> t then {#v} else {#v=>Fls})"
  "hyps(p=>q, t)   = hyps(p,t) Un hyps(q,t)"
 
primrec (** Semantics of propositional logic **)
  "is_true_fun(Fls, t)    = 0"
  "is_true_fun(Var(v), t) = (if v \\<in> t then 1 else 0)"
  "is_true_fun(p=>q, t)   = (if is_true_fun(p,t)=1 then is_true_fun(q,t)
			     else 1)"

end

(*  Title: 	ZF/ex/PropLog.thy
    ID:         $Id$
    Author: 	Tobias Nipkow & Lawrence C Paulson
    Copyright   1993  University of Cambridge

Datatype definition of propositional logic formulae and inductive definition
of the propositional tautologies.
*)

PropLog = Finite + Datatype +

(** The datatype of propositions; note mixfix syntax **)
consts
  prop     :: "i"

datatype
  "prop" = Fls
         | Var ("n: nat")	                ("#_" [100] 100)
         | "=>" ("p: prop", "q: prop")		(infixr 90)

(** The proof system **)
consts
  thms     :: "i => i"
  "|-"     :: "[i,i] => o"    			(infixl 50)

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
  prop_rec :: "[i, i, i=>i, [i,i,i,i]=>i] => i"
  is_true  :: "[i,i] => o"
  "|="     :: "[i,i] => o"    			(infixl 50)
  hyps     :: "[i,i] => i"

defs

  prop_rec_def
   "prop_rec(p,b,c,h) == \
\   Vrec(p, %p g.prop_case(b, c, %x y. h(x, y, g`x, g`y), p))"

  (** Semantics of propositional logic **)
  is_true_def
   "is_true(p,t) == prop_rec(p, 0,  %v. if(v:t, 1, 0), \
\                               %p q tp tq. if(tp=1,tq,1))         =  1"

  (*Logical consequence: for every valuation, if all elements of H are true
     then so is p*)
  logcon_def  "H |= p == ALL t. (ALL q:H. is_true(q,t)) --> is_true(p,t)"

  (** A finite set of hypotheses from t and the Vars in p **)
  hyps_def
   "hyps(p,t) == prop_rec(p, 0,  %v. {if(v:t, #v, #v=>Fls)}, \
\                            %p q Hp Hq. Hp Un Hq)"

end

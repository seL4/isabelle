(*  Title: 	ZF/ex/prop-log.thy
    ID:         $Id$
    Author: 	Tobias Nipkow & Lawrence C Paulson
    Copyright   1993  University of Cambridge

Inductive definition of propositional logic.
*)

PropLog = Prop + Fin +
consts
  (*semantics*)
  prop_rec :: "[i, i, i=>i, [i,i,i,i]=>i] => i"
  is_true  :: "[i,i] => o"
  "|="     :: "[i,i] => o"    			(infixl 50)
  hyps     :: "[i,i] => i"

  (*proof theory*)
  thms     :: "i => i"
  "|-"     :: "[i,i] => o"    			(infixl 50)

translations
  "H |- p" == "p : thms(H)"

rules

  prop_rec_def
   "prop_rec(p,b,c,h) == \
\   Vrec(p, %p g.prop_case(b, c, %x y. h(x, y, g`x, g`y), p))"

  (** Semantics of propositional logic **)
  is_true_def
   "is_true(p,t) == prop_rec(p, 0,  %v. if(v:t, 1, 0), \
\                               %p q tp tq. if(tp=1,tq,1))         =  1"

  (*For every valuation, if all elements of H are true then so is p*)
  sat_def     "H |= p == ALL t. (ALL q:H. is_true(q,t)) --> is_true(p,t)"

  (** A finite set of hypotheses from t and the Vars in p **)
  hyps_def
   "hyps(p,t) == prop_rec(p, 0,  %v. {if(v:t, #v, #v=>Fls)}, \
\                            %p q Hp Hq. Hp Un Hq)"

end

(*  Title:      HOL/Lambda/Lambda.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TU Muenchen

Lambda-terms in de Bruijn notation,
substitution and beta-reduction.
*)

Lambda = Datatype +

datatype dB = Var nat | "$" dB dB (infixl 200) | Abs dB

consts
  subst  :: [dB,dB,nat]=>dB ("_[_'/_]" [300,0,0] 300)
  lift   :: [dB,nat] => dB
  (* optimized versions *)
  substn :: [dB,dB,nat] => dB
  liftn  :: [nat,dB,nat] => dB

primrec
  "lift (Var i) k = (if i < k then Var i else Var(i+1))"
  "lift (s $ t) k = (lift s k) $ (lift t k)"
  "lift (Abs s) k = Abs(lift s (k+1))"

primrec
  subst_Var "(Var i)[s/k] = (if k < i then Var(i-1)
                            else if i = k then s else Var i)"
  subst_App "(t $ u)[s/k] = t[s/k] $ u[s/k]"
  subst_Abs "(Abs t)[s/k] = Abs (t[lift s 0 / k+1])"

primrec
  "liftn n (Var i) k = (if i < k then Var i else Var(i+n))"
  "liftn n (s $ t) k = (liftn n s k) $ (liftn n t k)"
  "liftn n (Abs s) k = Abs(liftn n s (k+1))"

primrec
  "substn (Var i) s k = (if k < i then Var(i-1)
                         else if i = k then liftn k s 0 else Var i)"
  "substn (t $ u) s k = (substn t s k) $ (substn u s k)"
  "substn (Abs t) s k = Abs (substn t s (k+1))"

consts  beta :: "(dB * dB) set"

syntax  "->", "->>" :: [dB,dB] => bool (infixl 50)

translations
  "s -> t"  == "(s,t) : beta"
  "s ->> t" == "(s,t) : beta^*"

inductive beta
intrs
   beta  "(Abs s) $ t -> s[t/0]"
   appL  "s -> t ==> s$u -> t$u"
   appR  "s -> t ==> u$s -> u$t"
   abs   "s -> t ==> Abs s -> Abs t"
end

(*  Title:      HOL/Lambda/Lambda.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TU Muenchen

Lambda-terms in de Bruijn notation,
substitution and beta-reduction.
*)

Lambda = Arith +

datatype db = Var nat | "@" db db (infixl 200) | Fun db

consts
  subst  :: [db,db,nat]=>db ("_[_'/_]" [300,0,0] 300)
  lift   :: [db,nat] => db
  (* optimized versions *)
  substn :: [db,db,nat] => db
  liftn  :: [nat,db,nat] => db

primrec lift db
  "lift (Var i) k = (if i < k then Var i else Var(Suc i))"
  "lift (s @ t) k = (lift s k) @ (lift t k)"
  "lift (Fun s) k = Fun(lift s (Suc k))"

primrec subst db
  subst_Var "(Var i)[s/k] = (if k < i then Var(pred i)
                            else if i = k then s else Var i)"
  subst_App "(t @ u)[s/k] = t[s/k] @ u[s/k]"
  subst_Fun "(Fun t)[s/k] = Fun (t[lift s 0 / Suc k])"

primrec liftn db
  "liftn n (Var i) k = (if i < k then Var i else Var(i+n))"
  "liftn n (s @ t) k = (liftn n s k) @ (liftn n t k)"
  "liftn n (Fun s) k = Fun(liftn n s (Suc k))"

primrec substn db
  "substn (Var i) s k = (if k < i then Var(pred i)
                         else if i = k then liftn k s 0 else Var i)"
  "substn (t @ u) s k = (substn t s k) @ (substn u s k)"
  "substn (Fun t) s k = Fun (substn t s (Suc k))"

consts  beta :: "(db * db) set"

syntax  "->", "->>" :: [db,db] => bool (infixl 50)

translations
  "s -> t"  == "(s,t) : beta"
  "s ->> t" == "(s,t) : beta^*"

inductive beta
intrs
   beta  "(Fun s) @ t -> s[t/0]"
   appL  "s -> t ==> s@u -> t@u"
   appR  "s -> t ==> u@s -> u@t"
   abs   "s -> t ==> Fun s -> Fun t"
end

(*  Title:      HOL/Lambda.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TU Muenchen

Lambda-terms in de Bruijn notation,
substitution and beta-reduction.
*)

Lambda = Arith +

datatype db = Var nat | "@" db db (infixl 200) | Fun db

consts
  subst  :: "[db,db,nat]=>db" ("_[_'/_]" [300,0,0] 300)
  lift   :: "[db,nat] => db"

primrec subst db
  subst_Var "(Var i)[s/n] = (if n < i then Var(pred i)
                            else if i = n then s else Var i)"
  subst_App "(t @ u)[s/n] = t[s/n] @ u[s/n]"
  subst_Fun "(Fun t)[s/n] = Fun (t[lift s 0 / Suc n])"

primrec lift db
  lift_Var "lift (Var i) n = (if i < n then Var i else Var(Suc i))"
  lift_App "lift (s @ t) n = (lift s n) @ (lift t n)"
  lift_Fun "lift (Fun s) n = Fun(lift s (Suc n))"

consts  beta :: "(db * db) set"

syntax  "->", "->>" :: "[db,db] => bool" (infixl 50)

translations
  "s -> t"  == "(s,t) : beta"
  "s ->> t" == "(s,t) : beta^*"

inductive "beta"
intrs
   beta  "(Fun s) @ t -> s[t/0]"
   appL  "s -> t ==> s@u -> t@u"
   appR  "s -> t ==> u@s -> u@t"
   abs   "s -> t ==> Fun s -> Fun t"
end

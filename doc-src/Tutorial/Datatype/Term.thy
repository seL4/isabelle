Term = Main +
datatype 'a t = A | B "'a * ('a t list)"
datatype expr = Var string | Lam string expr | App expr expr
              | Data data
and      data = Bool bool | Num nat
              | Closure string expr "(string * data)list"
datatype ('a,'b)term = Var 'a | App 'b ((('a,'b)term)list)
consts
   subst  :: ('a => ('a,'b)term) => ('a,'b)term      => ('a,'b)term
   substs :: ('a => ('a,'b)term) => ('a,'b)term list => ('a,'b)term list
primrec
  "subst s (Var x) = s x"
  "subst s (App f ts) = App f (substs s ts)"
  "substs s [] = []"
  "substs s (t # ts) = subst s t # substs s ts"
end

Term = Main +
datatype
    'a aexp = IF ('a bexp) ('a aexp) ('a aexp)
            | Sum ('a aexp list)
            | Diff ('a aexp) ('a aexp)
            | Var 'a
            | Num nat
and 'a bexp = Less ('a aexp) ('a aexp)
            | And ('a bexp) ('a bexp)
            | Neg ('a bexp)
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

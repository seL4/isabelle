ABexp = Main +
datatype
    'a aexp = IF ('a bexp) ('a aexp) ('a aexp)
            | Sum ('a aexp) ('a aexp)
            | Diff ('a aexp) ('a aexp)
            | Var 'a
            | Num nat
and 'a bexp = Less ('a aexp) ('a aexp)
            | And ('a bexp) ('a bexp)
            | Neg ('a bexp)
consts  evala :: ('a => nat) => 'a aexp => nat
        evalb :: ('a => nat) => 'a bexp => bool
primrec
  "evala env (IF b a1 a2) =
     (if evalb env b then evala env a1 else evala env a2)"
  "evala env (Sum a1 a2) = evala env a1 + evala env a2"
  "evala env (Diff a1 a2) = evala env a1 - evala env a2"
  "evala env (Var v) = env v"
  "evala env (Num n) = n"
  "evalb env (Less a1 a2) = (evala env a1 < evala env a2)"
  "evalb env (And b1 b2) = (evalb env b1 & evalb env b2)"
  "evalb env (Neg b) = (~ evalb env b)"
consts substa :: ('a => 'b aexp) => 'a aexp => 'b aexp
       substb :: ('a => 'b aexp) => 'a bexp => 'b bexp
primrec
  "substa s (IF b a1 a2) =
     IF (substb s b) (substa s a1) (substa s a2)"
  "substa s (Sum a1 a2) = Sum (substa s a1) (substa s a2)"
  "substa s (Diff a1 a2) = Diff (substa s a1) (substa s a2)"
  "substa s (Var v) = s v"
  "substa s (Num n) = Num n"
  "substb s (Less a1 a2) = Less (substa s a1) (substa s a2)"
  "substb s (And b1 b2) = And (substb s b1) (substb s b2)"
  "substb s (Neg b) = Neg (substb s b)"
end

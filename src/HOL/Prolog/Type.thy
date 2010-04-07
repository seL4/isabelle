(*  Title:    HOL/Prolog/Type.thy
    Author:   David von Oheimb (based on a lecture on Lambda Prolog by Nadathur)
*)

header {* Type inference *}

theory Type
imports Func
begin

typedecl ty

consts
  bool    :: ty
  nat     :: ty
  arrow   :: "ty => ty => ty"       (infixr "->" 20)
  typeof  :: "[tm, ty] => bool"
  anyterm :: tm

axioms  common_typeof:   "
typeof (app M N) B       :- typeof M (A -> B) & typeof N A..

typeof (cond C L R) A :- typeof C bool & typeof L A & typeof R A..
typeof (fix F)   A       :- (!x. typeof x A => typeof (F  x) A)..

typeof true  bool..
typeof false bool..
typeof (M and N) bool :- typeof M bool & typeof N bool..

typeof (M eq  N) bool :- typeof M T    & typeof N T   ..

typeof  Z    nat..
typeof (S N) nat :- typeof N nat..
typeof (M + N) nat :- typeof M nat & typeof N nat..
typeof (M - N) nat :- typeof M nat & typeof N nat..
typeof (M * N) nat :- typeof M nat & typeof N nat"

axioms good_typeof:     "
typeof (abs Bo) (A -> B) :- (!x. typeof x A => typeof (Bo x) B)"

axioms bad1_typeof:     "
typeof (abs Bo) (A -> B) :- (typeof varterm A => typeof (Bo varterm) B)"

axioms bad2_typeof:     "
typeof (abs Bo) (A -> B) :- (typeof anyterm A => typeof (Bo anyterm) B)"


lemmas prog_Type = prog_Func good_typeof common_typeof

lemma "typeof (abs(%n. abs(%m. abs(%p. p and (n eq m))))) ?T"
  apply (prolog prog_Type)
  done

lemma "typeof (fix (%x. x)) ?T"
  apply (prolog prog_Type)
  done

lemma "typeof (fix (%fact. abs(%n. (app fact (n - Z))))) ?T"
  apply (prolog prog_Type)
  done

lemma "typeof (fix (%fact. abs(%n. cond (n eq Z) (S Z)
  (n * (app fact (n - (S Z))))))) ?T"
  apply (prolog prog_Type)
  done

lemma "typeof (abs(%v. Z)) ?T" (*correct only solution (?A1 -> nat) *)
  apply (prolog prog_Type)
  done

lemma "typeof (abs(%v. Z)) ?T"
  apply (prolog bad1_typeof common_typeof) (* 1st result ok*)
  done

lemma "typeof (abs(%v. Z)) ?T"
  apply (prolog bad1_typeof common_typeof)
  back (* 2nd result (?A1 -> ?A1) wrong *)
  done

lemma "typeof (abs(%v. abs(%v. app v v))) ?T"
  apply (prolog prog_Type)?  (*correctly fails*)
  oops

lemma "typeof (abs(%v. abs(%v. app v v))) ?T"
  apply (prolog bad2_typeof common_typeof) (* wrong result ((?A3 -> ?B3) -> ?A3 -> ?B3)*)
  done

end

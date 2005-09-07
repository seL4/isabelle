(*  Title:    HOL/Prolog/Type.thy
    ID:       $Id$
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
  "->"    :: "ty => ty => ty"       (infixr 20)
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

ML {* use_legacy_bindings (the_context ()) *}

end

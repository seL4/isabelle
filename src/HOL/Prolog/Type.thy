(*  Title:    HOL/Prolog/Type.thy
    Author:   David von Oheimb (based on a lecture on Lambda Prolog by Nadathur)
*)

section \<open>Type inference\<close>

theory Type
imports Func
begin

typedecl ty

axiomatization
  bool    :: ty and
  nat     :: ty and
  arrow   :: "ty \<Rightarrow> ty \<Rightarrow> ty"       (infixr \<open>->\<close> 20) and
  typeof  :: "[tm, ty] \<Rightarrow> bool" and
  anyterm :: tm
where common_typeof:   "
typeof (app M N) B       :- typeof M (A -> B) \<and> typeof N A..

typeof (cond C L R) A :- typeof C bool \<and> typeof L A \<and> typeof R A..
typeof (fix F)   A       :- (\<forall>x. typeof x A => typeof (F  x) A)..

typeof true  bool..
typeof false bool..
typeof (M and N) bool :- typeof M bool & typeof N bool..

typeof (M eq  N) bool :- typeof M T    & typeof N T   ..

typeof  Z    nat..
typeof (S N) nat :- typeof N nat..
typeof (M + N) nat :- typeof M nat & typeof N nat..
typeof (M - N) nat :- typeof M nat & typeof N nat..
typeof (M * N) nat :- typeof M nat & typeof N nat"

axiomatization where good_typeof:     "
typeof (abs Bo) (A -> B) :- (\<forall>x. typeof x A => typeof (Bo x) B)"

axiomatization where bad1_typeof:     "
typeof (abs Bo) (A -> B) :- (typeof varterm A => typeof (Bo varterm) B)"

axiomatization where bad2_typeof:     "
typeof (abs Bo) (A -> B) :- (typeof anyterm A => typeof (Bo anyterm) B)"


lemmas prog_Type = prog_Func good_typeof common_typeof

schematic_goal "typeof (abs(%n. abs(%m. abs(%p. p and (n eq m))))) ?T"
  apply (prolog prog_Type)
  done

schematic_goal "typeof (fix (%x. x)) ?T"
  apply (prolog prog_Type)
  done

schematic_goal "typeof (fix (%fact. abs(%n. (app fact (n - Z))))) ?T"
  apply (prolog prog_Type)
  done

schematic_goal "typeof (fix (%fact. abs(%n. cond (n eq Z) (S Z)
  (n * (app fact (n - (S Z))))))) ?T"
  apply (prolog prog_Type)
  done

schematic_goal "typeof (abs(%v. Z)) ?T" (*correct only solution (?A1 -> nat) *)
  apply (prolog prog_Type)
  done

schematic_goal "typeof (abs(%v. Z)) ?T"
  apply (prolog bad1_typeof common_typeof) (* 1st result ok*)
  done

schematic_goal "typeof (abs(%v. Z)) ?T"
  apply (prolog bad1_typeof common_typeof)
  back (* 2nd result (?A1 -> ?A1) wrong *)
  done

schematic_goal "typeof (abs(%v. abs(%v. app v v))) ?T"
  apply (prolog prog_Type)?  (*correctly fails*)
  oops

schematic_goal "typeof (abs(%v. abs(%v. app v v))) ?T"
  apply (prolog bad2_typeof common_typeof) (* wrong result ((?A3 -> ?B3) -> ?A3 -> ?B3)*)
  done

end

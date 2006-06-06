(*  Title:      HOL/IMPP/EvenOdd.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 TUM
*)

header {* Example of mutually recursive procedures verified with Hoare logic *}

theory EvenOdd
imports Misc
begin

constdefs
  even :: "nat => bool"
  "even n == 2 dvd n"

consts
  Even :: pname
  Odd :: pname
axioms
  Even_neq_Odd: "Even ~= Odd"
  Arg_neq_Res:  "Arg  ~= Res"

constdefs
  evn :: com
 "evn == IF (%s. s<Arg> = 0)
         THEN Loc Res:==(%s. 0)
         ELSE(Loc Res:=CALL Odd(%s. s<Arg> - 1);;
              Loc Arg:=CALL Odd(%s. s<Arg> - 1);;
              Loc Res:==(%s. s<Res> * s<Arg>))"
  odd :: com
 "odd == IF (%s. s<Arg> = 0)
         THEN Loc Res:==(%s. 1)
         ELSE(Loc Res:=CALL Even (%s. s<Arg> - 1))"

defs
  bodies_def: "bodies == [(Even,evn),(Odd,odd)]"

consts
  Z_eq_Arg_plus   :: "nat => nat assn" ("Z=Arg+_" [50]50)
 "even_Z=(Res=0)" ::        "nat assn" ("Res'_ok")
defs
  Z_eq_Arg_plus_def: "Z=Arg+n == %Z s.      Z =  s<Arg>+n"
  Res_ok_def:       "Res_ok   == %Z s. even Z = (s<Res> = 0)"


subsection "even"

lemma even_0 [simp]: "even 0"
apply (unfold even_def)
apply simp
done

lemma not_even_1 [simp]: "even (Suc 0) = False"
apply (unfold even_def)
apply simp
done

lemma even_step [simp]: "even (Suc (Suc n)) = even n"
apply (unfold even_def)
apply (subgoal_tac "Suc (Suc n) = n+2")
prefer 2
apply  simp
apply (erule ssubst)
apply (rule dvd_reduce)
done


subsection "Arg, Res"

declare Arg_neq_Res [simp] Arg_neq_Res [THEN not_sym, simp]
declare Even_neq_Odd [simp] Even_neq_Odd [THEN not_sym, simp]

lemma Z_eq_Arg_plus_def2: "(Z=Arg+n) Z s = (Z = s<Arg>+n)"
apply (unfold Z_eq_Arg_plus_def)
apply (rule refl)
done

lemma Res_ok_def2: "Res_ok Z s = (even Z = (s<Res> = 0))"
apply (unfold Res_ok_def)
apply (rule refl)
done

lemmas Arg_Res_simps = Z_eq_Arg_plus_def2 Res_ok_def2

lemma body_Odd [simp]: "body Odd = Some odd"
apply (unfold body_def bodies_def)
apply auto
done

lemma body_Even [simp]: "body Even = Some evn"
apply (unfold body_def bodies_def)
apply auto
done


subsection "verification"

lemma Odd_lemma: "{{Z=Arg+0}. BODY Even .{Res_ok}}|-{Z=Arg+Suc 0}. odd .{Res_ok}"
apply (unfold odd_def)
apply (rule hoare_derivs.If)
apply (rule hoare_derivs.Ass [THEN conseq1])
apply  (clarsimp simp: Arg_Res_simps)
apply (rule export_s)
apply (rule hoare_derivs.Call [THEN conseq1])
apply  (rule_tac P = "Z=Arg+Suc (Suc 0) " in conseq12)
apply (rule single_asm)
apply (auto simp: Arg_Res_simps)
done

lemma Even_lemma: "{{Z=Arg+1}. BODY Odd .{Res_ok}}|-{Z=Arg+0}. evn .{Res_ok}"
apply (unfold evn_def)
apply (rule hoare_derivs.If)
apply (rule hoare_derivs.Ass [THEN conseq1])
apply  (clarsimp simp: Arg_Res_simps)
apply (rule hoare_derivs.Comp)
apply (rule_tac [2] hoare_derivs.Ass)
apply clarsimp
apply (rule_tac Q = "%Z s. ?P Z s & Res_ok Z s" in hoare_derivs.Comp)
apply (rule export_s)
apply  (rule_tac I1 = "%Z l. Z = l Arg & 0 < Z" and Q1 = "Res_ok" in Call_invariant [THEN conseq12])
apply (rule single_asm [THEN conseq2])
apply   (clarsimp simp: Arg_Res_simps)
apply  (force simp: Arg_Res_simps)
apply (rule export_s)
apply (rule_tac I1 = "%Z l. even Z = (l Res = 0) " and Q1 = "%Z s. even Z = (s<Arg> = 0) " in Call_invariant [THEN conseq12])
apply (rule single_asm [THEN conseq2])
apply  (clarsimp simp: Arg_Res_simps)
apply (force simp: Arg_Res_simps)
done


lemma Even_ok_N: "{}|-{Z=Arg+0}. BODY Even .{Res_ok}"
apply (rule BodyN)
apply (simp (no_asm))
apply (rule Even_lemma [THEN hoare_derivs.cut])
apply (rule BodyN)
apply (simp (no_asm))
apply (rule Odd_lemma [THEN thin])
apply (simp (no_asm))
done

lemma Even_ok_S: "{}|-{Z=Arg+0}. BODY Even .{Res_ok}"
apply (rule conseq1)
apply  (rule_tac Procs = "{Odd, Even}" and pn = "Even" and P = "%pn. Z=Arg+ (if pn = Odd then 1 else 0) " and Q = "%pn. Res_ok" in Body1)
apply    auto
apply (rule hoare_derivs.insert)
apply (rule Odd_lemma [THEN thin])
apply  (simp (no_asm))
apply (rule Even_lemma [THEN thin])
apply (simp (no_asm))
done

end

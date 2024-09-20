(*  Title:      HOL/IMPP/EvenOdd.thy
    Author:     David von Oheimb, TUM
*)

section \<open>Example of mutually recursive procedures verified with Hoare logic\<close>

theory EvenOdd
imports Main Misc
begin

axiomatization
  Even :: pname and
  Odd :: pname
where
  Even_neq_Odd: "Even ~= Odd" and
  Arg_neq_Res:  "Arg  ~= Res"

definition
  evn :: com where
 "evn = (IF (%s. s<Arg> = 0)
         THEN Loc Res:==(%s. 0)
         ELSE(Loc Res:=CALL Odd(%s. s<Arg> - 1);;
              Loc Arg:=CALL Odd(%s. s<Arg> - 1);;
              Loc Res:==(%s. s<Res> * s<Arg>)))"

definition
  odd :: com where
 "odd = (IF (%s. s<Arg> = 0)
         THEN Loc Res:==(%s. 1)
         ELSE(Loc Res:=CALL Even (%s. s<Arg> - 1)))"

overloading bodies \<equiv> bodies
begin
  definition "bodies == [(Even,evn),(Odd,odd)]"
end

definition
  Z_eq_Arg_plus :: "nat => nat assn" (\<open>Z=Arg+_\<close> [50]50) where
  "Z=Arg+n = (%Z s.      Z =  s<Arg>+n)"

definition
  Res_ok :: "nat assn" where
  "Res_ok = (%Z s. even Z = (s<Res> = 0))"


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
apply (rule_tac Q = "%Z s. P Z s & Res_ok Z s" and P = P for P in hoare_derivs.Comp)
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

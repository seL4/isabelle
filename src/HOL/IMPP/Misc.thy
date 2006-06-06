(*  Title:      HOL/IMPP/Misc.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 TUM
*)

header {* Several examples for Hoare logic *}

theory Misc
imports Hoare
begin

defs
  newlocs_def: "newlocs       == %x. arbitrary"
  setlocs_def: "setlocs s l'  == case s of st g l => st g l'"
  getlocs_def: "getlocs s     == case s of st g l => l"
   update_def: "update s vn v == case vn of
                               Glb gn => (case s of st g l => st (g(gn:=v)) l)
                             | Loc ln => (case s of st g l => st g (l(ln:=v)))"


subsection "state access"

lemma getlocs_def2: "getlocs (st g l) = l"
apply (unfold getlocs_def)
apply simp
done

lemma update_Loc_idem2 [simp]: "s[Loc Y::=s<Y>] = s"
apply (unfold update_def)
apply (induct_tac s)
apply (simp add: getlocs_def2)
done

lemma update_overwrt [simp]: "s[X::=x][X::=y] = s[X::=y]"
apply (unfold update_def)
apply (induct_tac X)
apply  auto
apply  (induct_tac [!] s)
apply  auto
done

lemma getlocs_Loc_update [simp]: "(s[Loc Y::=k])<Y'> = (if Y=Y' then k else s<Y'>)"
apply (unfold update_def)
apply (induct_tac s)
apply (simp add: getlocs_def2)
done

lemma getlocs_Glb_update [simp]: "getlocs (s[Glb Y::=k]) = getlocs s"
apply (unfold update_def)
apply (induct_tac s)
apply (simp add: getlocs_def2)
done

lemma getlocs_setlocs [simp]: "getlocs (setlocs s l) = l"
apply (unfold setlocs_def)
apply (induct_tac s)
apply auto
apply (simp add: getlocs_def2)
done

lemma getlocs_setlocs_lemma: "getlocs (setlocs s (getlocs s')[Y::=k]) = getlocs (s'[Y::=k])"
apply (induct_tac Y)
apply (rule_tac [2] ext)
apply auto
done

(*unused*)
lemma classic_Local_valid: 
"!v. G|={%Z s. P Z (s[Loc Y::=v]) & s<Y> = a (s[Loc Y::=v])}.  
  c .{%Z s. Q Z (s[Loc Y::=v])} ==> G|={P}. LOCAL Y:=a IN c .{Q}"
apply (unfold hoare_valids_def)
apply (simp (no_asm_use) add: triple_valid_def2)
apply clarsimp
apply (drule_tac x = "s<Y>" in spec)
apply (tactic "smp_tac 1 1")
apply (drule spec)
apply (drule_tac x = "s[Loc Y::=a s]" in spec)
apply (simp (no_asm_use))
apply (erule (1) notE impE)
apply (tactic "smp_tac 1 1")
apply simp
done

lemma classic_Local: "!v. G|-{%Z s. P Z (s[Loc Y::=v]) & s<Y> = a (s[Loc Y::=v])}.  
  c .{%Z s. Q Z (s[Loc Y::=v])} ==> G|-{P}. LOCAL Y:=a IN c .{Q}"
apply (rule export_s)
(*variant 1*)
apply (rule hoare_derivs.Local [THEN conseq1])
apply (erule spec)
apply force
(*variant 2
by (res_inst_tac [("P'","%Z s. s' = s & P Z (s[Loc Y::=a s][Loc Y::=s'<Y>]) & (s[Loc Y::=a s])<Y> = a (s[Loc Y::=a s][Loc Y::=s'<Y>])")] conseq1 1)
by  (Clarsimp_tac 2);
by (rtac hoare_derivs.Local 1);
by (etac spec 1);
*)
done

lemma classic_Local_indep: "[| Y~=Y'; G|-{P}. c .{%Z s. s<Y'> = d} |] ==>  
  G|-{%Z s. P Z (s[Loc Y::=a s])}. LOCAL Y:=a IN c .{%Z s. s<Y'> = d}"
apply (rule classic_Local)
apply clarsimp
apply (erule conseq12)
apply clarsimp
apply (drule sym)
apply simp
done

lemma Local_indep: "[| Y~=Y'; G|-{P}. c .{%Z s. s<Y'> = d} |] ==>  
  G|-{%Z s. P Z (s[Loc Y::=a s])}. LOCAL Y:=a IN c .{%Z s. s<Y'> = d}"
apply (rule export_s)
apply (rule hoare_derivs.Local)
apply clarsimp
done

lemma weak_Local_indep: "[| Y'~=Y; G|-{P}. c .{%Z s. s<Y'> = d} |] ==>  
  G|-{%Z s. P Z (s[Loc Y::=a s])}. LOCAL Y:=a IN c .{%Z s. s<Y'> = d}"
apply (rule weak_Local)
apply auto
done


lemma export_Local_invariant: "G|-{%Z s. Z = s<Y>}. LOCAL Y:=a IN c .{%Z s. Z = s<Y>}"
apply (rule export_s)
apply (rule_tac P' = "%Z s. s'=s & True" and Q' = "%Z s. s'<Y> = s<Y>" in conseq12)
prefer 2
apply  clarsimp
apply (rule hoare_derivs.Local)
apply clarsimp
apply (rule trueI)
done

lemma classic_Local_invariant: "G|-{%Z s. Z = s<Y>}. LOCAL Y:=a IN c .{%Z s. Z = s<Y>}"
apply (rule classic_Local)
apply clarsimp
apply (rule trueI [THEN conseq12])
apply clarsimp
done

lemma Call_invariant: "G|-{P}. BODY pn .{%Z s. Q Z (setlocs s (getlocs s')[X::=s<Res>])} ==>  
  G|-{%Z s. s'=s & I Z (getlocs (s[X::=k Z])) & P Z (setlocs s newlocs[Loc Arg::=a s])}.  
  X:=CALL pn (a) .{%Z s. I Z (getlocs (s[X::=k Z])) & Q Z s}"
apply (rule_tac s'1 = "s'" and
  Q' = "%Z s. I Z (getlocs (s[X::=k Z])) = I Z (getlocs (s'[X::=k Z])) & Q Z s" in
  hoare_derivs.Call [THEN conseq12])
apply  (simp (no_asm_simp) add: getlocs_setlocs_lemma)
apply force
done

end

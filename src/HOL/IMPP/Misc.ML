(*  Title:      HOL/IMPP/Misc.ML
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 TUM
*)

section "state access";

Goalw [getlocs_def] "getlocs (st g l) = l";
by (Simp_tac 1);
qed "getlocs_def2";

Goalw [update_def] "s[Loc Y::=s<Y>] = s";
by (induct_tac "s" 1);
by (simp_tac (simpset() addsimps [getlocs_def2]) 1);
br ext 1;
by (Simp_tac 1);
qed "update_Loc_idem2";
Addsimps[update_Loc_idem2];

Goalw [update_def] "s[X::=x][X::=y] = s[X::=y]";
by (induct_tac "X" 1);
by  Auto_tac;
by  (ALLGOALS (induct_tac "s"));
by  Auto_tac;
by  (ALLGOALS (rtac ext));
by  Auto_tac;
qed "update_overwrt";
Addsimps[update_overwrt];

Goalw [update_def]"(s[Loc Y::=k])<Y'> = (if Y=Y' then k else s<Y'>)";
by (induct_tac "s" 1);
by (simp_tac (simpset() addsimps [getlocs_def2]) 1);
qed "getlocs_Loc_update";
Addsimps[getlocs_Loc_update];

Goalw [update_def] "getlocs (s[Glb Y::=k]) = getlocs s";
by (induct_tac "s" 1);
by (simp_tac (simpset() addsimps [getlocs_def2]) 1);
qed "getlocs_Glb_update";
Addsimps[getlocs_Glb_update];

Goalw [setlocs_def] "getlocs (setlocs s l) = l";
by (induct_tac "s" 1);
by Auto_tac;
by (simp_tac (simpset() addsimps [getlocs_def2]) 1);
qed "getlocs_setlocs";
Addsimps[getlocs_setlocs];

Goal "getlocs (setlocs s (getlocs s')[Y::=k]) = getlocs (s'[Y::=k])";
by (induct_tac "Y" 1);
br ext 2;
by Auto_tac;
qed "getlocs_setlocs_lemma";

(*unused*)
Goalw [hoare_valids_def] 
"!v. G|={%Z s. P Z (s[Loc Y::=v]) & s<Y> = a (s[Loc Y::=v])}. \
\ c .{%Z s. Q Z (s[Loc Y::=v])} ==> G|={P}. LOCAL Y:=a IN c .{Q}";
by (full_simp_tac (simpset() addsimps [triple_valid_def2]) 1);
by (Clarsimp_tac 1);
by (dres_inst_tac [("x","s<Y>")] spec 1);
by (smp_tac 1 1);
bd spec 1;
by (dres_inst_tac [("x","s[Loc Y::=a s]")] spec 1);
by (Full_simp_tac 1);
by (mp_tac 1);
by (smp_tac 1 1);
by (Simp_tac 1);
qed "classic_Local_valid";

Goal "!v. G|-{%Z s. P Z (s[Loc Y::=v]) & s<Y> = a (s[Loc Y::=v])}. \
\ c .{%Z s. Q Z (s[Loc Y::=v])} ==> G|-{P}. LOCAL Y:=a IN c .{Q}";
br export_s 1;
(*variant 1*)
br (hoare_derivs.Local RS conseq1) 1;
be  spec 1;
by (Force_tac 1);
(*variant 2
by (res_inst_tac [("P'","%Z s. s' = s & P Z (s[Loc Y::=a s][Loc Y::=s'<Y>]) & (s[Loc Y::=a s])<Y> = a (s[Loc Y::=a s][Loc Y::=s'<Y>])")] conseq1 1);
by  (Clarsimp_tac 2);
br hoare_derivs.Local 1;
be spec 1;
*)
qed "classic_Local";

Goal "[| Y~=Y'; G|-{P}. c .{%Z s. s<Y'>=d} |] ==> \
\ G|-{%Z s. P Z (s[Loc Y::=a s])}. LOCAL Y:=a IN c .{%Z s. s<Y'>=d}";
br classic_Local 1;
by (ALLGOALS Clarsimp_tac);
be conseq12 1;
by (Clarsimp_tac 1);
bd sym 1;
by (Asm_full_simp_tac 1);
qed "classic_Local_indep";

Goal "[| Y~=Y'; G|-{P}. c .{%Z s. s<Y'>=d} |] ==> \
\ G|-{%Z s. P Z (s[Loc Y::=a s])}. LOCAL Y:=a IN c .{%Z s. s<Y'>=d}";
br export_s 1;
br hoare_derivs.Local 1;
by (Clarsimp_tac 1);
qed "Local_indep";

Goal "[| Y'~=Y; G|-{P}. c .{%Z s. s<Y'>=d} |] ==> \
\ G|-{%Z s. P Z (s[Loc Y::=a s])}. LOCAL Y:=a IN c .{%Z s. s<Y'>=d}";
br weak_Local 1;
by (ALLGOALS Clarsimp_tac);
qed "weak_Local_indep";


Goal "G|-{%Z s. Z = s<Y>}. LOCAL Y:=a IN c .{%Z s. Z = s<Y>}";
br export_s 1;
by (res_inst_tac [("P'","%Z s. s'=s & True"), ("Q'","%Z s. s'<Y> = s<Y>")] (conseq12) 1);
by  (Clarsimp_tac 2);
br hoare_derivs.Local 1;
by (Clarsimp_tac 1);
br trueI 1;
qed "export_Local_invariant";

Goal "G|-{%Z s. Z = s<Y>}. LOCAL Y:=a IN c .{%Z s. Z = s<Y>}";
br classic_Local 1;
by (Clarsimp_tac 1);
br (trueI RS conseq12) 1;
by (Clarsimp_tac 1);
qed "classic_Local_invariant";

Goal "G|-{P}. BODY pn .{%Z s. Q Z (setlocs s (getlocs s')[X::=s<Res>])} ==> \
\ G|-{%Z s. s'=s & I Z (getlocs (s[X::=k Z])) & P Z (setlocs s newlocs[Loc Arg::=a s])}. \
\ X:=CALL pn (a) .{%Z s. I Z (getlocs (s[X::=k Z])) & Q Z s}";
by (res_inst_tac [("s'1","s'"),("Q'","%Z s. I Z (getlocs (s[X::=k Z])) = I Z (getlocs (s'[X::=k Z])) & Q Z s")] (hoare_derivs.Call RS conseq12) 1);
by  (asm_simp_tac  (simpset() addsimps [getlocs_setlocs_lemma]) 1);
by (Force_tac 1);
qed "Call_invariant";



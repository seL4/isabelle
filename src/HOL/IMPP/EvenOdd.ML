(*  Title:      HOL/IMPP/EvenOdd.ML
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 TUM
*)

section "even"; 

Goalw [even_def] "even 0";
by (Simp_tac 1);
qed "even_0";
Addsimps [even_0];

Goalw [even_def] "even 1 = False";
by (Clarsimp_tac 1);
bd dvd_imp_le 1;
by Auto_tac;
qed "not_even_1";
Addsimps [not_even_1];

Goalw [even_def] "even (Suc (Suc n)) = even n";
by (subgoal_tac "Suc (Suc n) = n+2" 1);
by  (Simp_tac 2);
be ssubst 1;
br dvd_reduce 1;
qed "even_step";
Addsimps[even_step];


section "Arg, Res";

Addsimps[Arg_neq_Res,Arg_neq_Res RS not_sym];
Addsimps[Even_neq_Odd, Even_neq_Odd RS not_sym];

Goalw [Z_eq_Arg_plus_def] "(Z=Arg+n) Z s = (Z = s<Arg>+n)";
br refl 1;
qed "Z_eq_Arg_plus_def2";

Goalw [Res_ok_def] "Res_ok Z s = (even Z = (s<Res> = 0))";
br refl 1;
qed "Res_ok_def2";

val Arg_Res_css = (claset(),simpset()addsimps[Z_eq_Arg_plus_def2,Res_ok_def2]);

Goalw [body_def, bodies_def] "body Odd = Some odd";
by Auto_tac;
qed "body_Odd";
Goalw [body_def, bodies_def] "body Even = Some evn";
by Auto_tac;
qed "body_Even";
Addsimps[body_Odd, body_Even];

section "verification";

Goalw [odd_def] "{{Z=Arg+0}. BODY Even .{Res_ok}}|-{Z=Arg+1}. odd .{Res_ok}";
br hoare_derivs.If 1;
br  (hoare_derivs.Ass RS conseq1) 1;
by  (clarsimp_tac Arg_Res_css 1);
br export_s 1;
br (hoare_derivs.Call RS conseq1) 1;
by  (res_inst_tac [("P","Z=Arg+2")] conseq12 1);
br   single_asm 1;
by (auto_tac Arg_Res_css);
qed "Odd_lemma";

Goalw [evn_def] "{{Z=Arg+1}. BODY Odd .{Res_ok}}|-{Z=Arg+0}. evn .{Res_ok}";
br hoare_derivs.If 1;
br  (hoare_derivs.Ass RS conseq1) 1;
by  (clarsimp_tac Arg_Res_css 1);
br hoare_derivs.Comp 1;
br  hoare_derivs.Ass 2;
by (Clarsimp_tac 1);
by (res_inst_tac [("Q","%Z s. ?P Z s & Res_ok Z s")] hoare_derivs.Comp 1);
br  export_s 1;
by  (res_inst_tac [("I1","%Z l. Z = l Arg & 0 < Z"),
		   ("Q1","Res_ok")] (Call_invariant RS conseq12) 1);
br   (single_asm RS conseq2) 1;
by   (clarsimp_tac Arg_Res_css 1);
by  (force_tac Arg_Res_css 1);
br export_s 1;
by (res_inst_tac [("I1","%Z l. even Z = (l Res = 0)"),
		  ("Q1","%Z s. even Z = (s<Arg>=0)")]
		 (Call_invariant RS conseq12) 1);
br  (single_asm RS conseq2) 1;
by  (clarsimp_tac Arg_Res_css 1);
by (force_tac Arg_Res_css 1);
qed "Even_lemma";


Goal "{}|-{Z=Arg+0}. BODY Even .{Res_ok}";
br BodyN 1;
by (Simp_tac 1);
br (Even_lemma RS hoare_derivs.cut) 1;
br BodyN 1;
by (Simp_tac 1);
br (Odd_lemma RS thin) 1;
by (Simp_tac 1);
qed "Even_ok_N";

Goal "{}|-{Z=Arg+0}. BODY Even .{Res_ok}";
br conseq1 1;
by  (res_inst_tac [("Procs","{Odd, Even}"), ("pn","Even"), 
      ("P","%pn. Z=Arg+(if pn = Odd then 1 else 0)"),
      ("Q","%pn. Res_ok")] Body1 1);
by    Auto_tac;
br hoare_derivs.insert 1;
br  (Odd_lemma RS thin) 1;
by  (Simp_tac 1);
br (Even_lemma RS thin) 1;
by (Simp_tac 1);
qed "Even_ok_S";

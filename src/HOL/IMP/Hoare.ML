(*  Title: 	HOL/IMP/Hoare.ML
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1995 TUM

Soundness of Hoare rules wrt denotational semantics
*)

open Hoare;

goalw Hoare.thy [spec_def] "!P c Q. ({{P}}c{{Q}}) --> spec P c Q";
br hoare.mutual_induct 1;
    by(ALLGOALS Asm_simp_tac);
  by(fast_tac rel_cs 1);
 by(fast_tac HOL_cs 1);
br allI 1;
br allI 1;
br impI 1;
be induct2 1;
 br Gamma_mono 1;
by (rewrite_goals_tac [Gamma_def]);  
by(eres_inst_tac [("x","a")] allE 1);
by (safe_tac comp_cs);
  by(ALLGOALS Asm_full_simp_tac);
qed "hoare_sound";

(*
fun while_tac inv ss i =
  EVERY[res_inst_tac[("P",inv)] hoare_conseq i, atac i, rtac hoare_while i,
        asm_full_simp_tac ss (i+1)];

fun assign_tac ss = EVERY'[rtac hoare_assign, simp_tac ss,
                           TRY o (strip_tac THEN' atac)];

fun hoare_tac ss =
  REPEAT(STATE(fn th => FIRST'[rtac hoare_seq, assign_tac ss] (nprems_of th)));

(* example *)
val prems = goal Hoare.thy
  "[| u ~= y; u ~= z; y ~= z |] ==> \
\  {{%s.s(x)=i & s(y)=j}} \
\  z := X x; (u := N 0; \
\  while noti(ROp op = (X u) (X y)) \
\             do (u := Op1 Suc (X u); z := Op1 Suc (X z))) \
\  {{%s. s(z)=i+j}}";
val ss = !simpset addsimps (eq_sym_conv::assign_def::prems);
by(hoare_tac ss);
by(while_tac "%s.s z = i + s u & s y = j" ss 3);
by(hoare_tac ss);
result();
*)

(*  Title: 	HOL/IMP/Hoare.ML
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1995 TUM

Derivation of Hoare rules
*)

open Hoare;

Unify.trace_bound := 30;
Unify.search_bound := 30;

goalw Hoare.thy [spec_def]
  "!!P.[| !s. P' s --> P s; {{P}}c{{Q}}; !s. Q s --> Q' s |] \
\  ==> {{P'}}c{{Q'}}";
by(fast_tac HOL_cs 1);
bind_thm("hoare_conseq", impI RSN (3,allI RSN (3,impI RS allI RS result())));

goalw Hoare.thy (spec_def::C_simps)  "{{P}} skip {{P}}";
by(fast_tac comp_cs 1);
qed"hoare_skip";

goalw Hoare.thy (spec_def::C_simps)
  "!!P. [| !s. P s --> Q(s[A a s/x]) |] ==> {{P}} x := a {{Q}}";
by(asm_full_simp_tac prod_ss 1);
qed"hoare_assign";

goalw Hoare.thy (spec_def::C_simps)
  "!!P. [| {{P}} c {{Q}}; {{Q}} d {{R}} |] ==> {{P}} c;d {{R}}";
by(fast_tac comp_cs 1);
qed"hoare_seq";

goalw Hoare.thy (spec_def::C_simps)
  "!!P. [| {{%s. P s & B b s}} c {{Q}}; {{%s. P s & ~B b s}} d {{Q}} |] ==> \
\  {{P}} ifc b then c else d {{Q}}";
by(simp_tac prod_ss 1);
by(fast_tac comp_cs 1);
qed"hoare_if";

val major::prems = goal Hoare.thy
  "[| (a,b) :lfp f; mono f; \
\     !!a b. (a,b) : f(lfp f Int Collect(split P)) ==> P a b |] ==> P a b";
by(res_inst_tac [("c1","P")] (split RS subst) 1);
br (major RS induct) 1;
brs prems 1;
by(res_inst_tac[("p","x")]PairE 1);
by(hyp_subst_tac 1);
by(asm_simp_tac (prod_ss addsimps prems) 1);
qed"induct2";

goalw Hoare.thy (spec_def::C_simps)
  "!!P. [| {{%s. P s & B b s}} c {{P}} |] ==> \
\  {{P}} while b do c {{%s. P s & ~B b s}}";
br allI 1;
br allI 1;
br impI 1;
be induct2 1;
br Gamma_mono 1;
by (rewrite_goals_tac [Gamma_def]);  
by(eres_inst_tac [("x","a")] allE 1);
by (safe_tac comp_cs);
by(ALLGOALS(asm_full_simp_tac prod_ss));
qed"hoare_while";

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
val ss = arith_ss addsimps (eq_sym_conv::assign_def::prems@A_simps@B_simps);
by(hoare_tac ss);
by(while_tac "%s.s z = i + s u & s y = j" ss 3);
by(hoare_tac ss);
result();

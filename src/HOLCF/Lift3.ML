(*  Title:      HOLCF/Lift3.ML
    ID:         $Id$
    Author:     Olaf Mueller, Robert Sandner
    Copyright   1996 Technische Universitaet Muenchen

Theorems for Lift3.thy
*)


open Lift3;

(* ----------------------------------------------------------- *)
(*                        From Undef to UU		       *)
(* ----------------------------------------------------------- *)

Addsimps [inst_lift_pcpo];

local

val case1' = prove_goal Lift3.thy "lift_case f1 f2 UU = f1"
	     (fn _ => [simp_tac (!simpset addsimps lift.simps) 1]);

val case2' = prove_goal Lift3.thy "lift_case f1 f2 (Def a) = f2 a"
	     (fn _ => [Simp_tac 1]);

val distinct1' = prove_goal Lift3.thy "UU ~= Def a" 
		 (fn _ => [Simp_tac 1]);

val distinct2' = prove_goal Lift3.thy "Def a ~= UU"
		 (fn _ => [Simp_tac 1]);

val inject' = prove_goal Lift3.thy "Def a = Def aa = (a = aa)"
	       (fn _ => [Simp_tac 1]);

val rec1' = prove_goal Lift3.thy "lift_rec f1 f2 UU = f1"
	    (fn _ => [Simp_tac 1]);

val rec2' = prove_goal Lift3.thy "lift_rec f1 f2 (Def a) = f2 a"
	    (fn _ => [Simp_tac 1]);

val induct' = prove_goal Lift3.thy "[| P UU; !a. P (Def a) |] ==> P lift"
	    (fn prems => [cut_facts_tac prems 1, Asm_full_simp_tac 1,
		      etac Lift1.lift.induct 1,fast_tac HOL_cs 1]);

in 

val Def_not_UU = distinct1' RS not_sym;

structure lift =
struct
val cases = [case1',case2'];
val distinct = [distinct1',distinct2'];
val inject = [inject'];
val induct = allI RSN(2,induct');
val recs = [rec1',rec2'];
val simps = cases@distinct@inject@recs;
fun induct_tac (s:string) (i:int) = 
    (res_inst_tac [("lift",s)] induct i);
end;

end; (* local *)

Delsimps [inst_lift_pcpo];
Delsimps lift.simps;

Addsimps [inst_lift_pcpo RS sym];
Addsimps lift.simps;


(* -------------------------------------------------------------------------*)
(* rewrite_rule for less_lift 						    *)
(* -------------------------------------------------------------------------*)

goal Lift3.thy "(x::'a lift) << y = (x=y | x=UU)";
br (inst_lift_po RS ssubst) 1;
by (Simp_tac 1);
val less_lift = result();




(* ---------------------------------------------------------- *)
(*                  Relating UU and Undef                     *)
(* ---------------------------------------------------------- *)

goal Lift3.thy "x=UU | (? y.x=Def y)"; 
by (lift.induct_tac "x" 1);
by (Asm_simp_tac 1);
by (rtac disjI2 1);
by (rtac exI 1);
by (Asm_simp_tac 1);
qed"Lift_exhaust";

val prems = goal Lift3.thy 
  "[| x = UU ==> P; ? a. x = Def a ==> P |] ==> P";
by (cut_facts_tac [Lift_exhaust] 1);
by (fast_tac (HOL_cs addSEs prems) 1);
qed"Lift_cases";

goal Lift3.thy "(x~=UU)=(? y.x=Def y)";
br iffI 1;
 br Lift_cases 1;
  by (fast_tac HOL_cs 1);
 by (fast_tac HOL_cs 1);
by (fast_tac (HOL_cs addSIs lift.distinct) 1);
qed"not_Undef_is_Def";

val Undef_eq_UU = inst_lift_pcpo RS sym;

val DefE = prove_goal Lift3.thy "Def x = UU ==> R" 
    (fn prems => [
        cut_facts_tac prems 1,
        asm_full_simp_tac (HOL_ss addsimps [Def_not_UU]) 1]);

val prems = goal Lift3.thy "[| x = Def s; x = UU |] ==> R";
by (cut_facts_tac prems 1);
by (fast_tac (HOL_cs addSDs [DefE]) 1);
val DefE2 = result();



(* ---------------------------------------------------------- *)
(*                          Lift is flat                     *)
(* ---------------------------------------------------------- *)

goalw Lift3.thy [flat_def] "flat (x::'a lift)";
by (simp_tac (!simpset addsimps [less_lift]) 1);
val flat_lift = result();




(* ---------------------------------------------------------- *)
(*       More Continuity Proofs and Extended Tactic           *)
(* ---------------------------------------------------------- *)

goal Lift3.thy "cont (%x. case x of Undef => UU | Def a => f a)";

br flatdom_strict2cont 1;
 br flat_lift 1;
by (Simp_tac 1);

val cont_flift1_arg = result();



goal Lift3.thy "cont (%x. case x of Undef => UU | Def a => Def (f a))";

br flatdom_strict2cont 1;
 br flat_lift 1;
by (Simp_tac 1);

val cont_flift2_arg = result();



goal Lift3.thy "!!f. [|! a.cont (%y. (f y) a)|] ==> \
\   cont (%y. case x of Undef => UU | Def a => (f y) a)";

by (res_inst_tac [("x","x")] Lift_cases 1);
 by (Asm_simp_tac 1);
by (fast_tac (HOL_cs addss !simpset) 1);

qed"cont_flift1_not_arg";

val cont_flift1_not_arg2 = (allI RS cont_flift1_not_arg);




(* zusammenfassen zu cont(%y. ((f y)`(g y)) s)     *)

goal Lift3.thy "!!f.cont g ==> cont(%x. (f`(g x)) s)";
by (rtac monocontlub2cont 1);
(* monotone *)
 by (rtac monofunI 1);
 by (strip_tac 1);
 by (rtac (monofun_cfun_arg RS monofun_fun_fun) 1);
 by (etac (cont2mono RS monofunE RS spec RS spec RS mp) 1); 
 by (atac 1);
(* contlub *)
by (rtac contlubI 1);
by (strip_tac 1);
by ((rtac (cont2contlub RS contlubE RS spec RS mp RS ssubst) 1) THEN (atac 1));
 ba 1;
by (stac (contlub_cfun_arg RS fun_cong) 1);
 be (cont2mono RS ch2ch_monofun) 1;
 ba 1;
by (stac thelub_fun 1);
 by (fast_tac ((HOL_cs addSIs [ch2ch_fappR]) 
		       addSEs [cont2mono RS ch2ch_monofun]) 1);
br refl 1;
qed"cont_fapp_app1";


goal Lift3.thy "cont(%y. (y`x) s)";
by (rtac monocontlub2cont 1);
 (* monotone *)
 by (rtac monofunI 1);
 by (strip_tac 1); 
 be (monofun_cfun_fun RS monofun_fun_fun) 1;
(* continuous *)
by (rtac contlubI 1);
by (strip_tac 1);
by (stac (contlub_cfun_fun RS fun_cong) 1);
 by (atac 1);
by (stac thelub_fun 1);
 be ch2ch_fappL 1;
br refl 1;
qed"cont_fapp_app2";



val prems = goal Lift3.thy "[| cont f1; cont f2 |] ==> \
\   cont (%x. if b then f1 x else f2 x)";

by (cut_facts_tac prems 1);
by (case_tac "b" 1);
by (TRYALL (fast_tac (HOL_cs addss HOL_ss)));

val cont_if = result();



val cont2cont_CF1L_rev2 = (allI RS cont2cont_CF1L_rev);

val cont_lemmas =  cont_lemmas@
		   [cont_flift1_arg,cont_flift2_arg,
                    cont_flift1_not_arg2,cont2cont_CF1L_rev2, 
                    cont_fapp_app1,cont_fapp_app2,cont_if];


val cont_tac = (fn i => ((resolve_tac cont_lemmas i)));
 
val cont_tacR = (fn i => ((simp_tac (!simpset 
                                addsimps [flift1_def,flift2_def]) i)
                           THEN REPEAT (cont_tac i) ));

(* --------------------------------------------------------- *)
(*                Admissibility tactic and tricks            *)
(* --------------------------------------------------------- *)


goal Lift3.thy "x~=FF = (x=TT|x=UU)";
by (res_inst_tac [("p","x")] trE 1);
  by (TRYALL (Asm_full_simp_tac));
qed"adm_trick_1";

goal Lift3.thy "x~=TT = (x=FF|x=UU)";
by (res_inst_tac [("p","x")] trE 1);
  by (TRYALL (Asm_full_simp_tac));
qed"adm_trick_2";


val adm_tricks = [adm_trick_1,adm_trick_2];
val adm_tac = (fn i => ((resolve_tac adm_thms i)));
val adm_tacR = (fn i => (REPEAT (adm_tac i)));
val adm_cont_tac = (fn i => ((adm_tacR i) THEN (cont_tacR i)));


(* ----------------------------------------------------------------- *)
(*     Relations between domains and terms using lift constructs     *)
(* ----------------------------------------------------------------- *)

goal Lift3.thy
"!!t.[|t~=UU|]==> ((t andalso s)~=FF)=(t~=FF & s~=FF)";
by (rtac iffI 1);
(* 1 *)
by (res_inst_tac [("p","t")] trE 1);
by (fast_tac HOL_cs 1);
by (res_inst_tac [("p","s")] trE 1);
by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (subgoal_tac "(t andalso s) = FF" 1);
by (fast_tac HOL_cs 1);
by (Asm_full_simp_tac 1);
by (res_inst_tac [("p","s")] trE 1);
by (subgoal_tac "(t andalso s) = FF" 1);
by (fast_tac HOL_cs 1);
by (Asm_full_simp_tac 1);
by (subgoal_tac "(t andalso s) = FF" 1);
by (fast_tac HOL_cs 1);
by (Asm_full_simp_tac 1);
by (subgoal_tac "(t andalso s) = FF" 1);
by (fast_tac HOL_cs 1);
by (Asm_full_simp_tac 1);
(* 2*)
by (res_inst_tac [("p","t")] trE 1);
by (fast_tac HOL_cs 1);
by (Asm_full_simp_tac 1);
by (fast_tac HOL_cs 1);
qed"andalso_and";


goal Lift3.thy "blift x ~=UU";
by (simp_tac (!simpset addsimps [blift_def])1);
by (case_tac "x" 1);
 by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
qed"blift_not_UU";

goal Lift3.thy "(blift x ~=FF)= x";
by (simp_tac (!simpset addsimps [blift_def]) 1);
by (case_tac "x" 1); 
 by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
qed"blift_and_bool";

goal Lift3.thy "plift P`(Def y) = blift (P y)";
by (simp_tac (!simpset addsimps [plift_def,flift1_def]) 1);
by (stac beta_cfun 1);
by (cont_tacR 1);
by (Simp_tac 1);
qed"plift2blift";

goal Lift3.thy 
  "(If blift P then A else B fi)= (if P then A else B)";
by (simp_tac (!simpset addsimps [blift_def]) 1);
by (res_inst_tac [("P","P"),("Q","P")] impCE 1);
by (fast_tac HOL_cs 1);
by (REPEAT (Asm_full_simp_tac 1));
qed"If_and_if";


Addsimps [plift2blift,If_and_if,blift_not_UU,blift_and_bool];

simpset := !simpset addsolver (K (DEPTH_SOLVE_1 o cont_tac));
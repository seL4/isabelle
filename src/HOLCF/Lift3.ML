(*  Title:      HOLCF/Lift3.ML
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1996 Technische Universitaet Muenchen

Theorems for Lift3.thy
*)


(* for compatibility with old HOLCF-Version *)
qed_goal "inst_lift_pcpo" thy "UU = Undef"
 (fn prems => 
        [
        (simp_tac (HOL_ss addsimps [UU_def,UU_lift_def]) 1)
        ]);

(* ----------------------------------------------------------- *)
(*           In lift.simps Undef is replaced by UU             *)
(*           Undef should be invisible from now on             *)
(* ----------------------------------------------------------- *)


Addsimps [inst_lift_pcpo];

local

val case1' = prove_goal thy "lift_case f1 f2 UU = f1"
             (fn _ => [simp_tac (!simpset addsimps lift.simps) 1]);
val case2' = prove_goal thy "lift_case f1 f2 (Def a) = f2 a"
             (fn _ => [Simp_tac 1]);
val distinct1' = prove_goal thy "UU ~= Def a" 
                 (fn _ => [Simp_tac 1]);
val distinct2' = prove_goal thy "Def a ~= UU"
                 (fn _ => [Simp_tac 1]);
val inject' = prove_goal thy "Def a = Def aa = (a = aa)"
               (fn _ => [Simp_tac 1]);
val rec1' = prove_goal thy "lift_rec f1 f2 UU = f1"
            (fn _ => [Simp_tac 1]);
val rec2' = prove_goal thy "lift_rec f1 f2 (Def a) = f2 a"
            (fn _ => [Simp_tac 1]);
val induct' = prove_goal thy "[| P UU; !a. P (Def a) |] ==> P lift"
            (fn prems => [cut_facts_tac prems 1, Asm_full_simp_tac 1,
                      etac Lift1.lift.induct 1,fast_tac HOL_cs 1]);

in 

val Def_not_UU = distinct2';

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

Delsimps Lift1.lift.simps;
Delsimps [inst_lift_pcpo];
Addsimps [inst_lift_pcpo RS sym];
Addsimps lift.simps;


(* --------------------------------------------------------*)
              section"less_lift";
(* --------------------------------------------------------*)

goal thy "(x::'a lift) << y = (x=y | x=UU)";
by (stac inst_lift_po 1);
by (Simp_tac 1);
qed"less_lift";


(* ---------------------------------------------------------- *)
                 section"UU and Def";             
(* ---------------------------------------------------------- *)

goal thy "x=UU | (? y. x=Def y)"; 
by (lift.induct_tac "x" 1);
by (Asm_simp_tac 1);
by (rtac disjI2 1);
by (rtac exI 1);
by (Asm_simp_tac 1);
qed"Lift_exhaust";

val prems = goal thy 
  "[| x = UU ==> P; ? a. x = Def a ==> P |] ==> P";
by (cut_facts_tac [Lift_exhaust] 1);
by (fast_tac (HOL_cs addSEs prems) 1);
qed"Lift_cases";

goal thy
  "P(lift_case a b x) = ((x=UU --> P a) & (!y. x = Def y --> P(b y)))";
by (lift.induct_tac "x" 1);
by (ALLGOALS Asm_simp_tac);
qed "expand_lift_case";

goal thy "(x~=UU)=(? y. x=Def y)";
by (rtac iffI 1);
by (rtac Lift_cases 1);
by (REPEAT (fast_tac (HOL_cs addSIs lift.distinct) 1));
qed"not_Undef_is_Def";

(* For x~=UU in assumptions def_tac replaces x by (Def a) in conclusion *)
val def_tac = etac (not_Undef_is_Def RS iffD1 RS exE) THEN' Asm_simp_tac;

bind_thm("Undef_eq_UU", inst_lift_pcpo RS sym);

val DefE = prove_goal thy "Def x = UU ==> R" 
    (fn prems => [
        cut_facts_tac prems 1,
        asm_full_simp_tac (HOL_ss addsimps [Def_not_UU]) 1]);

val prems = goal thy "[| x = Def s; x = UU |] ==> R";
by (cut_facts_tac prems 1);
by (fast_tac (HOL_cs addSDs [DefE]) 1);
qed"DefE2";

goal thy "Def x << Def y = (x = y)";
by (stac (hd lift.inject RS sym) 1);
back();
by (rtac iffI 1);
by (asm_full_simp_tac (!simpset addsimps [inst_lift_po] ) 1);
by (etac (antisym_less_inverse RS conjunct1) 1);
qed"Def_inject_less_eq";

goal thy "Def x << y = (Def x = y)";
by (simp_tac (!simpset addsimps [less_lift]) 1);
qed"Def_less_is_eq";

Addsimps [Def_less_is_eq];

(* ---------------------------------------------------------- *)
              section"Lift is flat";
(* ---------------------------------------------------------- *)

goal thy "! x y::'a lift. x << y --> x = UU | x = y";
by (simp_tac (!simpset addsimps [less_lift]) 1);
qed"ax_flat_lift";

(* Two specific lemmas for the combination of LCF and HOL terms *)

goal thy "!!f.[|cont g; cont f|] ==> cont(%x. ((f x)`(g x)) s)";
by (rtac cont2cont_CF1L 1);
by (REPEAT (resolve_tac cont_lemmas1 1));
by (Auto_tac());
qed"cont_fapp_app";

goal thy "!!f.[|cont g; cont f|] ==> cont(%x. ((f x)`(g x)) s t)";
by (rtac cont2cont_CF1L 1);
by (etac cont_fapp_app 1);
by (assume_tac 1);
qed"cont_fapp_app_app";


(* continuity of if then else *)
val prems = goal thy "[| cont f1; cont f2 |] ==> \
\   cont (%x. if b then f1 x else f2 x)";
by (cut_facts_tac prems 1);
by (case_tac "b" 1);
by (TRYALL (fast_tac (HOL_cs addss HOL_ss)));
qed"cont_if";


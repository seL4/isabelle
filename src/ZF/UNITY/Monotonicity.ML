(*  Title:      ZF/UNITY/Monotonicity.ML
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge

Monotonicity of an operator (meta-function) with respect to arbitrary set relations.
*)


(*TOO SLOW as a default simprule????
Addsimps [append_left_is_Nil_iff,append_left_is_Nil_iff2];
*)

Goalw [mono1_def]
  "[| mono1(A, r, B, s, f); <x, y>:r; x:A; y:A |] ==> <f(x), f(y)>:s";
by Auto_tac;
qed "mono1D";

Goalw [mono2_def]
"[| mono2(A, r, B, s, C, t, f);  <x, y>:r; <u,v>:s; x:A; y:A; u:B; v:B |] ==> \
\  <f(x, u), f(y,v)>:t";
by Auto_tac;
qed "mono2D";


(** Monotonicity of take **)

(*????premises too strong*)
Goal "[| i le j; xs:list(A); i:nat; j:nat |] ==> <take(i, xs), take(j, xs)>:prefix(A)";
by (case_tac "length(xs) le i" 1);
by (subgoal_tac "length(xs) le j" 1);
by (blast_tac (claset() addIs [le_trans]) 2);
by (Asm_simp_tac 1);
by (dtac not_lt_imp_le 1);
by Auto_tac;
by (case_tac "length(xs) le j" 1);
by (auto_tac (claset(), simpset() addsimps [take_prefix]));
by (dtac not_lt_imp_le 1);
by Auto_tac;
by (dres_inst_tac [("m", "i")] less_imp_succ_add 1);
by Auto_tac;
by (subgoal_tac "i #+ k le length(xs)" 1);
by (blast_tac (claset() addIs [leI]) 2);
by (asm_full_simp_tac (simpset() addsimps [take_add, prefix_iff, take_type, drop_type]) 1);
qed "take_mono_left";

Goal "[| <xs, ys>:prefix(A); i:nat |] ==> <take(i, xs), take(i, ys)>:prefix(A)"; 
by (auto_tac (claset(), simpset() addsimps [prefix_iff]));
qed "take_mono_right";

Goal "[| i le j; <xs, ys>:prefix(A); i:nat; j:nat |] ==> <take(i, xs), take(j, ys)>:prefix(A)";
by (res_inst_tac [("b", "take(j, xs)")] prefix_trans 1);
by (auto_tac (claset() addDs [prefix_type RS subsetD]
                       addIs [take_mono_left, take_mono_right], simpset()));
qed "take_mono";

Goalw [mono2_def, Le_def] "mono2(nat, Le, list(A), prefix(A), list(A), prefix(A), take)";
by Auto_tac;
by (blast_tac (claset() addIs [take_mono]) 1);
qed "mono_take";
Addsimps [mono_take];
AddIs [mono_take];

(** Monotonicity of length **)

bind_thm("length_mono", prefix_length_le);

Goalw [mono1_def] "mono1(list(A), prefix(A), nat, Le, length)";
by (auto_tac (claset() addDs [prefix_length_le],
             simpset() addsimps [Le_def]));
qed "mono_length";
Addsimps [mono_length];
AddIs [mono_length];

(** Monotonicity of Un **)

Goalw [mono2_def, SetLe_def]  
 "mono2(Pow(A), SetLe(A), Pow(A), SetLe(A), Pow(A), SetLe(A), op Un)";
by Auto_tac;
qed "mono_Un";
Addsimps [mono_Un];
AddIs [mono_Un];

(* Monotonicity of multiset union *)

Goalw [mono2_def, MultLe_def]  
   "mono2(Mult(A), MultLe(A,r), Mult(A), MultLe(A, r), Mult(A), MultLe(A, r), munion)";
by (auto_tac (claset(), simpset() addsimps [Mult_iff_multiset]));
by (REPEAT(blast_tac (claset() addIs [munion_multirel_mono,
                                munion_multirel_mono1,
                                munion_multirel_mono2,
                                multiset_into_Mult]) 1));
qed "mono_munion";
Addsimps [mono_munion];
AddIs [mono_munion];

Goalw [mono1_def, Le_def] "mono1(nat, Le, nat, Le, succ)";
by Auto_tac;
qed "mono_succ";
Addsimps [mono_succ];
AddIs [mono_succ];


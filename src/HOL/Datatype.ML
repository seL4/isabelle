(*  Title:      HOL/Datatype.ML
    ID:         $Id$
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

(** legacy ML bindings **)

structure bool =
struct
  val distinct = thms "bool.distinct";
  val inject = thms "bool.inject";
  val exhaust = thm "bool.exhaust";
  val cases = thms "bool.cases";
  val split = thm "bool.split";
  val split_asm = thm "bool.split_asm";
  val induct = thm "bool.induct";
  val recs = thms "bool.recs";
  val simps = thms "bool.simps";
  val size = thms "bool.size";
end;

structure sum =
struct
  val distinct = thms "sum.distinct";
  val inject = thms "sum.inject";
  val exhaust = thm "sum.exhaust";
  val cases = thms "sum.cases";
  val split = thm "sum.split";
  val split_asm = thm "sum.split_asm";
  val induct = thm "sum.induct";
  val recs = thms "sum.recs";
  val simps = thms "sum.simps";
  val size = thms "sum.size";
end;

structure unit =
struct
  val distinct = thms "unit.distinct";
  val inject = thms "unit.inject";
  val exhaust = thm "unit.exhaust";
  val cases = thms "unit.cases";
  val split = thm "unit.split";
  val split_asm = thm "unit.split_asm";
  val induct = thm "unit.induct";
  val recs = thms "unit.recs";
  val simps = thms "unit.simps";
  val size = thms "unit.size";
end;

structure prod =
struct
  val distinct = thms "prod.distinct";
  val inject = thms "prod.inject";
  val exhaust = thm "prod.exhaust";
  val cases = thms "prod.cases";
  val split = thm "prod.split";
  val split_asm = thm "prod.split_asm";
  val induct = thm "prod.induct";
  val recs = thms "prod.recs";
  val simps = thms "prod.simps";
  val size = thms "prod.size";
end;


(** sum_case -- the selection operator for sums **)

(*compatibility*)
val [sum_case_Inl, sum_case_Inr] = sum.cases;
bind_thm ("sum_case_Inl", sum_case_Inl);
bind_thm ("sum_case_Inr", sum_case_Inr);

Goal "sum_case (%x::'a. f(Inl x)) (%y::'b. f(Inr y)) s = f(s)";
by (EVERY1 [res_inst_tac [("s","s")] sumE,
            etac ssubst, rtac sum_case_Inl,
            etac ssubst, rtac sum_case_Inr]);
qed "surjective_sum";

(*Prevents simplification of f and g: much faster*)
Goal "s=t ==> sum_case f g s = sum_case f g t";
by (etac arg_cong 1);
qed "sum_case_weak_cong";

val [p1,p2] = Goal
  "[| sum_case f1 f2 = sum_case g1 g2;  \
\     [| f1 = g1; f2 = g2 |] ==> P |] \
\  ==> P";
by (rtac p2 1);
by (rtac ext 1);
by (cut_inst_tac [("x","Inl x")] (p1 RS fun_cong) 1);
by (Asm_full_simp_tac 1);
by (rtac ext 1);
by (cut_inst_tac [("x","Inr x")] (p1 RS fun_cong) 1);
by (Asm_full_simp_tac 1);
qed "sum_case_inject";

(*  Title:      Pure/Isar/spec_rules.ML
    Author:     Makarius

Rules that characterize functional/relational specifications.  NB: In
the face of arbitrary morphisms, the original shape of specifications
may get transformed almost arbitrarily.
*)

signature SPEC_RULES =
sig
  datatype kind = Functional | Relational | Co_Relational
  val dest: Proof.context -> (kind * (term * thm list) list) list
  val dest_global: theory -> (kind * (term * thm list) list) list
  val add: kind * (term * thm list) list -> local_theory -> local_theory
  val add_global: kind * (term * thm list) list -> theory -> theory
end;

structure Spec_Rules: SPEC_RULES =
struct

(* maintain rules *)

datatype kind = Functional | Relational | Co_Relational;

structure Rules = GenericDataFun
(
  type T = (kind * (term * thm list) list) Item_Net.T;
  val empty : T =
    Item_Net.init
      (fn ((k1, spec1), (k2, spec2)) => k1 = k2 andalso
        eq_list (fn ((t1, ths1), (t2, ths2)) =>
          t1 aconv t2 andalso eq_list Thm.eq_thm_prop (ths1, ths2)) (spec1, spec2))
      (map #1 o #2);
  val extend = I;
  fun merge _ = Item_Net.merge;
);

val dest = Item_Net.content o Rules.get o Context.Proof;
val dest_global = Item_Net.content o Rules.get o Context.Theory;

fun add (kind, specs) = LocalTheory.declaration
  (fn phi =>
    let val specs' = map (fn (t, ths) => (Morphism.term phi t, Morphism.fact phi ths)) specs;
    in Rules.map (Item_Net.update (kind, specs')) end);

fun add_global entry =
  Context.theory_map (Rules.map (Item_Net.update entry));

end;

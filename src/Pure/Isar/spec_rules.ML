(*  Title:      Pure/Isar/spec_rules.ML
    Author:     Makarius

Rules that characterize specifications, with rough classification.
NB: In the face of arbitrary morphisms, the original shape of
specifications may get lost.
*)

signature SPEC_RULES =
sig
  datatype recursion =
    Primrec of string list | Recdef | Primcorec of string list | Corec | Unknown_Recursion
  val recursion_ord: recursion ord
  datatype rough_classification = Equational of recursion | Inductive | Co_Inductive | Unknown
  val rough_classification_ord: rough_classification ord
  val equational_primrec: string list -> rough_classification
  val equational_recdef: rough_classification
  val equational_primcorec: string list -> rough_classification
  val equational_corec: rough_classification
  val equational: rough_classification
  val is_equational: rough_classification -> bool
  val is_inductive: rough_classification -> bool
  val is_co_inductive: rough_classification -> bool
  val is_unknown: rough_classification -> bool
  type spec = rough_classification * (term list * thm list)
  val get: Proof.context -> spec list
  val get_global: theory -> spec list
  val retrieve: Proof.context -> term -> spec list
  val retrieve_global: theory -> term -> spec list
  val add: rough_classification -> term list * thm list -> local_theory -> local_theory
  val add_global: rough_classification -> term list * thm list -> theory -> theory
end;

structure Spec_Rules: SPEC_RULES =
struct

(* recursion *)

datatype recursion =
  Primrec of string list | Recdef | Primcorec of string list | Corec | Unknown_Recursion;

val recursion_index =
  fn Primrec _ => 0 | Recdef => 1 | Primcorec _ => 2 | Corec => 3 | Unknown_Recursion => 4;

fun recursion_ord (Primrec Ts1, Primrec Ts2) = list_ord fast_string_ord (Ts1, Ts2)
  | recursion_ord (Primcorec Ts1, Primcorec Ts2) = list_ord fast_string_ord (Ts1, Ts2)
  | recursion_ord rs = int_ord (apply2 recursion_index rs);


(* rough classification *)

datatype rough_classification = Equational of recursion | Inductive | Co_Inductive | Unknown;

fun rough_classification_ord (Equational r1, Equational r2) = recursion_ord (r1, r2)
  | rough_classification_ord cs =
      int_ord (apply2 (fn Equational _ => 0 | Inductive => 1 | Co_Inductive => 2 | Unknown => 3) cs);

val equational_primrec = Equational o Primrec;
val equational_recdef = Equational Recdef;
val equational_primcorec = Equational o Primcorec;
val equational_corec = Equational Corec;
val equational = Equational Unknown_Recursion;

val is_equational = fn Equational _ => true | _ => false;
val is_inductive = fn Inductive => true | _ => false;
val is_co_inductive = fn Co_Inductive => true | _ => false;
val is_unknown = fn Unknown => true | _ => false;


(* rules *)

type spec = rough_classification * (term list * thm list);

structure Rules = Generic_Data
(
  type T = spec Item_Net.T;
  val empty : T =
    Item_Net.init
      (fn ((c1, (ts1, ths1)), (c2, (ts2, ths2))) =>
        is_equal (rough_classification_ord (c1, c2)) andalso
        eq_list (op aconv) (ts1, ts2) andalso
        eq_list Thm.eq_thm_prop (ths1, ths2))
      (#1 o #2);
  val extend = I;
  val merge = Item_Net.merge;
);


(* get *)

fun get_generic context =
  let
    val thy = Context.theory_of context;
    val transfer = Global_Theory.transfer_theories thy;
  in Item_Net.content (Rules.get context) |> (map o apsnd o apsnd o map) transfer end;

val get = get_generic o Context.Proof;
val get_global = get_generic o Context.Theory;


(* retrieve *)

fun retrieve_generic context =
  Item_Net.retrieve (Rules.get context)
  #> (map o apsnd o apsnd o map) (Thm.transfer'' context);

val retrieve = retrieve_generic o Context.Proof;
val retrieve_global = retrieve_generic o Context.Theory;


(* add *)

fun add class (ts, ths) lthy =
  let
    val cts = map (Thm.cterm_of lthy) ts;
  in
    lthy |> Local_Theory.declaration {syntax = false, pervasive = true}
      (fn phi =>
        let
          val (ts', ths') =
            Morphism.fact phi (map Drule.mk_term cts @ ths)
            |> chop (length cts)
            |>> map (Thm.term_of o Drule.dest_term)
            ||> map Thm.trim_context;
        in Rules.map (Item_Net.update (class, (ts', ths'))) end)
  end;

fun add_global class spec =
  Context.theory_map (Rules.map (Item_Net.update (class, (apsnd o map) Thm.trim_context spec)));

end;

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
  val is_relational: rough_classification -> bool
  val is_unknown: rough_classification -> bool
  type spec =
    {name: string, rough_classification: rough_classification, terms: term list, rules: thm list}
  val get: Proof.context -> spec list
  val get_global: theory -> spec list
  val retrieve: Proof.context -> term -> spec list
  val retrieve_global: theory -> term -> spec list
  val add: string -> rough_classification -> term list -> thm list -> local_theory -> local_theory
  val add_global: string -> rough_classification -> term list -> thm list -> theory -> theory
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
val is_relational = is_inductive orf is_co_inductive;
val is_unknown = fn Unknown => true | _ => false;


(* rules *)

type spec =
  {name: string, rough_classification: rough_classification, terms: term list, rules: thm list};

fun eq_spec (specs: spec * spec) =
  (op =) (apply2 #name specs) andalso
  is_equal (rough_classification_ord (apply2 #rough_classification specs)) andalso
  eq_list (op aconv) (apply2 #terms specs) andalso
  eq_list Thm.eq_thm_prop (apply2 #rules specs);

fun map_spec_rules f ({name, rough_classification, terms, rules}: spec) : spec =
  {name = name, rough_classification = rough_classification, terms = terms, rules = map f rules};

structure Rules = Generic_Data
(
  type T = spec Item_Net.T;
  val empty : T = Item_Net.init eq_spec #terms;
  val extend = I;
  val merge = Item_Net.merge;
);


(* get *)

fun get_generic context =
  let
    val thy = Context.theory_of context;
    val transfer = Global_Theory.transfer_theories thy;
  in
    Item_Net.content (Rules.get context)
    |> (map o map_spec_rules) transfer
  end;

val get = get_generic o Context.Proof;
val get_global = get_generic o Context.Theory;


(* retrieve *)

fun retrieve_generic context =
  Item_Net.retrieve (Rules.get context)
  #> (map o map_spec_rules) (Thm.transfer'' context);

val retrieve = retrieve_generic o Context.Proof;
val retrieve_global = retrieve_generic o Context.Theory;


(* add *)

fun add name rough_classification terms rules lthy =
  let val thms0 = map Thm.trim_context (map (Drule.mk_term o Thm.cterm_of lthy) terms @ rules) in
    lthy |> Local_Theory.declaration {syntax = false, pervasive = true}
      (fn phi => fn context =>
        let
          val (terms', rules') =
            map (Thm.transfer (Context.theory_of context)) thms0
            |> Morphism.fact phi
            |> chop (length terms)
            |>> map (Thm.term_of o Drule.dest_term)
            ||> map Thm.trim_context;
        in
          context |> (Rules.map o Item_Net.update)
            {name = name, rough_classification = rough_classification,
              terms = terms', rules = rules'}
        end)
  end;

fun add_global name rough_classification terms rules =
  (Context.theory_map o Rules.map o Item_Net.update)
    {name = name, rough_classification = rough_classification,
      terms = terms, rules = map Thm.trim_context rules};

end;

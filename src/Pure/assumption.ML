(*  Title:      Pure/assumption.ML
    ID:         $Id$
    Author:     Makarius

Local assumptions, parameterized by export rules.
*)

signature ASSUMPTION =
sig
  type export
  val assume_export: export
  val presume_export: export
  val assume: cterm -> thm
  val assms_of: Proof.context -> cterm list
  val prems_of: Proof.context -> thm list
  val extra_hyps: Proof.context -> thm -> term list
  val add_assms: export -> cterm list -> Proof.context -> thm list * Proof.context
  val add_assumes: cterm list -> Proof.context -> thm list * Proof.context
  val add_view: Proof.context -> cterm list -> Proof.context -> Proof.context
  val export: bool -> Proof.context -> Proof.context -> thm -> thm
  val export_term: Proof.context -> Proof.context -> term -> term
  val export_morphism: Proof.context -> Proof.context -> morphism
end;

structure Assumption: ASSUMPTION =
struct

(** basic rules **)

type export = bool -> cterm list -> (thm -> thm) * (term -> term);

(*
    [A]
     :
     B
  --------
  #A ==> B
*)
fun assume_export is_goal asms =
  (if is_goal then Drule.implies_intr_protected asms else Drule.implies_intr_list asms, fn t => t);

(*
    [A]
     :
     B
  -------
  A ==> B
*)
fun presume_export _ = assume_export false;

val assume = MetaSimplifier.norm_hhf o Thm.assume;



(** local context data **)

datatype data = Data of
 {assms: (export * cterm list) list,    (*assumes and views: A ==> _*)
  prems: thm list};                     (*prems: A |- A*)

fun make_data (assms, prems) = Data {assms = assms, prems = prems};

structure Data = ProofDataFun
(
  type T = data;
  fun init _ = make_data ([], []);
);

fun map_data f = Data.map (fn Data {assms, prems} => make_data (f (assms, prems)));
fun rep_data ctxt = Data.get ctxt |> (fn Data args => args);

val assumptions_of = #assms o rep_data;
val assms_of = maps #2 o assumptions_of;
val prems_of = #prems o rep_data;

fun extra_hyps ctxt th = subtract (op aconv) (map Thm.term_of (assms_of ctxt)) (Thm.hyps_of th);


(* named prems -- legacy feature *)

val _ = Context.add_setup
  (PureThy.add_thms_dynamic ("prems",
    fn Context.Theory _ => [] | Context.Proof ctxt => prems_of ctxt));


(* add assumptions *)

fun add_assms export new_asms =
  let val new_prems = map assume new_asms in
    map_data (fn (asms, prems) => (asms @ [(export, new_asms)], prems @ new_prems)) #>
    pair new_prems
  end;

val add_assumes = add_assms assume_export;

fun add_view outer view = map_data (fn (asms, prems) =>
  let
    val (asms1, asms2) = chop (length (assumptions_of outer)) asms;
    val asms' = asms1 @ [(assume_export, view)] @ asms2;
  in (asms', prems) end);


(* export *)

fun diff_assms inner outer =
  Library.drop (length (assumptions_of outer), assumptions_of inner);

fun export is_goal inner outer =
  let val asms = diff_assms inner outer in
    MetaSimplifier.norm_hhf_protect
    #> fold_rev (fn (e, As) => #1 (e is_goal As)) asms
    #> MetaSimplifier.norm_hhf_protect
  end;

fun export_term inner outer =
  fold_rev (fn (e, As) => #2 (e false As)) (diff_assms inner outer);

fun export_morphism inner outer =
  let
    val thm = export false inner outer;
    val term = export_term inner outer;
    val typ = Logic.type_map term;
  in Morphism.morphism {name = I, var = I, typ = typ, term = term, fact = map thm} end;

end;

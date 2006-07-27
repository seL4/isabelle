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
  val assms_of: Context.proof -> term list
  val prems_of: Context.proof -> thm list
  val extra_hyps: Context.proof -> thm -> term list
  val add_assms: export -> cterm list -> Context.proof -> thm list * Context.proof
  val add_assumes: cterm list -> Context.proof -> thm list * Context.proof
  val add_view: Context.proof -> cterm list -> Context.proof -> Context.proof
  val exports: bool -> Context.proof -> Context.proof -> thm list -> thm list Seq.seq
end;

structure Assumption: ASSUMPTION =
struct

(** basic rules **)

type export = bool -> cterm list -> thm -> thm Seq.seq;

(*
    [A]
     :
     B
  --------
  #A ==> B
*)
fun assume_export true = Seq.single oo Drule.implies_intr_protected
  | assume_export false = Seq.single oo Drule.implies_intr_list;

(*
    [A]
     :
     B
  -------
  A ==> B
*)
fun presume_export _ = assume_export false;

val assume = norm_hhf o Thm.assume;



(** local context data **)

datatype data = Data of
 {assms: (export * cterm list) list,    (*assumes and views: A ==> _*)
  prems: thm list};                     (*prems: A |- A*)

fun make_data (assms, prems) = Data {assms = assms, prems = prems};

structure Data = ProofDataFun
(
  val name = "Pure/assumption";
  type T = data;
  fun init _ = make_data ([], []);
  fun print _ _ = ();
);

val _ = Context.add_setup Data.init;

fun map_data f = Data.map (fn Data {assms, prems} => make_data (f (assms, prems)));
fun rep_data ctxt = Data.get ctxt |> (fn Data args => args);

val assumptions_of = #assms o rep_data;
val assms_of = map Thm.term_of o maps #2 o assumptions_of;
val prems_of = #prems o rep_data;

fun extra_hyps ctxt th = subtract (op aconv) (assms_of ctxt) (Thm.hyps_of th);


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


(* exports *)

fun exports is_goal inner outer =
  let
    val asms = rev (Library.drop (length (assumptions_of outer), assumptions_of inner));
    val exp_asms = map (fn (exp, As) => exp is_goal As) asms;
  in
    map norm_hhf_protect
    #> Seq.map_list (Seq.EVERY exp_asms)
    #> Seq.map (map norm_hhf_protect)
  end;

end;

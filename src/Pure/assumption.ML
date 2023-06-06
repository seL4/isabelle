(*  Title:      Pure/assumption.ML
    Author:     Makarius

Context assumptions, parameterized by export rules.
*)

signature ASSUMPTION =
sig
  type export = bool -> cterm list -> (thm -> thm) * (term -> term)
  val assume_export: export
  val presume_export: export
  val assume: Proof.context -> cterm -> thm
  val assume_hyps: cterm -> Proof.context -> thm * Proof.context
  val all_assms_of: Proof.context -> cterm list
  val all_prems_of: Proof.context -> thm list
  val local_assms_of: Proof.context -> Proof.context -> cterm list
  val local_prems_of: Proof.context -> Proof.context -> thm list
  val add_assms: export -> cterm list -> Proof.context -> thm list * Proof.context
  val add_assumes: cterm list -> Proof.context -> thm list * Proof.context
  val export_term: Proof.context -> Proof.context -> term -> term
  val export_: {goal: bool} -> Proof.context -> Proof.context -> thm -> thm
  val export: Proof.context -> Proof.context -> thm -> thm
  val export_goal: Proof.context -> Proof.context -> thm -> thm
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
  #A \<Longrightarrow> B
*)
fun assume_export is_goal asms =
  (if is_goal then Drule.implies_intr_protected asms else Drule.implies_intr_list asms, fn t => t);

(*
    [A]
     :
     B
  -------
  A \<Longrightarrow> B
*)
fun presume_export _ = assume_export false;


fun assume ctxt = Raw_Simplifier.norm_hhf ctxt o Thm.assume;

fun assume_hyps ct ctxt =
  let val (th, ctxt') = Thm.assume_hyps ct ctxt
  in (Raw_Simplifier.norm_hhf ctxt' th, ctxt') end;



(** local context data **)

datatype data = Data of
 {rev_assms: (export * cterm list) list,    (*assumes: A \<Longrightarrow> _*)
  rev_prems: thm list};                     (*prems: A |- norm_hhf A*)

fun make_data (rev_assms, rev_prems) = Data {rev_assms = rev_assms, rev_prems = rev_prems};
val empty_data = make_data ([], []);

structure Data = Proof_Data
(
  type T = data;
  fun init _ = empty_data;
);

fun map_data f = Data.map (fn Data {rev_assms, rev_prems} => make_data (f (rev_assms, rev_prems)));
fun rep_data ctxt = Data.get ctxt |> (fn Data rep => rep);


(* all assumptions *)

val all_assumptions_of = rev o #rev_assms o rep_data;
val all_assms_of = maps #2 o all_assumptions_of;
val all_prems_of = rev o #rev_prems o rep_data;


(* local assumptions *)

local

fun drop_prefix eq (args as (x :: xs, y :: ys)) =
      if eq (x, y) then drop_prefix eq (xs, ys) else args
  | drop_prefix _ args = args;

fun check_result ctxt kind term_of res =
  (case res of
    ([], rest) => rest
  | (bad :: _, _) =>
      raise Fail ("Outer context disagrees on " ^ kind ^ ": " ^
        Syntax.string_of_term ctxt (term_of bad)));

in

fun local_assumptions_of inner outer =
  drop_prefix (eq_snd (eq_list Thm.aconvc)) (apply2 all_assumptions_of (outer, inner))
  |>> maps #2
  |> check_result outer "assumption" Thm.term_of;

val local_assms_of = maps #2 oo local_assumptions_of;

fun local_prems_of inner outer =
  drop_prefix Thm.eq_thm_prop (apply2 all_prems_of (outer, inner))
  |> check_result outer "premise" Thm.prop_of;

end;


(* add assumptions *)

fun add_assms export new_asms ctxt =
  let val (new_prems, ctxt') = fold_map assume_hyps new_asms ctxt in
    ctxt'
    |> map_data (fn (rev_assms, rev_prems) =>
        ((export, new_asms) :: rev_assms, fold cons new_prems rev_prems))
    |> pair new_prems
  end;

val add_assumes = add_assms assume_export;


(* export *)

fun export_term inner outer =
  fold_rev (fn (e, As) => #2 (e false As)) (local_assumptions_of inner outer);

fun export_thm is_goal inner outer =
  fold_rev (fn (e, As) => #1 (e is_goal As)) (local_assumptions_of inner outer);

fun export_{goal} inner outer =
  Raw_Simplifier.norm_hhf_protect inner #>
  export_thm goal inner outer #>
  Raw_Simplifier.norm_hhf_protect outer;

val export = export_{goal = false};
val export_goal = export_{goal = true};

fun export_morphism inner outer =
  let
    val export0 = export_thm false inner outer;
    fun thm thy =
      let val norm = norm_hhf_protect (Proof_Context.init_global thy)
      in norm #> export0 #> norm end;
    val term = export_term inner outer;
    val typ = Logic.type_map term;
  in
    Morphism.morphism "Assumption.export"
      {binding = [], typ = [K typ], term = [K term], fact = [map o thm o Morphism.the_theory]}
    |> Morphism.set_context (Proof_Context.theory_of inner)
  end;

end;

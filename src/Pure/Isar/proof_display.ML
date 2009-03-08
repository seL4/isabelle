(*  Title:      Pure/Isar/proof_display.ML
    Author:     Makarius

Printing of theorems, goals, results etc.
*)

signature PROOF_DISPLAY =
sig
  val pprint_context: Proof.context -> pprint_args -> unit
  val pprint_typ: theory -> typ -> pprint_args -> unit
  val pprint_term: theory -> term -> pprint_args -> unit
  val pprint_ctyp: ctyp -> pprint_args -> unit
  val pprint_cterm: cterm -> pprint_args -> unit
  val pprint_thm: thm -> pprint_args -> unit
  val print_theorems_diff: theory -> theory -> unit
  val print_theorems: theory -> unit
  val pretty_full_theory: bool -> theory -> Pretty.T
  val print_theory: theory -> unit
  val string_of_rule: Proof.context -> string -> thm -> string
  val print_results: bool -> Proof.context -> ((string * string) * (string * thm list) list) -> unit
  val pretty_consts: Proof.context -> (string * typ -> bool) -> (string * typ) list -> Pretty.T
end

structure ProofDisplay: PROOF_DISPLAY =
struct

(* toplevel pretty printing *)

fun pprint_context ctxt = Pretty.pprint
 (if ! ProofContext.debug then
    Pretty.quote (Pretty.big_list "proof context:" (ProofContext.pretty_context ctxt))
  else Pretty.str "<context>");

fun pprint pretty thy = Pretty.pprint o Pretty.quote o pretty (Syntax.init_pretty_global thy);

val pprint_typ = pprint Syntax.pretty_typ;
val pprint_term = pprint Syntax.pretty_term;
fun pprint_ctyp cT = pprint_typ (Thm.theory_of_ctyp cT) (Thm.typ_of cT);
fun pprint_cterm ct = pprint_term (Thm.theory_of_cterm ct) (Thm.term_of ct);
val pprint_thm = Pretty.pprint o ProofContext.pretty_thm_legacy;


(* theorems and theory *)

fun pretty_theorems_diff prev_thys thy =
  let
    val pretty_fact = ProofContext.pretty_fact (ProofContext.init thy);
    val thmss = Facts.dest_static (map PureThy.facts_of prev_thys) (PureThy.facts_of thy);
  in Pretty.big_list "theorems:" (map #1 (sort_wrt (#1 o #2) (map (`pretty_fact) thmss))) end;

fun print_theorems_diff prev_thy thy =
  Pretty.writeln (pretty_theorems_diff [prev_thy] thy);

fun pretty_theorems thy = pretty_theorems_diff (Theory.parents_of thy) thy;
val print_theorems = Pretty.writeln o pretty_theorems;

fun pretty_full_theory verbose thy =
  Pretty.chunks (Display.pretty_full_theory verbose thy @ [pretty_theorems thy]);

val print_theory = Pretty.writeln o pretty_full_theory false;


(* refinement rule *)

fun pretty_rule ctxt s thm =
  Pretty.block [Pretty.str (s ^ " attempt to solve goal by exported rule:"),
    Pretty.fbrk, ProofContext.pretty_thm ctxt thm];

val string_of_rule = Pretty.string_of ooo pretty_rule;


(* results *)

local

fun pretty_fact_name (kind, "") = Pretty.str kind
  | pretty_fact_name (kind, name) = Pretty.block [Pretty.str kind, Pretty.brk 1,
      Pretty.str (Long_Name.base_name name), Pretty.str ":"];

fun pretty_facts ctxt =
  flat o (separate [Pretty.fbrk, Pretty.str "and "]) o
    map (single o ProofContext.pretty_fact ctxt);

in

fun print_results do_print ctxt ((kind, name), facts) =
  if not do_print orelse kind = "" orelse kind = Thm.internalK then ()
  else if name = "" then
    Pretty.writeln (Pretty.block (Pretty.str kind :: Pretty.brk 1 :: pretty_facts ctxt facts))
  else Pretty.writeln
    (case facts of
      [fact] => Pretty.blk (1, [pretty_fact_name (kind, name), Pretty.fbrk,
        ProofContext.pretty_fact ctxt fact])
    | _ => Pretty.blk (1, [pretty_fact_name (kind, name), Pretty.fbrk,
        Pretty.blk (1, Pretty.str "(" :: pretty_facts ctxt facts @ [Pretty.str ")"])]));

end;


(* consts *)

local

fun pretty_var ctxt (x, T) =
  Pretty.block [Pretty.str x, Pretty.str " ::", Pretty.brk 1,
    Pretty.quote (Syntax.pretty_typ ctxt T)];

fun pretty_vars ctxt kind vs = Pretty.big_list kind (map (pretty_var ctxt) vs);

in

fun pretty_consts ctxt pred cs =
  (case filter pred (#1 (ProofContext.inferred_fixes ctxt)) of
    [] => pretty_vars ctxt "constants" cs
  | ps => Pretty.chunks [pretty_vars ctxt "parameters" ps, pretty_vars ctxt "constants" cs]);

end;

end;

(*  Title:      Pure/Isar/proof_display.ML
    ID:         $Id$
    Author:     Makarius

Printing of theorems, goals, results etc.
*)

signature BASIC_PROOF_DISPLAY =
sig
  val print_theorems: theory -> unit
  val print_theory: theory -> unit
end

signature PROOF_DISPLAY =
sig
  include BASIC_PROOF_DISPLAY
  val pprint_context: Proof.context -> pprint_args -> unit
  val pprint_typ: theory -> typ -> pprint_args -> unit
  val pprint_term: theory -> term -> pprint_args -> unit
  val pprint_ctyp: ctyp -> pprint_args -> unit
  val pprint_cterm: cterm -> pprint_args -> unit
  val pprint_thm: thm -> pprint_args -> unit
  val print_theorems_diff: theory -> theory -> unit
  val pretty_full_theory: bool -> theory -> Pretty.T
  val string_of_rule: Proof.context -> string -> thm -> string
  val print_results: bool -> Proof.context ->
    ((string * string) * (string * thm list) list) -> unit
  val present_results: Proof.context ->
    ((string * string) * (string * thm list) list) -> unit
  val pretty_consts: Proof.context ->
    (string * typ -> bool) -> (string * typ) list -> Pretty.T
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

fun pretty_theorems_diff prev_facts thy =
  let
    val ctxt = ProofContext.init thy;
    val facts = PureThy.facts_of thy;
    val thmss = Facts.fold_static (fn (name, ths) =>
      if exists (fn prev => Facts.defined prev name) prev_facts then I
      else cons (Facts.extern facts name, ths)) facts [];
  in Pretty.big_list "theorems:" (map (ProofContext.pretty_fact ctxt) (sort_wrt #1 thmss)) end;

fun print_theorems_diff prev_thy thy =
  Pretty.writeln (pretty_theorems_diff [PureThy.facts_of prev_thy] thy);

fun pretty_theorems thy = pretty_theorems_diff (map PureThy.facts_of (Theory.parents_of thy)) thy;
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

fun pretty_facts ctxt =
  flat o (separate [Pretty.fbrk, Pretty.str "and "]) o
    map (single o ProofContext.pretty_fact ctxt);

fun pretty_results ctxt ((kind, ""), facts) =
      Pretty.block (Pretty.str kind :: Pretty.brk 1 :: pretty_facts ctxt facts)
  | pretty_results ctxt ((kind, name), [fact]) = Pretty.blk (1,
      [Pretty.str (kind ^ " " ^ name ^ ":"), Pretty.fbrk, ProofContext.pretty_fact ctxt fact])
  | pretty_results ctxt ((kind, name), facts) = Pretty.blk (1,
      [Pretty.str (kind ^ " " ^ name ^ ":"), Pretty.fbrk,
        Pretty.blk (1, Pretty.str "(" :: pretty_facts ctxt facts @ [Pretty.str ")"])]);

fun name_results "" res = res
  | name_results name res =
      let
        val n = length (maps snd res);
        fun name_res (a, ths) i =
          let
            val m = length ths;
            val j = i + m;
          in
            if a <> "" then ((a, ths), j)
            else if m = n then ((name, ths), j)
            else ((Facts.string_of_ref (Facts.Named ((name, Position.none),
              SOME ([if m = 1 then Facts.Single i else Facts.FromTo (i, j - 1)]))), ths), j)
          end;
      in fst (fold_map name_res res 1) end;

in

fun print_results true = Pretty.writeln oo pretty_results
  | print_results false = K (K ());

fun present_results ctxt ((kind, name), res) =
  if kind = "" orelse kind = Thm.internalK then ()
  else (print_results true ctxt ((kind, name), res);
    Context.setmp_thread_data (SOME (Context.Proof ctxt))
      (Present.results kind) (name_results name res));

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

structure BasicProofDisplay: BASIC_PROOF_DISPLAY = ProofDisplay;
open BasicProofDisplay;

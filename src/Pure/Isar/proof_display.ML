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
  val print_theorems_diff: theory -> theory -> unit
  val string_of_rule: ProofContext.context -> string -> thm -> string
  val print_results: bool -> ProofContext.context ->
    ((string * string) * (string * thm list) list) -> unit
  val present_results: ProofContext.context ->
    ((string * string) * (string * thm list) list) -> unit
end

structure ProofDisplay: PROOF_DISPLAY =
struct


(* theorems and theory *)

fun pretty_theorems_diff prev_thms thy =
  let
    val ctxt = ProofContext.init thy;
    val (space, thms) = PureThy.theorems_of thy;
    val diff_thmss = Symtab.fold (fn fact =>
      if not (Symtab.member Thm.eq_thms prev_thms fact) then cons fact else I) thms [];
    val thmss = diff_thmss |> map (apfst (NameSpace.extern space)) |> Library.sort_wrt #1;
  in Pretty.big_list "theorems:" (map (ProofContext.pretty_fact ctxt) thmss) end;

fun print_theorems_diff prev_thy thy =
  Pretty.writeln (pretty_theorems_diff (#2 (PureThy.theorems_of prev_thy)) thy);

fun pretty_theorems thy = pretty_theorems_diff Symtab.empty thy;

val print_theorems = Pretty.writeln o pretty_theorems;

fun print_theory thy =
  Pretty.writeln (Pretty.chunks (Display.pretty_full_theory thy @ [pretty_theorems thy]));


(* refinement rule *)

fun pretty_rule ctxt s thm =
  Pretty.block [Pretty.str (s ^ " attempt to solve goal by exported rule:"),
    Pretty.fbrk, ProofContext.pretty_thm ctxt thm];

val string_of_rule = Pretty.string_of ooo pretty_rule;


(* results *)

local

fun pretty_facts ctxt =
  List.concat o (separate [Pretty.fbrk, Pretty.str "and "]) o
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
        val n = length (List.concat (map snd res));
        fun name_res (a, ths) i =
          let
            val m = length ths;
            val j = i + m;
          in
            if a <> "" then ((a, ths), j)
            else if m = n then ((name, ths), j)
            else if m = 1 then
              ((PureThy.string_of_thmref (NameSelection (name, [Single i])), ths), j)
            else ((PureThy.string_of_thmref (NameSelection (name, [FromTo (i, j - 1)])), ths), j)
          end;
      in fst (fold_map name_res res 1) end;

in

fun print_results true = Pretty.writeln oo pretty_results
  | print_results false = K (K ());

fun present_results ctxt ((kind, name), res) =
  if kind = "" orelse kind = PureThy.internalK then ()
  else (print_results true ctxt ((kind, name), res);
    Context.setmp (SOME (ProofContext.theory_of ctxt))
      (Present.results kind) (name_results name res));

end;

end;

structure BasicProofDisplay: BASIC_PROOF_DISPLAY = ProofDisplay;
open BasicProofDisplay;


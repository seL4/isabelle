(*  Title:      Pure/Isar/proof_display.ML
    ID:         $Id$
    Author:     Makarius

Printing of Isar proof configurations etc.
*)

signature PROOF_DISPLAY =
sig
  val string_of_rule: ProofContext.context -> string -> thm -> string
  val print_results: bool -> ProofContext.context ->
    ((string * string) * (string * thm list) list) -> unit
  val present_results: ProofContext.context ->
    ((string * string) * (string * thm list) list) -> unit
end

structure ProofDisplay: PROOF_DISPLAY =
struct

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

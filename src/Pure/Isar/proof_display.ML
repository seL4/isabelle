(*  Title:      Pure/Isar/proof_display.ML
    Author:     Makarius

Printing of theorems, goals, results etc.
*)

signature PROOF_DISPLAY =
sig
  val pp_context: Proof.context -> Pretty.T
  val pp_thm: (unit -> theory) -> thm -> Pretty.T
  val pp_typ: (unit -> theory) -> typ -> Pretty.T
  val pp_term: (unit -> theory) -> term -> Pretty.T
  val pp_ctyp: (unit -> theory) -> ctyp -> Pretty.T
  val pp_cterm: (unit -> theory) -> cterm -> Pretty.T
  val pretty_definitions: bool -> Proof.context -> Pretty.T
  val pretty_theorems_diff: bool -> theory list -> theory -> Pretty.T list
  val pretty_theorems: bool -> theory -> Pretty.T list
  val pretty_full_theory: bool -> theory -> Pretty.T
  val string_of_rule: Proof.context -> string -> thm -> string
  val pretty_goal_header: thm -> Pretty.T
  val string_of_goal: Proof.context -> thm -> string
  val pretty_goal_facts: Proof.context -> string -> thm list -> Pretty.T
  val method_error: string -> Position.T ->
    {context: Proof.context, facts: thm list, goal: thm} -> 'a Seq.result
  val print_results: bool -> Position.T -> Proof.context ->
    ((string * string) * (string * thm list) list) -> unit
  val print_consts: bool -> Position.T -> Proof.context ->
    (string * typ -> bool) -> (string * typ) list -> unit
end

structure Proof_Display: PROOF_DISPLAY =
struct

(** toplevel pretty printing **)

fun pp_context ctxt =
 (if Config.get ctxt Proof_Context.debug then
    Pretty.quote (Pretty.big_list "proof context:" (Proof_Context.pretty_context ctxt))
  else Pretty.str "<context>");

fun default_context mk_thy =
  (case Context.thread_data () of
    SOME (Context.Proof ctxt) => ctxt
  | SOME (Context.Theory thy) =>
      (case try Syntax.init_pretty_global thy of
        SOME ctxt => ctxt
      | NONE => Syntax.init_pretty_global (mk_thy ()))
  | NONE => Syntax.init_pretty_global (mk_thy ()));

fun pp_thm mk_thy th =
  Display.pretty_thm_raw (default_context mk_thy) {quote = true, show_hyps = false} th;

fun pp_typ mk_thy T = Pretty.quote (Syntax.pretty_typ (default_context mk_thy) T);
fun pp_term mk_thy t = Pretty.quote (Syntax.pretty_term (default_context mk_thy) t);

fun pp_ctyp mk_thy cT = pp_typ mk_thy (Thm.typ_of cT);
fun pp_cterm mk_thy ct = pp_term mk_thy (Thm.term_of ct);



(** theory content **)

(* theorems and theory *)

fun pretty_theorems_diff verbose prev_thys thy =
  let
    val pretty_fact = Proof_Context.pretty_fact (Proof_Context.init_global thy);
    val facts = Global_Theory.facts_of thy;
    val thmss = Facts.dest_static verbose (map Global_Theory.facts_of prev_thys) facts;
    val prts = map #1 (sort_by (#1 o #2) (map (`pretty_fact) thmss));
  in if null prts then [] else [Pretty.big_list "theorems:" prts] end;

fun pretty_theorems verbose thy =
  pretty_theorems_diff verbose (Theory.parents_of thy) thy;

fun pretty_full_theory verbose thy =
  Pretty.chunks (Display.pretty_full_theory verbose thy @ pretty_theorems verbose thy);


(* definitions *)

fun pretty_definitions verbose ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;

    val const_space = Proof_Context.const_space ctxt;
    val type_space = Proof_Context.type_space ctxt;
    val item_space = fn Defs.Const => const_space | Defs.Type => type_space;
    fun prune_item (k, c) = not verbose andalso Name_Space.is_concealed (item_space k) c;

    fun markup_extern_item (kind, name) =
      let val (markup, xname) = Name_Space.markup_extern ctxt (item_space kind) name
      in (markup, (kind, xname)) end;

    fun pretty_entry ((markup, (kind, xname)), args) =
      let
        val prt_prefix =
          if kind = Defs.Type then [Pretty.keyword1 "type", Pretty.brk 1] else [];
        val prt_item = Pretty.mark_str (markup, xname);
        val prt_args = Defs.pretty_args ctxt args;
      in Pretty.block (prt_prefix @ [prt_item] @ prt_args) end;

    fun sort_items f = sort (Defs.item_ord o apply2 (snd o f));

    fun pretty_reduct (lhs, rhs) = Pretty.block
      ([pretty_entry lhs, Pretty.str "  ->", Pretty.brk 2] @
        Pretty.commas (map pretty_entry (sort_items fst rhs)));

    fun pretty_restrict (entry, name) =
      Pretty.block ([pretty_entry entry, Pretty.brk 2, Pretty.str ("(from " ^ quote name ^ ")")]);

    val defs = Theory.defs_of thy;
    val {restricts, reducts} = Defs.dest defs;

    val (reds1, reds2) =
      filter_out (prune_item o #1 o #1) reducts
      |> map (fn (lhs, rhs) =>
        (apfst markup_extern_item lhs, map (apfst markup_extern_item) (filter_out (prune_item o fst) rhs)))
      |> sort_items (#1 o #1)
      |> filter_out (null o #2)
      |> List.partition (Defs.plain_args o #2 o #1);

    val rests = restricts |> map (apfst (apfst markup_extern_item)) |> sort_items (#1 o #1);
  in
    Pretty.big_list "definitions:"
      [Pretty.big_list "non-overloaded LHS:" (map pretty_reduct reds1),
       Pretty.big_list "overloaded LHS:" (map pretty_reduct reds2),
       Pretty.big_list "pattern restrictions due to incomplete LHS:" (map pretty_restrict rests)]
  end;



(** proof items **)

(* refinement rule *)

fun pretty_rule ctxt s thm =
  Pretty.block [Pretty.str (s ^ " attempt to solve goal by exported rule:"),
    Pretty.fbrk, Display.pretty_thm ctxt thm];

val string_of_rule = Pretty.string_of ooo pretty_rule;


(* goals *)

local

fun subgoals 0 = []
  | subgoals 1 = [Pretty.brk 1, Pretty.str "(1 subgoal)"]
  | subgoals n = [Pretty.brk 1, Pretty.str ("(" ^ string_of_int n ^ " subgoals)")];

in

fun pretty_goal_header goal =
  Pretty.block ([Pretty.keyword1 "goal"] @ subgoals (Thm.nprems_of goal) @ [Pretty.str ":"]);

end;

fun string_of_goal ctxt goal =
  Pretty.string_of (Pretty.chunks [pretty_goal_header goal, Goal_Display.pretty_goal ctxt goal]);


(* goal facts *)

fun pretty_goal_facts ctxt s ths =
  (Pretty.block o Pretty.fbreaks)
    [if s = "" then Pretty.str "this:"
     else Pretty.block [Pretty.keyword1 s, Pretty.brk 1, Pretty.str "this:"],
     Proof_Context.pretty_fact ctxt ("", ths)];


(* method_error *)

fun method_error kind pos {context = ctxt, facts, goal} = Seq.Error (fn () =>
  let
    val pr_header =
      "Failed to apply " ^ (if kind = "" then "" else kind ^ " ") ^
      "proof method" ^ Position.here pos ^ ":\n";
    val pr_facts =
      if null facts then ""
      else Pretty.string_of (pretty_goal_facts ctxt "using" facts) ^ "\n";
    val pr_goal = string_of_goal ctxt goal;
  in pr_header ^ pr_facts ^ pr_goal end);


(* results *)

fun position_markup pos = Pretty.mark (Position.markup pos Markup.position);

local

fun pretty_fact_name pos (kind, "") = position_markup pos (Pretty.keyword1 kind)
  | pretty_fact_name pos (kind, name) =
      Pretty.block [position_markup pos (Pretty.keyword1 kind), Pretty.brk 1,
        Pretty.str (Long_Name.base_name name), Pretty.str ":"];

fun pretty_facts ctxt =
  flat o (separate [Pretty.fbrk, Pretty.keyword2 "and", Pretty.str " "]) o
    map (single o Proof_Context.pretty_fact ctxt);

in

fun print_results do_print pos ctxt ((kind, name), facts) =
  if not do_print orelse kind = "" then ()
  else if name = "" then
    (Output.state o Pretty.string_of)
      (Pretty.block (position_markup pos (Pretty.keyword1 kind) :: Pretty.brk 1 ::
        pretty_facts ctxt facts))
  else
    (Output.state o Pretty.string_of)
      (case facts of
        [fact] => Pretty.blk (1, [pretty_fact_name pos (kind, name), Pretty.fbrk,
          Proof_Context.pretty_fact ctxt fact])
      | _ => Pretty.blk (1, [pretty_fact_name pos (kind, name), Pretty.fbrk,
          Pretty.blk (1, Pretty.str "(" :: pretty_facts ctxt facts @ [Pretty.str ")"])]));

end;


(* consts *)

local

fun pretty_var ctxt (x, T) =
  Pretty.block [Pretty.str x, Pretty.str " ::", Pretty.brk 1,
    Pretty.quote (Syntax.pretty_typ ctxt T)];

fun pretty_vars pos ctxt kind vs =
  Pretty.block (Pretty.fbreaks (position_markup pos (Pretty.str kind) :: map (pretty_var ctxt) vs));

fun pretty_consts pos ctxt pred cs =
  (case filter pred (#1 (Proof_Context.inferred_fixes ctxt)) of
    [] => pretty_vars pos ctxt "constants" cs
  | ps => Pretty.chunks [pretty_vars pos ctxt "parameters" ps, pretty_vars pos ctxt "constants" cs]);

in

fun print_consts do_print pos ctxt pred cs =
  if not do_print orelse null cs then ()
  else Output.state (Pretty.string_of (pretty_consts pos ctxt pred cs));

end;

end;

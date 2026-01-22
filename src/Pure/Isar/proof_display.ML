(*  Title:      Pure/Isar/proof_display.ML
    Author:     Makarius

Printing of theorems, goals, results etc.
*)

signature PROOF_DISPLAY =
sig
  val pretty_theory: bool -> Proof.context -> Pretty.T
  val pretty_definitions: bool -> Proof.context -> Pretty.T
  val pretty_theorems_diff: bool -> theory list -> Proof.context -> Pretty.T list
  val pretty_theorems: bool -> Proof.context -> Pretty.T list
  val string_of_rule: Proof.context -> string -> thm -> string
  val pretty_goal_header: thm -> Pretty.T
  val pretty_goal: Proof.context -> thm -> Pretty.T
  val pretty_goal_facts: Proof.context -> string -> thm list option -> Pretty.T list
  val pretty_goal_inst: Proof.context -> term list list -> thm -> Pretty.T list
  val method_error: string -> Position.T ->
    {context: Proof.context, facts: thm list, goal: thm} -> 'a Seq.result
  val show_results: bool Config.T
  val print_results: {interactive: bool, pos: Position.T} -> Proof.context ->
    ((string * string) * (string * thm list) list) -> unit
  val print_theorem: Position.T -> Proof.context -> string * thm list -> unit
  val print_consts: bool -> Position.T -> Proof.context ->
    (string * typ -> bool) -> (string * typ) list -> unit
  val markup_extern_label: Position.T -> (Markup.T * xstring) option
  val print_label: Position.T -> string
  val print_context_tracing: Context.generic * Position.T -> string
end

structure Proof_Display: PROOF_DISPLAY =
struct

(** theory content **)

fun pretty_theory verbose ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;

    fun prt_cls c = Syntax.pretty_sort ctxt [c];
    fun prt_sort S = Syntax.pretty_sort ctxt S;
    fun prt_arity t (c, Ss) = Syntax.pretty_arity ctxt (t, Ss, [c]);
    fun prt_typ ty = Pretty.quote (Syntax.pretty_typ ctxt ty);
    val prt_typ_no_tvars = prt_typ o Logic.unvarifyT_global;
    fun prt_term t = Pretty.quote (Syntax.pretty_term ctxt t);
    val prt_term_no_vars = prt_term o Logic.unvarify_global;
    fun prt_const (c, ty) = [Pretty.marks_str c, Pretty.str " ::", Pretty.brk 1, prt_typ_no_tvars ty];

    fun pretty_classrel (c, []) = prt_cls c
      | pretty_classrel (c, cs) = Pretty.block
          (prt_cls c :: Pretty.str " <" :: Pretty.brk 1 :: Pretty.commas (map prt_cls cs));

    fun pretty_default S = Pretty.block
      [Pretty.str "default sort:", Pretty.brk 1, prt_sort S];

    val tfrees = map (fn v => TFree (v, []));
    fun pretty_type syn (t, Type.Logical_Type n) =
          if syn then NONE
          else SOME (prt_typ (Type (t, tfrees (Name.invent_global_types n))))
      | pretty_type syn (t, Type.Abbreviation (vs, U, syn')) =
          if syn <> syn' then NONE
          else SOME (Pretty.block
            [prt_typ (Type (t, tfrees vs)), Pretty.str " =", Pretty.brk 1, prt_typ U])
      | pretty_type syn (t, Type.Nonterminal) =
          if not syn then NONE
          else SOME (prt_typ (Type (t, [])));

    val pretty_arities = maps (fn (t, ars) => map (prt_arity t) ars);

    fun pretty_abbrev (c, (ty, t)) = Pretty.block
      (prt_const (c, ty) @ [Pretty.str " \<equiv>", Pretty.brk 1, prt_term_no_vars t]);

    val tsig = Sign.tsig_of thy;
    val consts = Sign.consts_of thy;
    val {const_space, constants, constraints} = Consts.dest consts;
    val {classes, default, types, ...} = Type.rep_tsig tsig;
    val type_space = Type.type_space tsig;
    val (class_space, class_algebra) = classes;
    val classes = Sorts.classes_of class_algebra;
    val arities = Sorts.arities_of class_algebra;

    val clsses =
      Name_Space.extern_entries verbose ctxt class_space
        (map (fn ((c, _), cs) => (c, Sign.minimize_sort thy cs)) (Graph.dest classes))
      |> map (apfst #1);
    val tdecls = Name_Space.extern_table verbose ctxt types |> map (apfst #1);
    val arties =
      Name_Space.extern_entries verbose ctxt type_space (Symtab.dest arities)
      |> map (apfst #1);

    val cnsts = Name_Space.markups_entries verbose ctxt const_space constants;
    val log_cnsts = map_filter (fn (c, (ty, NONE)) => SOME (c, ty) | _ => NONE) cnsts;
    val abbrevs = map_filter (fn (c, (ty, SOME t)) => SOME (c, (ty, t)) | _ => NONE) cnsts;
    val cnstrs = Name_Space.markups_entries verbose ctxt const_space constraints;
  in
    Pretty.chunks
     [Pretty.big_list "classes:" (map pretty_classrel clsses),
      pretty_default default,
      Pretty.big_list "syntactic types:" (map_filter (pretty_type true) tdecls),
      Pretty.big_list "logical types:" (map_filter (pretty_type false) tdecls),
      Pretty.big_list "type arities:" (pretty_arities arties),
      Pretty.big_list "logical consts:" (map (Pretty.block o prt_const) log_cnsts),
      Pretty.big_list "abbreviations:" (map pretty_abbrev abbrevs),
      Pretty.big_list "constraints:" (map (Pretty.block o prt_const) cnstrs),
      Pretty.block
        (Pretty.breaks (Pretty.str "oracles:" ::
          map Pretty.marks_str (Thm.extern_oracles verbose ctxt)))]
  end;


(* theorems *)

fun pretty_theorems_diff verbose prev_thys ctxt =
  let
    val pretty_fact = Proof_Context.pretty_fact ctxt;
    val facts = Global_Theory.facts_of (Proof_Context.theory_of ctxt);
    val thmss = Facts.dest_static verbose (map Global_Theory.facts_of prev_thys) facts;
    val prts = map #1 (sort_by (#1 o #2) (map (`pretty_fact) thmss));
  in if null prts then [] else [Pretty.big_list "theorems:" prts] end;

fun pretty_theorems verbose ctxt =
  pretty_theorems_diff verbose (Theory.parents_of (Proof_Context.theory_of ctxt)) ctxt;


(* definitions *)

fun pretty_definitions verbose ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val context = Proof_Context.defs_context ctxt;

    val const_space = Proof_Context.const_space ctxt;
    val type_space = Proof_Context.type_space ctxt;
    val item_space = fn Defs.Const => const_space | Defs.Type => type_space;
    fun prune_item (k, c) = not verbose andalso Name_Space.is_concealed (item_space k) c;

    fun extern_item (kind, name) =
      let val xname = Name_Space.extern ctxt (item_space kind) name
      in (xname, (kind, name)) end;

    fun extern_item_ord ((xname1, (kind1, _)), (xname2, (kind2, _))) =
      (case Defs.item_kind_ord (kind1, kind2) of
        EQUAL => string_ord (xname1, xname2)
      | ord => ord);

    fun sort_items f = sort (extern_item_ord o apply2 f);

    fun pretty_entry ((_: string, item), args) = Defs.pretty_entry context (item, args);

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
        (apfst extern_item lhs, map (apfst extern_item) (filter_out (prune_item o fst) rhs)))
      |> sort_items (#1 o #1)
      |> filter_out (null o #2)
      |> List.partition (Defs.plain_args o #2 o #1);

    val rests = restricts |> map (apfst (apfst extern_item)) |> sort_items (#1 o #1);
  in
    Pretty.big_list "definitions:"
      (map (Pretty.text_fold o single)
        [Pretty.big_list "non-overloaded LHS:" (map pretty_reduct reds1),
         Pretty.big_list "overloaded LHS:" (map pretty_reduct reds2),
         Pretty.big_list "pattern restrictions due to incomplete LHS:" (map pretty_restrict rests)])
  end;



(** proof items **)

(* refinement rule *)

fun pretty_rule ctxt s thm =
  Pretty.block [Pretty.str (s ^ " attempt to solve goal by exported rule:"),
    Pretty.fbrk, Thm.pretty_thm ctxt thm];

val string_of_rule = Pretty.string_of ooo pretty_rule;


(* goals *)

local

fun subgoals 0 = []
  | subgoals 1 = [Pretty.brk 1, Pretty.str "(1 subgoal)"]
  | subgoals n = [Pretty.brk 1, Pretty.str ("(" ^ string_of_int n ^ " subgoals)")];

in

fun pretty_goal_header goal =
  Pretty.block ([Pretty.keyword1 "goal"] @ subgoals (Thm.nprems_of goal) @ [Pretty.str ":"]);

fun pretty_goal ctxt goal =
  Pretty.chunks [pretty_goal_header goal, Goal_Display.pretty_goal ctxt goal];

end;


(* goal facts *)

fun pretty_goal_facts _ _ NONE = []
  | pretty_goal_facts ctxt s (SOME ths) =
      (single o Pretty.block o Pretty.fbreaks)
        [if s = "" then Pretty.str "this:"
         else Pretty.block [Pretty.keyword1 s, Pretty.brk 1, Pretty.str "this:"],
         Proof_Context.pretty_fact ctxt ("", ths)];


(* goal instantiation *)

fun pretty_goal_inst ctxt propss goal =
  let
    val title = "goal instantiation:";

    fun prt_inst env =
      if Envir.is_empty env then []
      else
        let
          val Envir.Envir {tyenv, tenv, ...} = env;

          val prt_type = Syntax.pretty_typ ctxt;
          val prt_term = Syntax.pretty_term ctxt;

          fun instT v =
            let
              val T = TVar v;
              val T' = Envir.subst_type tyenv T;
            in if T = T' then NONE else SOME (prt_type T, prt_type T') end;

          fun inst v =
            let
              val t = Var v;
              val t' =
                Envir.subst_term (tyenv, tenv) t handle TYPE _ =>
                  Envir.subst_term (tyenv, tenv) (Envir.subst_term_types tyenv t);
            in if t aconv t' then NONE else SOME (prt_term t, prt_term t') end;

          fun inst_pair (x, y) = Pretty.item [x, Pretty.str " \<leadsto>", Pretty.brk 1, y];

          val prts =
            ((fold o fold) Term.add_tvars propss [] |> sort Term_Ord.tvar_ord |> map_filter instT) @
            ((fold o fold) Term.add_vars propss [] |> sort Term_Ord.var_ord |> map_filter inst);
        in if null prts then [] else [Pretty.big_list title (map inst_pair prts)] end;

    exception LOST_STRUCTURE;
    fun goal_matcher () =
      let
        val concl =
          Logic.unprotect (Thm.concl_of goal)
            handle TERM _ => raise LOST_STRUCTURE;
        val goal_propss = filter_out null propss;
        val results =
          Logic.dest_conjunction_balanced (length goal_propss) concl
          |> map2 Logic.dest_conjunction_balanced (map length goal_propss)
            handle TERM _ => raise LOST_STRUCTURE;
      in
        Unify.matcher (Context.Proof ctxt)
          (map (Soft_Type_System.purge ctxt) (flat goal_propss)) (flat results)
      end;

    fun failure msg = (warning (title ^ " " ^ msg); []);
  in
    (case goal_matcher () of
      SOME env => prt_inst env
    | NONE => failure "match failed")
    handle LOST_STRUCTURE => failure "lost goal structure"
  end;


(* method_error *)

fun method_error kind pos {context = ctxt, facts, goal} = Seq.Error (fn () =>
  let
    val pr_header =
      Pretty.block0
       ([Pretty.str ("Failed to apply " ^ (if kind = "" then "" else kind ^ " ") ^ "proof method")]
         @ Pretty.here pos @ [Pretty.str ":"]);
    val pr_facts =
      if null facts then []
      else [Pretty.chunks (pretty_goal_facts ctxt "using" (SOME facts))];
    val pr_goal = pretty_goal ctxt goal;
  in Pretty.string_of (Pretty.chunks ([pr_header] @ pr_facts @ [pr_goal])) end);


(* results *)

val interactive =
  Config.declare_bool ("interactive", \<^here>) (K false);

val show_results =
  Attrib.setup_config_bool \<^binding>\<open>show_results\<close>
    (fn context =>
      Config.get_generic context interactive orelse
      Options.default_bool \<^system_option>\<open>show_results\<close>);

fun no_print int ctxt = not (Config.get (Config.put interactive int ctxt) show_results);

local

fun pretty_fact_name pos (kind, "") = Pretty.mark_position pos (Pretty.keyword1 kind)
  | pretty_fact_name pos (kind, name) =
      Pretty.block [Pretty.mark_position pos (Pretty.keyword1 kind), Pretty.brk 1,
        Pretty.str (Long_Name.base_name name), Pretty.str ":"];

fun pretty_facts ctxt =
  flat o (separate [Pretty.fbrk, Pretty.keyword2 "and", Pretty.str " "]) o
    map (single o Proof_Context.pretty_fact ctxt);

in

fun print_results {interactive, pos} ctxt ((kind, name), facts) =
  if kind = "" orelse no_print interactive ctxt then ()
  else if name = "" then
    Pretty.writeln_urgent
      (Pretty.block (Pretty.mark_position pos (Pretty.keyword1 kind) :: Pretty.brk 1 ::
        pretty_facts ctxt facts))
  else
    Pretty.writeln_urgent
      (case facts of
        [fact] => Pretty.block1 [pretty_fact_name pos (kind, name), Pretty.fbrk,
          Proof_Context.pretty_fact ctxt fact]
      | _ => Pretty.block1 [pretty_fact_name pos (kind, name), Pretty.fbrk,
          Pretty.block1 (Pretty.str "(" :: pretty_facts ctxt facts @ [Pretty.str ")"])]);

fun print_theorem pos ctxt fact =
  print_results {interactive = true, pos = pos} ctxt ((Thm.theoremK, ""), [fact]);

end;


(* consts *)

local

fun pretty_var ctxt (x, T) =
  Pretty.block [Pretty.str x, Pretty.str " ::", Pretty.brk 1,
    Pretty.quote (Syntax.pretty_typ ctxt T)];

fun pretty_vars pos ctxt kind vs =
  Pretty.block
    (Pretty.fbreaks (Pretty.mark_position pos (Pretty.mark_str kind) :: map (pretty_var ctxt) vs));

val fixes = (Markup.keyword2, "fixes");
val consts = (Markup.keyword1, "consts");

fun pretty_consts pos ctxt pred cs =
  (case filter pred (#1 (Proof_Context.inferred_fixes ctxt)) of
    [] => pretty_vars pos ctxt consts cs
  | ps => Pretty.chunks [pretty_vars pos ctxt fixes ps, pretty_vars pos ctxt consts cs]);

in

fun print_consts int pos ctxt pred cs =
  if null cs orelse no_print int ctxt then ()
  else Pretty.writeln (pretty_consts pos ctxt pred cs);

end;


(* position label *)

val command_prefix = Markup.commandN ^ ".";

fun markup_extern_label pos =
  Position.label_of pos |> Option.map (fn label =>
    (case try (unprefix command_prefix) label of
      SOME cmd => (Markup.keyword1, Long_Name.base_name cmd)
    | NONE => (Markup.empty, label)));

fun print_label pos =
  (case markup_extern_label pos of
    NONE => ""
  | SOME (m, s) => Markup.markup m s);


(* context tracing *)

fun context_type (Context.Theory _) = "theory"
  | context_type (Context.Proof ctxt) =
      if can Local_Theory.assert ctxt then "local_theory" else "Proof.context";

fun print_context_tracing (context, pos) =
  context_type context ^ (case print_label pos of "" => "" | s => " " ^ s) ^ Position.here pos;

end;

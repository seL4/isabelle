(*  Title:      HOL/Tools/recdef_package.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Wrapper module for Konrad Slind's TFL package.
*)

signature RECDEF_PACKAGE =
sig
  val quiet_mode: bool ref
  val print_recdefs: theory -> unit
  val get_recdef: theory -> string
    -> {simps: thm list, rules: thm list list, induct: thm, tcs: term list} option
  val simp_add: Context.generic attribute
  val simp_del: Context.generic attribute
  val cong_add: Context.generic attribute
  val cong_del: Context.generic attribute
  val wf_add: Context.generic attribute
  val wf_del: Context.generic attribute
  val add_recdef: bool -> xstring -> string -> ((bstring * string) * Attrib.src list) list ->
    Attrib.src option -> theory -> theory
      * {simps: thm list, rules: thm list list, induct: thm, tcs: term list}
  val add_recdef_i: bool -> xstring -> term -> ((bstring * term) * theory attribute list) list ->
    theory -> theory * {simps: thm list, rules: thm list list, induct: thm, tcs: term list}
  val defer_recdef: xstring -> string list -> (thmref * Attrib.src list) list
    -> theory -> theory * {induct_rules: thm}
  val defer_recdef_i: xstring -> term list -> (thm list * theory attribute list) list
    -> theory -> theory * {induct_rules: thm}
  val recdef_tc: bstring * Attrib.src list -> xstring -> int option -> theory -> Proof.state
  val recdef_tc_i: bstring * theory attribute list -> string -> int option
    -> theory -> Proof.state
  val setup: theory -> theory
end;

structure RecdefPackage: RECDEF_PACKAGE =
struct

val quiet_mode = Tfl.quiet_mode;
val message = Tfl.message;


(** recdef hints **)

(* type hints *)

type hints = {simps: thm list, congs: (string * thm) list, wfs: thm list};

fun mk_hints (simps, congs, wfs) = {simps = simps, congs = congs, wfs = wfs}: hints;
fun map_hints f ({simps, congs, wfs}: hints) = mk_hints (f (simps, congs, wfs));

fun map_simps f = map_hints (fn (simps, congs, wfs) => (f simps, congs, wfs));
fun map_congs f = map_hints (fn (simps, congs, wfs) => (simps, f congs, wfs));
fun map_wfs f = map_hints (fn (simps, congs, wfs) => (simps, congs, f wfs));

fun pretty_hints ({simps, congs, wfs}: hints) =
 [Pretty.big_list "recdef simp hints:" (map Display.pretty_thm simps),
  Pretty.big_list "recdef cong hints:" (map Display.pretty_thm (map #2 congs)),
  Pretty.big_list "recdef wf hints:" (map Display.pretty_thm wfs)];


(* congruence rules *)

local

val cong_head =
  fst o Term.dest_Const o Term.head_of o fst o Logic.dest_equals o Thm.concl_of;

fun prep_cong raw_thm =
  let val thm = safe_mk_meta_eq raw_thm in (cong_head thm, thm) end;

in

fun add_cong raw_thm congs =
  let val (c, thm) = prep_cong raw_thm
  in overwrite_warn (congs, (c, thm)) ("Overwriting recdef congruence rule for " ^ quote c) end;

fun del_cong raw_thm congs =
  let
    val (c, thm) = prep_cong raw_thm;
    val (del, rest) = Library.partition (Library.equal c o fst) congs;
  in if null del then (warning ("No recdef congruence rule for " ^ quote c); congs) else rest end;

val add_congs = foldr (uncurry add_cong);

end;



(** global and local recdef data **)

(* theory data *)

type recdef_info = {simps: thm list, rules: thm list list, induct: thm, tcs: term list};

structure GlobalRecdefData = TheoryDataFun
(struct
  val name = "HOL/recdef";
  type T = recdef_info Symtab.table * hints;

  val empty = (Symtab.empty, mk_hints ([], [], [])): T;
  val copy = I;
  val extend = I;
  fun merge _
   ((tab1, {simps = simps1, congs = congs1, wfs = wfs1}),
    (tab2, {simps = simps2, congs = congs2, wfs = wfs2})) : T =
      (Symtab.merge (K true) (tab1, tab2),
        mk_hints (Drule.merge_rules (simps1, simps2),
          Library.merge_alists congs1 congs2,
          Drule.merge_rules (wfs1, wfs2)));

  fun print thy (tab, hints) =
    (Pretty.strs ("recdefs:" :: map #1 (NameSpace.extern_table (Sign.const_space thy, tab))) ::
      pretty_hints hints) |> Pretty.chunks |> Pretty.writeln;
end);

val print_recdefs = GlobalRecdefData.print;


val get_recdef = Symtab.lookup o #1 o GlobalRecdefData.get;

fun put_recdef name info thy =
  let
    val (tab, hints) = GlobalRecdefData.get thy;
    val tab' = Symtab.update_new (name, info) tab
      handle Symtab.DUP _ => error ("Duplicate recursive function definition " ^ quote name);
  in GlobalRecdefData.put (tab', hints) thy end;

val get_global_hints = #2 o GlobalRecdefData.get;
val map_global_hints = GlobalRecdefData.map o apsnd;


(* proof data *)

structure LocalRecdefData = ProofDataFun
(struct
  val name = "HOL/recdef";
  type T = hints;
  val init = get_global_hints;
  fun print _ hints = pretty_hints hints |> Pretty.chunks |> Pretty.writeln;
end);

val get_local_hints = LocalRecdefData.get;
val map_local_hints = LocalRecdefData.map;


(* attributes *)

fun map_hints f (Context.Theory thy) = Context.Theory (map_global_hints f thy)
  | map_hints f (Context.Proof ctxt) = Context.Proof (map_local_hints f ctxt);

fun attrib f = Attrib.declaration (map_hints o f);

val simp_add = attrib (map_simps o Drule.add_rule);
val simp_del = attrib (map_simps o Drule.del_rule);
val cong_add = attrib (map_congs o add_cong);
val cong_del = attrib (map_congs o del_cong);
val wf_add = attrib (map_wfs o Drule.add_rule);
val wf_del = attrib (map_wfs o Drule.del_rule);


(* modifiers *)

val recdef_simpN = "recdef_simp";
val recdef_congN = "recdef_cong";
val recdef_wfN = "recdef_wf";

val recdef_modifiers =
 [Args.$$$ recdef_simpN -- Args.colon >> K ((I, Attrib.context simp_add): Method.modifier),
  Args.$$$ recdef_simpN -- Args.add -- Args.colon >> K (I, Attrib.context simp_add),
  Args.$$$ recdef_simpN -- Args.del -- Args.colon >> K (I, Attrib.context simp_del),
  Args.$$$ recdef_congN -- Args.colon >> K (I, Attrib.context cong_add),
  Args.$$$ recdef_congN -- Args.add -- Args.colon >> K (I, Attrib.context cong_add),
  Args.$$$ recdef_congN -- Args.del -- Args.colon >> K (I, Attrib.context cong_del),
  Args.$$$ recdef_wfN -- Args.colon >> K (I, Attrib.context wf_add),
  Args.$$$ recdef_wfN -- Args.add -- Args.colon >> K (I, Attrib.context wf_add),
  Args.$$$ recdef_wfN -- Args.del -- Args.colon >> K (I, Attrib.context wf_del)] @
  Clasimp.clasimp_modifiers;



(** prepare_hints(_i) **)

fun prepare_hints thy opt_src =
  let
    val ctxt0 = ProofContext.init thy;
    val ctxt =
      (case opt_src of
        NONE => ctxt0
      | SOME src => Method.only_sectioned_args recdef_modifiers I src ctxt0);
    val {simps, congs, wfs} = get_local_hints ctxt;
    val cs = local_claset_of ctxt;
    val ss = local_simpset_of ctxt addsimps simps;
  in (cs, ss, map #2 congs, wfs) end;

fun prepare_hints_i thy () =
  let
    val ctxt0 = ProofContext.init thy;
    val {simps, congs, wfs} = get_global_hints thy;
  in (local_claset_of ctxt0, local_simpset_of ctxt0 addsimps simps, map #2 congs, wfs) end;



(** add_recdef(_i) **)

fun requires_recdef thy = Theory.requires thy "Recdef" "recursive functions";

fun gen_add_recdef tfl_fn prep_att prep_hints not_permissive raw_name R eq_srcs hints thy =
  let
    val _ = requires_recdef thy;

    val name = Sign.intern_const thy raw_name;
    val bname = Sign.base_name name;
    val _ = message ("Defining recursive function " ^ quote name ^ " ...");

    val ((eq_names, eqs), raw_eq_atts) = apfst split_list (split_list eq_srcs);
    val eq_atts = map (map (prep_att thy)) raw_eq_atts;

    val (cs, ss, congs, wfs) = prep_hints thy hints;
    (*We must remove imp_cong to prevent looping when the induction rule
      is simplified. Many induction rules have nested implications that would
      give rise to looping conditional rewriting.*)
    val (thy, {rules = rules_idx, induct, tcs}) =
        tfl_fn not_permissive thy cs (ss delcongs [imp_cong])
               congs wfs name R eqs;
    val rules = map (map #1) (Library.partition_eq (Library.eq_snd (op =)) rules_idx);
    val simp_att = if null tcs then
      [Attrib.theory Simplifier.simp_add, RecfunCodegen.add NONE] else [];

    val ((simps' :: rules', [induct']), thy) =
      thy
      |> Theory.add_path bname
      |> PureThy.add_thmss
        ((("simps", List.concat rules), simp_att) :: ((eq_names ~~ rules) ~~ eq_atts))
      ||>> PureThy.add_thms [(("induct", induct), [])];
    val result = {simps = simps', rules = rules', induct = induct', tcs = tcs};
    val thy =
      thy
      |> put_recdef name result
      |> Theory.parent_path;
  in (thy, result) end;

val add_recdef = gen_add_recdef Tfl.define Attrib.global_attribute prepare_hints;
fun add_recdef_i x y z w = gen_add_recdef Tfl.define_i (K I) prepare_hints_i x y z w ();



(** defer_recdef(_i) **)

fun gen_defer_recdef tfl_fn app_thms raw_name eqs raw_congs thy =
  let
    val name = Sign.intern_const thy raw_name;
    val bname = Sign.base_name name;

    val _ = requires_recdef thy;
    val _ = message ("Deferred recursive function " ^ quote name ^ " ...");

    val (congs, thy1) = thy |> app_thms raw_congs;
    val (thy2, induct_rules) = tfl_fn thy1 congs name eqs;
    val ([induct_rules'], thy3) =
      thy2
      |> Theory.add_path bname
      |> PureThy.add_thms [(("induct_rules", induct_rules), [])]
      ||> Theory.parent_path;
  in (thy3, {induct_rules = induct_rules'}) end;

val defer_recdef = gen_defer_recdef Tfl.defer IsarThy.apply_theorems;
val defer_recdef_i = gen_defer_recdef Tfl.defer_i IsarThy.apply_theorems_i;



(** recdef_tc(_i) **)

fun gen_recdef_tc prep_att prep_name (bname, raw_atts) raw_name opt_i thy =
  let
    val name = prep_name thy raw_name;
    val atts = map (prep_att thy) raw_atts;
    val tcs =
      (case get_recdef thy name of
        NONE => error ("No recdef definition of constant: " ^ quote name)
      | SOME {tcs, ...} => tcs);
    val i = getOpt (opt_i, 1);
    val tc = List.nth (tcs, i - 1) handle Subscript =>
      error ("No termination condition #" ^ string_of_int i ^
        " in recdef definition of " ^ quote name);
  in IsarThy.theorem_i Drule.internalK (bname, atts) (HOLogic.mk_Trueprop tc, ([], [])) thy end;

val recdef_tc = gen_recdef_tc Attrib.global_attribute Sign.intern_const;
val recdef_tc_i = gen_recdef_tc (K I) (K I);



(** package setup **)

(* setup theory *)

val setup =
  GlobalRecdefData.init #>
  LocalRecdefData.init #>
  Attrib.add_attributes
   [(recdef_simpN, Attrib.common (Attrib.add_del_args simp_add simp_del),
      "declaration of recdef simp rule"),
    (recdef_congN, Attrib.common (Attrib.add_del_args cong_add cong_del),
      "declaration of recdef cong rule"),
    (recdef_wfN, Attrib.common (Attrib.add_del_args wf_add wf_del),
      "declaration of recdef wf rule")];


(* outer syntax *)

local structure P = OuterParse and K = OuterKeyword in

val hints =
  P.$$$ "(" |-- P.!!! (P.position (P.$$$ "hints" -- P.arguments) --| P.$$$ ")") >> Args.src;

val recdef_decl =
  Scan.optional (P.$$$ "(" -- P.!!! (P.$$$ "permissive" -- P.$$$ ")") >> K false) true --
  P.name -- P.term -- Scan.repeat1 (P.opt_thm_name ":" -- P.prop) -- Scan.option hints
  >> (fn ((((p, f), R), eqs), src) => #1 o add_recdef p f R (map P.triple_swap eqs) src);

val recdefP =
  OuterSyntax.command "recdef" "define general recursive functions (TFL)" K.thy_decl
    (recdef_decl >> Toplevel.theory);


val defer_recdef_decl =
  P.name -- Scan.repeat1 P.prop --
  Scan.optional (P.$$$ "(" |-- P.$$$ "congs" |-- P.!!! (P.xthms1 --| P.$$$ ")")) []
  >> (fn ((f, eqs), congs) => #1 o defer_recdef f eqs congs);

val defer_recdefP =
  OuterSyntax.command "defer_recdef" "defer general recursive functions (TFL)" K.thy_decl
    (defer_recdef_decl >> Toplevel.theory);

val recdef_tcP =
  OuterSyntax.command "recdef_tc" "recommence proof of termination condition (TFL)" K.thy_goal
    (P.opt_thm_name ":" -- P.xname -- Scan.option (P.$$$ "(" |-- P.nat --| P.$$$ ")")
      >> (fn ((thm_name, name), i) =>
        Toplevel.print o Toplevel.theory_to_proof (recdef_tc thm_name name i)));


val _ = OuterSyntax.add_keywords ["permissive", "congs", "hints"];
val _ = OuterSyntax.add_parsers [recdefP, defer_recdefP, recdef_tcP];

end;

end;

(*  Title:      HOL/Tools/recdef_package.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Wrapper module for Konrad Slind's TFL package.
*)

signature RECDEF_PACKAGE =
sig
  val quiet_mode: bool ref
  val print_recdefs: theory -> unit
  val get_recdef: theory -> string
    -> {simps: thm list, rules: thm list list, induct: thm, tcs: term list} option
  val simp_add_global: theory attribute
  val simp_del_global: theory attribute
  val cong_add_global: theory attribute
  val cong_del_global: theory attribute
  val wf_add_global: theory attribute
  val wf_del_global: theory attribute
  val simp_add_local: Proof.context attribute
  val simp_del_local: Proof.context attribute
  val cong_add_local: Proof.context attribute
  val cong_del_local: Proof.context attribute
  val wf_add_local: Proof.context attribute
  val wf_del_local: Proof.context attribute
  val add_recdef: bool -> xstring -> string -> ((bstring * string) * Args.src list) list ->
    Args.src option -> theory -> theory
      * {simps: thm list, rules: thm list list, induct: thm, tcs: term list}
  val add_recdef_i: bool -> xstring -> term -> ((bstring * term) * theory attribute list) list ->
    theory -> theory * {simps: thm list, rules: thm list list, induct: thm, tcs: term list}
  val add_recdef_old: xstring -> string -> ((bstring * string) * Args.src list) list ->
    simpset * thm list -> theory ->
    theory * {simps: thm list, rules: thm list list, induct: thm, tcs: term list}
  val defer_recdef: xstring -> string list -> (xstring * Args.src list) list
    -> theory -> theory * {induct_rules: thm}
  val defer_recdef_i: xstring -> term list -> (thm * theory attribute list) list
    -> theory -> theory * {induct_rules: thm}
  val recdef_tc: bstring * Args.src list -> xstring -> int option
    -> bool -> theory -> ProofHistory.T
  val recdef_tc_i: bstring * theory attribute list -> string -> int option
    -> bool -> theory -> ProofHistory.T
  val setup: (theory -> theory) list
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

val add_congs = curry (foldr (uncurry add_cong));

end;



(** global and local recdef data **)

(* theory data kind 'HOL/recdef' *)

type recdef_info = {simps: thm list, rules: thm list list, induct: thm, tcs: term list};

structure GlobalRecdefArgs =
struct
  val name = "HOL/recdef";
  type T = recdef_info Symtab.table * hints;

  val empty = (Symtab.empty, mk_hints ([], [], [])): T;
  val copy = I;
  val prep_ext = I;
  fun merge
   ((tab1, {simps = simps1, congs = congs1, wfs = wfs1}),
    (tab2, {simps = simps2, congs = congs2, wfs = wfs2})) =
      (Symtab.merge (K true) (tab1, tab2),
        mk_hints (Drule.merge_rules (simps1, simps2),
          Library.merge_alists congs1 congs2,
          Drule.merge_rules (wfs1, wfs2)));

  fun print sg (tab, hints) =
   (Pretty.strs ("recdefs:" :: map #1 (Sign.cond_extern_table sg Sign.constK tab)) ::
     pretty_hints hints) |> Pretty.chunks |> Pretty.writeln;
end;

structure GlobalRecdefData = TheoryDataFun(GlobalRecdefArgs);
val print_recdefs = GlobalRecdefData.print;


fun get_recdef thy name = Symtab.lookup (#1 (GlobalRecdefData.get thy), name);

fun put_recdef name info thy =
  let
    val (tab, hints) = GlobalRecdefData.get thy;
    val tab' = Symtab.update_new ((name, info), tab)
      handle Symtab.DUP _ => error ("Duplicate recursive function definition " ^ quote name);
  in GlobalRecdefData.put (tab', hints) thy end;

val get_global_hints = #2 o GlobalRecdefData.get;
val map_global_hints = GlobalRecdefData.map o apsnd;


(* proof data kind 'HOL/recdef' *)

structure LocalRecdefArgs =
struct
  val name = "HOL/recdef";
  type T = hints;
  val init = get_global_hints;
  fun print _ hints = pretty_hints hints |> Pretty.chunks |> Pretty.writeln;
end;

structure LocalRecdefData = ProofDataFun(LocalRecdefArgs);
val get_local_hints = LocalRecdefData.get;
val map_local_hints = LocalRecdefData.map;


(* attributes *)

local

fun global_local f g =
 (fn (thy, thm) => (map_global_hints (f (g thm)) thy, thm),
  fn (ctxt, thm) => (map_local_hints (f (g thm)) ctxt, thm));

fun mk_attr (add1, add2) (del1, del2) =
 (Attrib.add_del_args add1 del1, Attrib.add_del_args add2 del2);

in

val (simp_add_global, simp_add_local) = global_local map_simps (Drule.add_rules o single);
val (simp_del_global, simp_del_local) = global_local map_simps (Drule.del_rules o single);
val (cong_add_global, cong_add_local) = global_local map_congs add_cong;
val (cong_del_global, cong_del_local) = global_local map_congs del_cong;
val (wf_add_global, wf_add_local) = global_local map_wfs (Drule.add_rules o single);
val (wf_del_global, wf_del_local) = global_local map_wfs (Drule.del_rules o single);

val simp_attr = mk_attr (simp_add_global, simp_add_local) (simp_del_global, simp_del_local);
val cong_attr = mk_attr (cong_add_global, cong_add_local) (cong_del_global, cong_del_local);
val wf_attr = mk_attr (wf_add_global, wf_add_local) (wf_del_global, wf_del_local);

end;


(* modifiers *)

val recdef_simpN = "recdef_simp";
val recdef_congN = "recdef_cong";
val recdef_wfN = "recdef_wf";

val recdef_modifiers =
 [Args.$$$ recdef_simpN -- Args.colon >> K ((I, simp_add_local): Method.modifier),
  Args.$$$ recdef_simpN -- Args.add -- Args.colon >> K (I, simp_add_local),
  Args.$$$ recdef_simpN -- Args.del -- Args.colon >> K (I, simp_del_local),
  Args.$$$ recdef_congN -- Args.colon >> K (I, cong_add_local),
  Args.$$$ recdef_congN -- Args.add -- Args.colon >> K (I, cong_add_local),
  Args.$$$ recdef_congN -- Args.del -- Args.colon >> K (I, cong_del_local),
  Args.$$$ recdef_wfN -- Args.colon >> K (I, wf_add_local),
  Args.$$$ recdef_wfN -- Args.add -- Args.colon >> K (I, wf_add_local),
  Args.$$$ recdef_wfN -- Args.del -- Args.colon >> K (I, wf_del_local)] @
  Clasimp.clasimp_modifiers;



(** prepare_hints(_i) **)

fun prepare_hints thy opt_src =
  let
    val ctxt0 = ProofContext.init thy;
    val ctxt =
      (case opt_src of
        None => ctxt0
      | Some src => Method.only_sectioned_args recdef_modifiers I src ctxt0);
    val {simps, congs, wfs} = get_local_hints ctxt;
    val cs = Classical.get_local_claset ctxt;
    val ss = Simplifier.get_local_simpset ctxt addsimps simps;
  in (cs, ss, map #2 congs, wfs) end;

fun prepare_hints_i thy () =
  let val {simps, congs, wfs} = get_global_hints thy
  in (Classical.claset_of thy, Simplifier.simpset_of thy addsimps simps, map #2 congs, wfs) end;



(** add_recdef(_i) **)

fun requires_recdef thy = Theory.requires thy "Recdef" "recursive functions";

fun gen_add_recdef tfl_fn prep_att prep_hints strict raw_name R eq_srcs hints thy =
  let
    val _ = requires_recdef thy;

    val name = Sign.intern_const (Theory.sign_of thy) raw_name;
    val bname = Sign.base_name name;
    val _ = message ("Defining recursive function " ^ quote name ^ " ...");

    val ((eq_names, eqs), raw_eq_atts) = apfst split_list (split_list eq_srcs);
    val eq_atts = map (map (prep_att thy)) raw_eq_atts;

    val (cs, ss, congs, wfs) = prep_hints thy hints;
    val (thy, {rules = rules_idx, induct, tcs}) = tfl_fn strict thy cs ss congs wfs name R eqs;
    val rules = map (map #1) (Library.partition_eq Library.eq_snd rules_idx);
    val simp_att = if null tcs then [Simplifier.simp_add_global] else [];

    val case_numbers = map Library.string_of_int (1 upto Thm.nprems_of induct);
    val (thy, (simps' :: rules', [induct'])) =
      thy
      |> Theory.add_path bname
      |> PureThy.add_thmss ((("simps", flat rules), simp_att) :: ((eq_names ~~ rules) ~~ eq_atts))
      |>>> PureThy.add_thms [(("induct", induct), [RuleCases.case_names case_numbers])];
    val result = {simps = simps', rules = rules', induct = induct', tcs = tcs};
    val thy =
      thy
      |> put_recdef name result
      |> Theory.parent_path;
  in (thy, result) end;

val add_recdef = gen_add_recdef Tfl.define Attrib.global_attribute prepare_hints;
fun add_recdef_i x y z w = gen_add_recdef Tfl.define_i (K I) prepare_hints_i x y z w ();


(* add_recdef_old -- legacy interface *)

fun prepare_hints_old thy (ss, thms) =
  let val {simps, congs, wfs} = get_global_hints thy
  in (Classical.claset_of thy, ss addsimps simps, map #2 (add_congs thms congs), wfs) end;

val add_recdef_old = gen_add_recdef Tfl.define Attrib.global_attribute prepare_hints_old false;



(** defer_recdef(_i) **)

fun gen_defer_recdef tfl_fn app_thms raw_name eqs raw_congs thy =
  let
    val name = Sign.intern_const (Theory.sign_of thy) raw_name;
    val bname = Sign.base_name name;

    val _ = requires_recdef thy;
    val _ = message ("Deferred recursive function " ^ quote name ^ " ...");

    val (thy1, congs) = thy |> app_thms raw_congs;
    val (thy2, induct_rules) = tfl_fn thy1 congs name eqs;
    val (thy3, [induct_rules']) =
      thy2
      |> Theory.add_path bname
      |> PureThy.add_thms [(("induct_rules", induct_rules), [])]
      |>> Theory.parent_path;
  in (thy3, {induct_rules = induct_rules'}) end;

val defer_recdef = gen_defer_recdef Tfl.defer IsarThy.apply_theorems;
val defer_recdef_i = gen_defer_recdef Tfl.defer_i IsarThy.apply_theorems_i;



(** recdef_tc(_i) **)

fun gen_recdef_tc prep_att prep_name (bname, raw_atts) raw_name opt_i int thy =
  let
    val name = prep_name (Theory.sign_of thy) raw_name;
    val atts = map (prep_att thy) raw_atts;
    val tcs =
      (case get_recdef thy name of
        None => error ("No recdef definition of constant: " ^ quote name)
      | Some {tcs, ...} => tcs);
    val i = if_none opt_i 1;
    val tc = Library.nth_elem (i - 1, tcs) handle Library.LIST _ =>
      error ("No termination condition #" ^ string_of_int i ^
        " in recdef definition of " ^ quote name);
  in
    thy |> IsarThy.theorem_i Drule.internalK
      (((bname, atts), (HOLogic.mk_Trueprop tc, ([], []))), Comment.none) int
  end;

val recdef_tc = gen_recdef_tc Attrib.global_attribute Sign.intern_const;
val recdef_tc_i = gen_recdef_tc (K I) (K I);



(** package setup **)

(* setup theory *)

val setup =
 [GlobalRecdefData.init, LocalRecdefData.init,
  Attrib.add_attributes
   [(recdef_simpN, simp_attr, "declaration of recdef simp rule"),
    (recdef_congN, cong_attr, "declaration of recdef cong rule"),
    (recdef_wfN, wf_attr, "declaration of recdef wf rule")]];


(* outer syntax *)

local structure P = OuterParse and K = OuterSyntax.Keyword in

val hints =
  P.$$$ "(" |-- P.!!! (P.position (P.$$$ "hints" -- P.arguments) --| P.$$$ ")") >> Args.src;

val recdef_decl =
  Scan.optional (P.$$$ "(" -- P.!!! (P.$$$ "permissive" -- P.$$$ ")") >> K false) true --
  P.name -- P.term -- Scan.repeat1 (P.opt_thm_name ":" -- P.prop --| P.marg_comment)
    -- Scan.option hints
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


val recdef_tc_decl =
  P.opt_thm_name ":" -- P.xname -- Scan.option (P.$$$ "(" |-- P.nat --| P.$$$ ")")
    --| P.marg_comment;

fun mk_recdef_tc ((thm_name, name), i) = recdef_tc thm_name name i;

val recdef_tcP =
  OuterSyntax.command "recdef_tc" "recommence proof of termination condition (TFL)" K.thy_goal
    (recdef_tc_decl >> (Toplevel.print oo (Toplevel.theory_to_proof o mk_recdef_tc)));


val _ = OuterSyntax.add_keywords ["permissive", "congs", "hints"];
val _ = OuterSyntax.add_parsers [recdefP, defer_recdefP, recdef_tcP];

end;


end;

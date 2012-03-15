(*  Title:      HOL/Tools/recdef.ML
    Author:     Markus Wenzel, TU Muenchen

Wrapper module for Konrad Slind's TFL package.
*)

signature RECDEF =
sig
  val get_recdef: theory -> string
    -> {lhs: term, simps: thm list, rules: thm list list, induct: thm, tcs: term list} option
  val get_hints: Proof.context -> {simps: thm list, congs: (string * thm) list, wfs: thm list}
  val simp_add: attribute
  val simp_del: attribute
  val cong_add: attribute
  val cong_del: attribute
  val wf_add: attribute
  val wf_del: attribute
  val add_recdef: bool -> xstring -> string -> ((binding * string) * Attrib.src list) list ->
    Attrib.src option -> theory -> theory
      * {lhs: term, simps: thm list, rules: thm list list, induct: thm, tcs: term list}
  val add_recdef_i: bool -> xstring -> term -> ((binding * term) * attribute list) list ->
    theory -> theory * {lhs: term, simps: thm list, rules: thm list list, induct: thm, tcs: term list}
  val defer_recdef: xstring -> string list -> (Facts.ref * Attrib.src list) list
    -> theory -> theory * {induct_rules: thm}
  val defer_recdef_i: xstring -> term list -> thm list -> theory -> theory * {induct_rules: thm}
  val recdef_tc: bstring * Attrib.src list -> xstring -> int option -> bool ->
    local_theory -> Proof.state
  val recdef_tc_i: bstring * Attrib.src list -> string -> int option -> bool ->
    local_theory -> Proof.state
  val setup: theory -> theory
end;

structure Recdef: RECDEF =
struct


(** recdef hints **)

(* type hints *)

type hints = {simps: thm list, congs: (string * thm) list, wfs: thm list};

fun mk_hints (simps, congs, wfs) = {simps = simps, congs = congs, wfs = wfs}: hints;
fun map_hints f ({simps, congs, wfs}: hints) = mk_hints (f (simps, congs, wfs));

fun map_simps f = map_hints (fn (simps, congs, wfs) => (f simps, congs, wfs));
fun map_congs f = map_hints (fn (simps, congs, wfs) => (simps, f congs, wfs));
fun map_wfs f = map_hints (fn (simps, congs, wfs) => (simps, congs, f wfs));


(* congruence rules *)

local

val cong_head =
  fst o Term.dest_Const o Term.head_of o fst o Logic.dest_equals o Thm.concl_of;

fun prep_cong raw_thm =
  let val thm = safe_mk_meta_eq raw_thm in (cong_head thm, thm) end;

in

fun add_cong raw_thm congs =
  let
    val (c, thm) = prep_cong raw_thm;
    val _ = if AList.defined (op =) congs c
      then warning ("Overwriting recdef congruence rule for " ^ quote c)
      else ();
  in AList.update (op =) (c, thm) congs end;

fun del_cong raw_thm congs =
  let
    val (c, thm) = prep_cong raw_thm;
    val _ = if AList.defined (op =) congs c
      then ()
      else warning ("No recdef congruence rule for " ^ quote c);
  in AList.delete (op =) c congs end;

end;



(** global and local recdef data **)

(* theory data *)

type recdef_info = {lhs: term, simps: thm list, rules: thm list list, induct: thm, tcs: term list};

structure GlobalRecdefData = Theory_Data
(
  type T = recdef_info Symtab.table * hints;
  val empty = (Symtab.empty, mk_hints ([], [], [])): T;
  val extend = I;
  fun merge
   ((tab1, {simps = simps1, congs = congs1, wfs = wfs1}),
    (tab2, {simps = simps2, congs = congs2, wfs = wfs2})) : T =
      (Symtab.merge (K true) (tab1, tab2),
        mk_hints (Thm.merge_thms (simps1, simps2),
          AList.merge (op =) (K true) (congs1, congs2),
          Thm.merge_thms (wfs1, wfs2)));
);

val get_recdef = Symtab.lookup o #1 o GlobalRecdefData.get;

fun put_recdef name info thy =
  let
    val (tab, hints) = GlobalRecdefData.get thy;
    val tab' = Symtab.update_new (name, info) tab
      handle Symtab.DUP _ => error ("Duplicate recursive function definition " ^ quote name);
  in GlobalRecdefData.put (tab', hints) thy end;

val get_global_hints = #2 o GlobalRecdefData.get;


(* proof data *)

structure LocalRecdefData = Proof_Data
(
  type T = hints;
  val init = get_global_hints;
);

val get_hints = LocalRecdefData.get;
fun map_hints f = Context.mapping (GlobalRecdefData.map (apsnd f)) (LocalRecdefData.map f);


(* attributes *)

fun attrib f = Thm.declaration_attribute (map_hints o f);

val simp_add = attrib (map_simps o Thm.add_thm);
val simp_del = attrib (map_simps o Thm.del_thm);
val cong_add = attrib (map_congs o add_cong);
val cong_del = attrib (map_congs o del_cong);
val wf_add = attrib (map_wfs o Thm.add_thm);
val wf_del = attrib (map_wfs o Thm.del_thm);


(* modifiers *)

val recdef_simpN = "recdef_simp";
val recdef_congN = "recdef_cong";
val recdef_wfN = "recdef_wf";

val recdef_modifiers =
 [Args.$$$ recdef_simpN -- Args.colon >> K ((I, simp_add): Method.modifier),
  Args.$$$ recdef_simpN -- Args.add -- Args.colon >> K (I, simp_add),
  Args.$$$ recdef_simpN -- Args.del -- Args.colon >> K (I, simp_del),
  Args.$$$ recdef_congN -- Args.colon >> K (I, cong_add),
  Args.$$$ recdef_congN -- Args.add -- Args.colon >> K (I, cong_add),
  Args.$$$ recdef_congN -- Args.del -- Args.colon >> K (I, cong_del),
  Args.$$$ recdef_wfN -- Args.colon >> K (I, wf_add),
  Args.$$$ recdef_wfN -- Args.add -- Args.colon >> K (I, wf_add),
  Args.$$$ recdef_wfN -- Args.del -- Args.colon >> K (I, wf_del)] @
  Clasimp.clasimp_modifiers;



(** prepare_hints(_i) **)

fun prepare_hints thy opt_src =
  let
    val ctxt0 = Proof_Context.init_global thy;
    val ctxt =
      (case opt_src of
        NONE => ctxt0
      | SOME src => #2 (Method.syntax (Method.sections recdef_modifiers) src ctxt0));
    val {simps, congs, wfs} = get_hints ctxt;
    val ctxt' = ctxt
      |> Simplifier.map_simpset (fn ss => ss addsimps simps |> Simplifier.del_cong @{thm imp_cong});
  in (ctxt', rev (map snd congs), wfs) end;

fun prepare_hints_i thy () =
  let
    val ctxt = Proof_Context.init_global thy;
    val {simps, congs, wfs} = get_global_hints thy;
    val ctxt' = ctxt
      |> Simplifier.map_simpset (fn ss => ss addsimps simps |> Simplifier.del_cong @{thm imp_cong});
  in (ctxt', rev (map snd congs), wfs) end;



(** add_recdef(_i) **)

fun requires_recdef thy = Theory.requires thy "Old_Recdef" "recursive functions";

fun gen_add_recdef tfl_fn prep_att prep_hints not_permissive raw_name R eq_srcs hints thy =
  let
    val _ = legacy_feature "Old 'recdef' command -- use 'fun' or 'function' instead";
    val _ = requires_recdef thy;

    val name = Sign.intern_const thy raw_name;
    val bname = Long_Name.base_name name;
    val _ = writeln ("Defining recursive function " ^ quote name ^ " ...");

    val ((eq_names, eqs), raw_eq_atts) = apfst split_list (split_list eq_srcs);
    val eq_atts = map (map (prep_att thy)) raw_eq_atts;

    val (ctxt, congs, wfs) = prep_hints thy hints;
    (*We must remove imp_cong to prevent looping when the induction rule
      is simplified. Many induction rules have nested implications that would
      give rise to looping conditional rewriting.*)
    val ({lhs, rules = rules_idx, induct, tcs}, thy) =
      tfl_fn not_permissive ctxt congs wfs name R eqs thy;
    val rules = (map o map) fst (partition_eq (eq_snd (op = : int * int -> bool)) rules_idx);
    val simp_att =
      if null tcs then [Simplifier.simp_add, Nitpick_Simps.add, Code.add_default_eqn_attribute]
      else [];
    val ((simps' :: rules', [induct']), thy) =
      thy
      |> Sign.add_path bname
      |> Global_Theory.add_thmss
        (((Binding.name "simps", flat rules), simp_att) :: ((eq_names ~~ rules) ~~ eq_atts))
      ||>> Global_Theory.add_thms [((Binding.name "induct", induct), [])]
      ||> Spec_Rules.add_global Spec_Rules.Equational ([lhs], flat rules);
    val result = {lhs = lhs, simps = simps', rules = rules', induct = induct', tcs = tcs};
    val thy =
      thy
      |> put_recdef name result
      |> Sign.parent_path;
  in (thy, result) end;

val add_recdef = gen_add_recdef Tfl.define Attrib.attribute prepare_hints;
fun add_recdef_i x y z w = gen_add_recdef Tfl.define_i (K I) prepare_hints_i x y z w ();



(** defer_recdef(_i) **)

fun gen_defer_recdef tfl_fn eval_thms raw_name eqs raw_congs thy =
  let
    val name = Sign.intern_const thy raw_name;
    val bname = Long_Name.base_name name;

    val _ = requires_recdef thy;
    val _ = writeln ("Deferred recursive function " ^ quote name ^ " ...");

    val congs = eval_thms (Proof_Context.init_global thy) raw_congs;
    val (induct_rules, thy2) = tfl_fn congs name eqs thy;
    val ([induct_rules'], thy3) =
      thy2
      |> Sign.add_path bname
      |> Global_Theory.add_thms [((Binding.name "induct_rules", induct_rules), [])]
      ||> Sign.parent_path;
  in (thy3, {induct_rules = induct_rules'}) end;

val defer_recdef = gen_defer_recdef Tfl.defer Attrib.eval_thms;
val defer_recdef_i = gen_defer_recdef Tfl.defer_i (K I);



(** recdef_tc(_i) **)

fun gen_recdef_tc prep_att prep_name (bname, raw_atts) raw_name opt_i int lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    val name = prep_name thy raw_name;
    val atts = map (prep_att thy) raw_atts;
    val tcs =
      (case get_recdef thy name of
        NONE => error ("No recdef definition of constant: " ^ quote name)
      | SOME {tcs, ...} => tcs);
    val i = the_default 1 opt_i;
    val tc = nth tcs (i - 1) handle General.Subscript =>
      error ("No termination condition #" ^ string_of_int i ^
        " in recdef definition of " ^ quote name);
  in
    Specification.theorem "" NONE (K I)
      (Binding.conceal (Binding.name bname), atts) []
      (Element.Shows [(Attrib.empty_binding, [(HOLogic.mk_Trueprop tc, [])])]) int lthy
  end;

val recdef_tc = gen_recdef_tc Attrib.intern_src Sign.intern_const;
val recdef_tc_i = gen_recdef_tc (K I) (K I);



(** package setup **)

(* setup theory *)

val setup =
  Attrib.setup @{binding recdef_simp} (Attrib.add_del simp_add simp_del)
    "declaration of recdef simp rule" #>
  Attrib.setup @{binding recdef_cong} (Attrib.add_del cong_add cong_del)
    "declaration of recdef cong rule" #>
  Attrib.setup @{binding recdef_wf} (Attrib.add_del wf_add wf_del)
    "declaration of recdef wf rule";


(* outer syntax *)

val hints =
  Parse.$$$ "(" |--
    Parse.!!! (Parse.position (Parse.$$$ "hints" -- Args.parse) --| Parse.$$$ ")") >> Args.src;

val recdef_decl =
  Scan.optional
    (Parse.$$$ "(" -- Parse.!!! (Parse.$$$ "permissive" -- Parse.$$$ ")") >> K false) true --
  Parse.name -- Parse.term -- Scan.repeat1 (Parse_Spec.opt_thm_name ":" -- Parse.prop)
    -- Scan.option hints
  >> (fn ((((p, f), R), eqs), src) => #1 o add_recdef p f R (map Parse.triple_swap eqs) src);

val _ =
  Outer_Syntax.command "recdef" "define general recursive functions (TFL)" Keyword.thy_decl
    (recdef_decl >> Toplevel.theory);


val defer_recdef_decl =
  Parse.name -- Scan.repeat1 Parse.prop --
  Scan.optional
    (Parse.$$$ "(" |-- Parse.$$$ "congs" |-- Parse.!!! (Parse_Spec.xthms1 --| Parse.$$$ ")")) []
  >> (fn ((f, eqs), congs) => #1 o defer_recdef f eqs congs);

val _ =
  Outer_Syntax.command "defer_recdef" "defer general recursive functions (TFL)" Keyword.thy_decl
    (defer_recdef_decl >> Toplevel.theory);

val _ =
  Outer_Syntax.local_theory_to_proof' "recdef_tc" "recommence proof of termination condition (TFL)"
    Keyword.thy_goal
    ((Parse_Spec.opt_thm_name ":" >> apfst Binding.name_of) -- Parse.xname --
        Scan.option (Parse.$$$ "(" |-- Parse.nat --| Parse.$$$ ")")
      >> (fn ((thm_name, name), i) => recdef_tc thm_name name i));

end;

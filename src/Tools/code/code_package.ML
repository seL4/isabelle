(*  Title:      Tools/code/code_package.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Code generator interfaces and Isar setup.
*)

signature CODE_PACKAGE =
sig
  val eval_conv: theory
    -> (CodeThingol.code -> CodeThingol.typscheme * CodeThingol.iterm
       -> string list -> cterm -> thm)
    -> cterm -> thm;
  val eval_term: theory
    -> (CodeThingol.code -> CodeThingol.typscheme * CodeThingol.iterm
       -> string list -> term -> 'a)
    -> term -> 'a;
  val satisfies_ref: (unit -> bool) option ref;
  val satisfies: theory -> term -> string list -> bool;
  val codegen_shell_command: string (*theory name*) -> string (*cg expr*) -> unit;
end;

structure CodePackage : CODE_PACKAGE =
struct

(** code theorems **)

fun code_depgr thy [] = CodeFuncgr.make thy []
  | code_depgr thy consts =
      let
        val gr = CodeFuncgr.make thy consts;
        val select = Graph.all_succs gr consts;
      in
        gr
        |> Graph.subgraph (member (op =) select) 
        |> Graph.map_nodes ((apsnd o map) (AxClass.overload thy))
      end;

fun code_thms thy =
  Pretty.writeln o CodeFuncgr.pretty thy o code_depgr thy;

fun code_deps thy consts =
  let
    val gr = code_depgr thy consts;
    fun mk_entry (const, (_, (_, parents))) =
      let
        val name = CodeUnit.string_of_const thy const;
        val nameparents = map (CodeUnit.string_of_const thy) parents;
      in { name = name, ID = name, dir = "", unfold = true,
        path = "", parents = nameparents }
      end;
    val prgr = Graph.fold ((fn x => fn xs => xs @ [x]) o mk_entry) gr [];
  in Present.display_graph prgr end;


(** code generation interfaces **)

(* code data *)

structure Program = CodeDataFun
(
  type T = CodeThingol.code;
  val empty = CodeThingol.empty_code;
  fun merge _ = CodeThingol.merge_code;
  fun purge _ NONE _ = CodeThingol.empty_code
    | purge NONE _ _ = CodeThingol.empty_code
    | purge (SOME thy) (SOME cs) code =
        let
          val cs_exisiting =
            map_filter (CodeName.const_rev thy) (Graph.keys code);
          val dels = (Graph.all_preds code
              o map (CodeName.const thy)
              o filter (member (op =) cs_exisiting)
            ) cs;
        in Graph.del_nodes dels code end;
);

(* generic generation combinators *)

val ensure_const = CodeThingol.ensure_const;

fun perhaps_const thy algbr funcgr c trns =
  case try (CodeThingol.ensure_const thy algbr funcgr c) trns
   of SOME (c, trns) => (SOME c, trns)
    | NONE => (NONE, trns);

fun generate thy funcgr gen it =
  let
    val naming = NameSpace.qualified_names NameSpace.default_naming;
    val consttab = Consts.empty
      |> fold (fn c => Consts.declare true naming [] (c, CodeFuncgr.typ funcgr c))
           (CodeFuncgr.all funcgr);
    val algbr = (Code.operational_algebra thy, consttab);
  in   
    Program.change_yield thy
      (CodeThingol.transact (gen thy algbr funcgr it))
  end;

fun code thy permissive cs seris =
  let
    val code = Program.get thy;
    val seris' = map (fn (((target, module), file), args) =>
      CodeTarget.get_serializer thy target permissive module file args cs) seris;
  in (map (fn f => f code) seris' : unit list; ()) end;

fun raw_eval evaluate term_of thy g =
  let
    fun result (_, code) =
      let
        val CodeThingol.Fun ((vs, ty), [(([], t), _)]) =
          Graph.get_node code CodeName.value_name;
        val deps = Graph.imm_succs code CodeName.value_name;
        val code' = Graph.del_nodes [CodeName.value_name] code;
        val code'' = CodeThingol.project_code false [] (SOME deps) code';
      in ((code'', ((vs, ty), t), deps), code') end;
    fun h funcgr ct =
      let
        val ((code, vs_ty_t, deps), _) = term_of ct
          |> generate thy funcgr CodeThingol.ensure_value
          |> result
          ||> `(fn code' => Program.change thy (K code'));
      in g code vs_ty_t deps ct end;
  in evaluate thy h end;

fun eval_conv thy = raw_eval CodeFuncgr.eval_conv Thm.term_of thy;
fun eval_term thy = raw_eval CodeFuncgr.eval_term I thy;

val satisfies_ref : (unit -> bool) option ref = ref NONE;

fun satisfies thy t witnesses =
  let
    fun evl code ((vs, ty), t) deps _ =
      CodeTarget.eval_invoke thy ("CodePackage.satisfies_ref", satisfies_ref)
        code (t, ty) witnesses;
  in eval_term thy evl t end;

fun filter_generatable thy consts =
  let
    val (consts', funcgr) = CodeFuncgr.make_consts thy consts;
    val (consts'', _) = generate thy funcgr (fold_map ooo perhaps_const) consts';
    val consts''' = map_filter (fn (const, SOME _) => SOME const | (_, NONE) => NONE)
      (consts' ~~ consts'');
  in consts''' end;

fun generate_const_exprs thy raw_cs =
  let
    val (perm1, cs) = CodeUnit.read_const_exprs thy
      (filter_generatable thy) raw_cs;
    val (perm2, cs') = case generate thy (CodeFuncgr.make thy cs)
      (fold_map ooo ensure_const) cs
     of ([], _) => (true, NONE)
      | (cs, _) => (false, SOME cs);
  in (perm1 orelse perm2, cs') end;


(** code properties **)

fun mk_codeprops thy all_cs sel_cs =
  let
    fun select (thmref, thm) = case try (Thm.unvarify o Drule.zero_var_indexes) thm
     of NONE => NONE
      | SOME thm => let
          val t = (ObjectLogic.drop_judgment thy o Thm.prop_of) thm;
          val cs = fold_aterms (fn Const (c, ty) =>
            cons (AxClass.unoverload_const thy (c, ty)) | _ => I) t [];
        in if exists (member (op =) sel_cs) cs
          andalso forall (member (op =) all_cs) cs
          then SOME (thmref, thm) else NONE end;
    fun mk_codeprop (thmref, thm) =
      let
        val t = ObjectLogic.drop_judgment thy (Thm.prop_of thm);
        val ty_judg = fastype_of t;
        val tfrees1 = fold_aterms (fn Const (c, ty) =>
          Term.add_tfreesT ty | _ => I) t [];
        val vars = Term.add_frees t [];
        val tfrees2 = fold (Term.add_tfreesT o snd) vars [];
        val tfrees' = subtract (op =) tfrees2 tfrees1 |> map TFree;
        val ty = map Term.itselfT tfrees' @ map snd vars ---> ty_judg;
        val tfree_vars = map Logic.mk_type tfrees';
        val c = PureThy.string_of_thmref thmref
          |> NameSpace.explode
          |> (fn [x] => [x] | (x::xs) => xs)
          |> space_implode "_"
        val propdef = (((c, ty), tfree_vars @ map Free vars), t);
      in if c = "" then NONE else SOME (thmref, propdef) end;
  in
    PureThy.thms_containing thy ([], [])
    |> maps PureThy.selections
    |> map_filter select
    |> map_filter mk_codeprop
  end;

fun add_codeprops all_cs sel_cs thy =
  let
    val codeprops = mk_codeprops thy all_cs sel_cs;
    fun lift_name_yield f x = (Name.context, x) |> f ||> snd;
    fun add (thmref, (((raw_c, ty), ts), t)) (names, thy) =
      let
        val _ = warning ("Adding theorem " ^ quote (PureThy.string_of_thmref thmref)
          ^ " as code property " ^ quote raw_c);
        val ([raw_c'], names') = Name.variants [raw_c] names;
        val (const as Const (c, _), thy') = thy |> Sign.declare_const [] (raw_c', ty, NoSyn);
        val eq = Logic.mk_equals (list_comb (const, ts), t);
        val ([def], thy'') = thy' |> PureThy.add_defs_i false [((Thm.def_name raw_c', eq), [])];
      in ((c, def), (names', thy'')) end;
  in
    thy
    |> Sign.sticky_prefix "codeprop"
    |> lift_name_yield (fold_map add codeprops)
    ||> Sign.restore_naming thy
    |-> (fn c_thms => fold (Code.add_func o snd) c_thms #> pair c_thms)
  end;


(** interfaces and Isar setup **)

local

structure P = OuterParse
and K = OuterKeyword

fun code_cmd raw_cs seris thy =
  let
    val (permissive, cs) = generate_const_exprs thy raw_cs;
    val _ = code thy permissive cs seris;
  in () end;

fun code_thms_cmd thy =
  code_thms thy o snd o CodeUnit.read_const_exprs thy (fst o CodeFuncgr.make_consts thy);

fun code_deps_cmd thy =
  code_deps thy o snd o CodeUnit.read_const_exprs thy (fst o CodeFuncgr.make_consts thy);

fun code_props_cmd raw_cs seris thy =
  let
    val (_, all_cs) = generate_const_exprs thy ["*"];
    val (permissive, cs) = generate_const_exprs thy raw_cs;
    val (c_thms, thy') = add_codeprops (map (the o CodeName.const_rev thy) (these all_cs))
      (map (the o CodeName.const_rev thy) (these cs)) thy;
    val prop_cs = (filter_generatable thy' o map fst) c_thms;
    val _ = if null seris then () else (generate thy' (CodeFuncgr.make thy' prop_cs)
      (fold_map ooo ensure_const) prop_cs; ());
    val _ = if null seris then () else code thy' permissive
      (SOME (map (CodeName.const thy') prop_cs)) seris;
  in thy' end;

val (inK, module_nameK, fileK) = ("in", "module_name", "file");

fun code_exprP cmd =
  (Scan.repeat P.term
  -- Scan.repeat (P.$$$ inK |-- P.name
     -- Scan.option (P.$$$ module_nameK |-- P.name)
     -- Scan.option (P.$$$ fileK |-- P.name)
     -- Scan.optional (P.$$$ "(" |-- P.arguments --| P.$$$ ")") []
  ) >> (fn (raw_cs, seris) => cmd raw_cs seris));

val _ = OuterSyntax.keywords [inK, module_nameK, fileK];

val (codeK, code_thmsK, code_depsK, code_propsK) =
  ("export_code", "code_thms", "code_deps", "code_props");

in

val _ =
  OuterSyntax.command codeK "generate executable code for constants"
    K.diag (P.!!! (code_exprP code_cmd) >> (fn f => Toplevel.keep (f o Toplevel.theory_of)));

fun codegen_shell_command thyname cmd = Isar.toplevel (fn _ =>
  (use_thy thyname; case Scan.read OuterLex.stopper (P.!!! (code_exprP code_cmd)) ((filter OuterLex.is_proper o OuterSyntax.scan) cmd)
   of SOME f => (writeln "Now generating code..."; f (theory thyname))
    | NONE => error ("Bad directive " ^ quote cmd)))
  handle TOPLEVEL_ERROR => OS.Process.exit OS.Process.failure;

val _ =
  OuterSyntax.improper_command code_thmsK "print system of defining equations for code" OuterKeyword.diag
    (Scan.repeat P.term
      >> (fn cs => Toplevel.no_timing o Toplevel.unknown_theory
        o Toplevel.keep ((fn thy => code_thms_cmd thy cs) o Toplevel.theory_of)));

val _ =
  OuterSyntax.improper_command code_depsK "visualize dependencies of defining equations for code" OuterKeyword.diag
    (Scan.repeat P.term
      >> (fn cs => Toplevel.no_timing o Toplevel.unknown_theory
        o Toplevel.keep ((fn thy => code_deps_cmd thy cs) o Toplevel.theory_of)));

val _ =
  OuterSyntax.command code_propsK "generate characteristic properties for executable constants"
    K.thy_decl (P.!!! (code_exprP code_props_cmd) >> Toplevel.theory);

end; (*local*)

end; (*struct*)

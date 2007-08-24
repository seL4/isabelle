(*  Title:      Tools/code/code_package.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Code generator translation kernel.  Code generator Isar setup.
*)

signature CODE_PACKAGE =
sig
  (* interfaces *)
  val eval_conv: theory
    -> (CodeThingol.code -> CodeThingol.typscheme * CodeThingol.iterm
       -> string list -> cterm -> thm)
    -> cterm -> thm;
  val eval_term: theory
    -> (CodeThingol.code -> CodeThingol.typscheme * CodeThingol.iterm
       -> string list -> cterm -> 'a)
    -> cterm -> 'a;
  val satisfies_ref: bool option ref;
  val satisfies: theory -> cterm -> string list -> bool;
  val codegen_command: theory -> string -> unit;

  (* axiomatic interfaces *)
  type appgen;
  val add_appconst: string * appgen -> theory -> theory;
  val appgen_let: appgen;
  val appgen_if: appgen;
  val appgen_case: (theory -> term
    -> ((string * typ) list * ((term * typ) * (term * term) list)) option)
    -> appgen;

  val timing: bool ref;
end;

structure CodePackage : CODE_PACKAGE =
struct

open BasicCodeThingol;

(** code translation **)

(* theory data *)

type appgen = theory -> ((sort -> sort) * Sorts.algebra) * Consts.T
  -> CodeFuncgr.T
  -> (string * typ) * term list -> CodeThingol.transact -> iterm * CodeThingol.transact;

structure Appgens = TheoryDataFun
(
  type T = (int * (appgen * stamp)) Symtab.table;
  val empty = Symtab.empty;
  val copy = I;
  val extend = I;
  fun merge _ = Symtab.merge (fn ((bounds1, (_, stamp1)), (bounds2, (_, stamp2))) =>
    bounds1 = bounds2 andalso stamp1 = stamp2);
);

fun code_depgr thy [] = CodeFuncgr.make thy []
  | code_depgr thy consts =
      let
        val gr = CodeFuncgr.make thy consts;
        val select = Graph.all_succs gr consts;
      in
        gr
        |> Graph.subgraph (member (op =) select) 
        |> Graph.map_nodes ((apsnd o map) (Conv.fconv_rule (Class.overload thy)))
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


(* translation kernel *)

val value_name = "Isabelle_Eval.EVAL.EVAL";

fun ensure_def thy = CodeThingol.ensure_def
  (fn s => if s = value_name then "<term>" else CodeName.labelled_name thy s);

fun ensure_def_class thy (algbr as ((_, algebra), _)) funcgr class =
  let
    val superclasses = (Sorts.certify_sort algebra o Sorts.super_classes algebra) class;
    val (v, cs) = AxClass.params_of_class thy class;
    val class' = CodeName.class thy class;
    val classrels' = map (curry (CodeName.classrel thy) class) superclasses;
    val classops' = map (CodeName.const thy o fst) cs;
    val defgen_class =
      fold_map (ensure_def_class thy algbr funcgr) superclasses
      ##>> (fold_map (exprgen_typ thy algbr funcgr) o map snd) cs
      #>> (fn (superclasses, classoptyps) =>
        CodeThingol.Class (superclasses ~~ classrels', (unprefix "'" v, classops' ~~ classoptyps)))
  in
    ensure_def thy defgen_class ("generating class " ^ quote class) class'
    #> pair class'
  end
and ensure_def_classrel thy algbr funcgr (subclass, superclass) =
  ensure_def_class thy algbr funcgr subclass
  #>> (fn _ => CodeName.classrel thy (subclass, superclass))
and ensure_def_tyco thy algbr funcgr "fun" =
      pair "fun"
  | ensure_def_tyco thy algbr funcgr tyco =
      let
        val defgen_datatype =
          let
            val (vs, cos) = Code.get_datatype thy tyco;
          in
            fold_map (exprgen_tyvar_sort thy algbr funcgr) vs
            ##>> fold_map (fn (c, tys) =>
              fold_map (exprgen_typ thy algbr funcgr) tys
              #>> (fn tys' => (CodeName.const thy c, tys'))) cos
            #>> (fn (vs, cos) => CodeThingol.Datatype (vs, cos))
          end;
        val tyco' = CodeName.tyco thy tyco;
      in
        ensure_def thy defgen_datatype ("generating type constructor " ^ quote tyco) tyco'
        #> pair tyco'
      end
and exprgen_tyvar_sort thy (algbr as ((proj_sort, _), _)) funcgr (v, sort) trns =
  trns
  |> fold_map (ensure_def_class thy algbr funcgr) (proj_sort sort)
  |>> (fn sort => (unprefix "'" v, sort))
and exprgen_typ thy algbr funcgr (TFree vs) trns =
      trns
      |> exprgen_tyvar_sort thy algbr funcgr vs
      |>> (fn (v, sort) => ITyVar v)
  | exprgen_typ thy algbr funcgr (Type (tyco, tys)) trns =
      trns
      |> ensure_def_tyco thy algbr funcgr tyco
      ||>> fold_map (exprgen_typ thy algbr funcgr) tys
      |>> (fn (tyco, tys) => tyco `%% tys);

exception CONSTRAIN of (string * typ) * typ;
val timing = ref false;

fun exprgen_dicts thy (algbr as ((proj_sort, algebra), consts)) funcgr (ty_ctxt, sort_decl) =
  let
    val pp = Sign.pp thy;
    datatype typarg =
        Global of (class * string) * typarg list list
      | Local of (class * class) list * (string * (int * sort));
    fun class_relation (Global ((_, tyco), yss), _) class =
          Global ((class, tyco), yss)
      | class_relation (Local (classrels, v), subclass) superclass =
          Local ((subclass, superclass) :: classrels, v);
    fun type_constructor tyco yss class =
      Global ((class, tyco), (map o map) fst yss);
    fun type_variable (TFree (v, sort)) =
      let
        val sort' = proj_sort sort;
      in map_index (fn (n, class) => (Local ([], (v, (n, sort'))), class)) sort' end;
    val typargs = Sorts.of_sort_derivation pp algebra
      {class_relation = class_relation, type_constructor = type_constructor,
       type_variable = type_variable}
      (ty_ctxt, proj_sort sort_decl);
    fun mk_dict (Global (inst, yss)) =
          ensure_def_inst thy algbr funcgr inst
          ##>> (fold_map o fold_map) mk_dict yss
          #>> (fn (inst, dss) => DictConst (inst, dss))
      | mk_dict (Local (classrels, (v, (k, sort)))) =
          fold_map (ensure_def_classrel thy algbr funcgr) classrels
          #>> (fn classrels => DictVar (classrels, (unprefix "'" v, (k, length sort))))
  in
    fold_map mk_dict typargs
  end
and exprgen_dict_parms thy (algbr as (_, consts)) funcgr (c, ty_ctxt) =
  let
    val ty_decl = Consts.the_declaration consts c;
    val (tys, tys_decl) = pairself (curry (Consts.typargs consts) c) (ty_ctxt, ty_decl);
    val sorts = map (snd o dest_TVar) tys_decl;
  in
    fold_map (exprgen_dicts thy algbr funcgr) (tys ~~ sorts)
  end
and ensure_def_inst thy (algbr as ((_, algebra), _)) funcgr (class, tyco) trns =
  let
    val superclasses = (Sorts.certify_sort algebra o Sorts.super_classes algebra) class;
    val (var, classops) = try (AxClass.params_of_class thy) class |> the_default ("'a", [])
    val vs = Name.names (Name.declare var Name.context) "'a" (Sorts.mg_domain algebra tyco [class]);
    val arity_typ = Type (tyco, map TFree vs);
    fun gen_superarity superclass trns =
      trns
      |> ensure_def_class thy algbr funcgr superclass
      ||>> ensure_def_classrel thy algbr funcgr (class, superclass)
      ||>> exprgen_dicts thy algbr funcgr (arity_typ, [superclass])
      |>> (fn ((superclass, classrel), [DictConst (inst, dss)]) =>
            (superclass, (classrel, (inst, dss))));
    fun gen_classop_def (c, ty) trns =
      trns
      |> ensure_def_const thy algbr funcgr c
      ||>> exprgen_term thy algbr funcgr
            (Const (Class.inst_const thy (c, tyco), map_type_tfree (K arity_typ) ty));
    fun defgen_inst trns =
      trns
      |> ensure_def_class thy algbr funcgr class
      ||>> ensure_def_tyco thy algbr funcgr tyco
      ||>> fold_map (exprgen_tyvar_sort thy algbr funcgr) vs
      ||>> fold_map gen_superarity superclasses
      ||>> fold_map gen_classop_def classops
      |>> (fn ((((class, tyco), arity), superarities), classops) =>
             CodeThingol.Classinst ((class, (tyco, arity)), (superarities, classops)));
    val inst = CodeName.instance thy (class, tyco);
  in
    trns
    |> ensure_def thy defgen_inst ("generating instance " ^ quote class ^ " / " ^ quote tyco) inst
    |> pair inst
  end
and ensure_def_const thy (algbr as (_, consts)) funcgr c =
  let
    val c' = CodeName.const thy c;
    fun defgen_datatypecons trns =
      trns 
      |> ensure_def_tyco thy algbr funcgr
          ((the o Code.get_datatype_of_constr thy) c)
      |>> (fn _ => CodeThingol.Bot);
    fun defgen_classop trns =
      trns 
      |> ensure_def_class thy algbr funcgr
        ((the o AxClass.class_of_param thy) c)
      |>> (fn _ => CodeThingol.Bot);
    fun defgen_fun trns =
      let
        val raw_thms = CodeFuncgr.funcs funcgr c;
        val ty = (Logic.unvarifyT o CodeFuncgr.typ funcgr) c;
        val thms = if (null o Term.typ_tfrees) ty orelse (null o fst o strip_type) ty
          then raw_thms
          else map (CodeUnit.expand_eta 1) raw_thms;
        val timeap = if !timing then Output.timeap_msg ("time for " ^ c)
          else I;
        val vs = (map dest_TFree o Consts.typargs consts) (c, ty);
        val dest_eqthm =
          apfst (snd o strip_comb) o Logic.dest_equals o Logic.unvarify o prop_of;
        fun exprgen_eq (args, rhs) =
          fold_map (exprgen_term thy algbr funcgr) args
          ##>> exprgen_term thy algbr funcgr rhs;
      in
        trns
        |> fold_map (exprgen_tyvar_sort thy algbr funcgr) vs
        ||>> exprgen_typ thy algbr funcgr ty
        ||>> timeap (fold_map (exprgen_eq o dest_eqthm) thms)
        |>> (fn ((vs, ty), eqs) => CodeThingol.Fun ((vs, ty), eqs))
      end;
    val defgen = if (is_some o Code.get_datatype_of_constr thy) c
      then defgen_datatypecons
      else if (is_some o AxClass.class_of_param thy) c
      then defgen_classop
      else defgen_fun
  in
    ensure_def thy defgen ("generating constant " ^ CodeUnit.string_of_const thy c) c'
    #> pair c'
  end
and exprgen_term thy algbr funcgr (Const (c, ty)) trns =
      trns
      |> select_appgen thy algbr funcgr ((c, ty), [])
  | exprgen_term thy algbr funcgr (Free (v, ty)) trns =
      trns
      |> exprgen_typ thy algbr funcgr ty
      |>> (fn _ => IVar v)
  | exprgen_term thy algbr funcgr (Abs (raw_v, ty, raw_t)) trns =
      let
        val (v, t) = Syntax.variant_abs (raw_v, ty, raw_t);
      in
        trns
        |> exprgen_typ thy algbr funcgr ty
        ||>> exprgen_term thy algbr funcgr t
        |>> (fn (ty, t) => (v, ty) `|-> t)
      end
  | exprgen_term thy algbr funcgr (t as _ $ _) trns =
      case strip_comb t
       of (Const (c, ty), ts) =>
            trns
            |> select_appgen thy algbr funcgr ((c, ty), ts)
        | (t', ts) =>
            trns
            |> exprgen_term thy algbr funcgr t'
            ||>> fold_map (exprgen_term thy algbr funcgr) ts
            |>> (fn (t, ts) => t `$$ ts)
and appgen_default thy algbr funcgr ((c, ty), ts) trns =
  trns
  |> ensure_def_const thy algbr funcgr c
  ||>> fold_map (exprgen_typ thy algbr funcgr) ((fst o Term.strip_type) ty)
  ||>> exprgen_typ thy algbr funcgr ((snd o Term.strip_type) ty)
  ||>> exprgen_dict_parms thy algbr funcgr (c, ty)
  ||>> fold_map (exprgen_term thy algbr funcgr) ts
  |>> (fn ((((c, tys), ty), iss), ts) => IConst (c, (iss, tys)) `$$ ts)
and select_appgen thy algbr funcgr ((c, ty), ts) trns =
  case Symtab.lookup (Appgens.get thy) c
   of SOME (i, (appgen, _)) =>
        if length ts < i then
          let
            val k = length ts;
            val tys = (curry Library.take (i - k) o curry Library.drop k o fst o strip_type) ty;
            val ctxt = (fold o fold_aterms)
              (fn Free (v, _) => Name.declare v | _ => I) ts Name.context;
            val vs = Name.names ctxt "a" tys;
          in
            trns
            |> fold_map (exprgen_typ thy algbr funcgr) tys
            ||>> appgen thy algbr funcgr ((c, ty), ts @ map Free vs)
            |>> (fn (tys, t) => map2 (fn (v, _) => pair v) vs tys `|--> t)
          end
        else if length ts > i then
          trns
          |> appgen thy algbr funcgr ((c, ty), Library.take (i, ts))
          ||>> fold_map (exprgen_term thy algbr funcgr) (Library.drop (i, ts))
          |>> (fn (t, ts) => t `$$ ts)
        else
          trns
          |> appgen thy algbr funcgr ((c, ty), ts)
    | NONE =>
        trns
        |> appgen_default thy algbr funcgr ((c, ty), ts);


(* entrance points into translation kernel *)

fun ensure_def_const' thy algbr funcgr c trns =
  ensure_def_const thy algbr funcgr c trns
  handle CONSTRAIN ((c, ty), ty_decl) => error (
    "Constant " ^ c ^ " with most general type\n"
    ^ CodeUnit.string_of_typ thy ty
    ^ "\noccurs with type\n"
    ^ CodeUnit.string_of_typ thy ty_decl);

fun perhaps_def_const thy algbr funcgr c trns =
  case try (ensure_def_const thy algbr funcgr c) trns
   of SOME (c, trns) => (SOME c, trns)
    | NONE => (NONE, trns);

fun exprgen_term' thy algbr funcgr t trns =
  exprgen_term thy algbr funcgr t trns
  handle CONSTRAIN ((c, ty), ty_decl) => error ("In term " ^ (quote o Sign.string_of_term thy) t
    ^ ",\nconstant " ^ c ^ " with most general type\n"
    ^ CodeUnit.string_of_typ thy ty
    ^ "\noccurs with type\n"
    ^ CodeUnit.string_of_typ thy ty_decl);


(* parametrized application generators, for instantiation in object logic *)
(* (axiomatic extensions of translation kernel) *)

fun appgen_case dest_case_expr thy algbr funcgr (app as (c_ty, ts)) =
  let
    val SOME ([], ((st, sty), ds)) = dest_case_expr thy (list_comb (Const c_ty, ts));
    fun clause_gen (dt, bt) =
      exprgen_term thy algbr funcgr
        (map_aterms (fn Const (c_ty as (c, ty)) => Const
          (Class.unoverload_const thy c_ty, ty) | t => t) dt)
      ##>> exprgen_term thy algbr funcgr bt;
  in
    exprgen_term thy algbr funcgr st
    ##>> exprgen_typ thy algbr funcgr sty
    ##>> fold_map clause_gen ds
    ##>> appgen_default thy algbr funcgr app
    #>> (fn (((se, sty), ds), t0) => ICase (((se, sty), ds), t0))
  end;

fun appgen_let thy algbr funcgr (app as (_, [st, ct])) =
  exprgen_term thy algbr funcgr ct
  ##>> exprgen_term thy algbr funcgr st
  ##>> appgen_default thy algbr funcgr app
  #>> (fn (((v, ty) `|-> be, se), t0) =>
            ICase (CodeThingol.collapse_let (((v, ty), se), be), t0)
        | (_, t0) => t0);

fun appgen_if thy algbr funcgr (app as (_, [tb, tt, tf])) =
  exprgen_term thy algbr funcgr tb
  ##>> exprgen_typ thy algbr funcgr (Type ("bool", []))
  ##>> exprgen_term thy algbr funcgr (Const ("True", Type ("bool", [])))
  ##>> exprgen_term thy algbr funcgr tt
  ##>> exprgen_term thy algbr funcgr (Const ("False", Type ("bool", [])))
  ##>> exprgen_term thy algbr funcgr tf
  ##>> appgen_default thy algbr funcgr app
  #>> (fn ((((((tb, B), T), tt), F), tf), t0) => ICase (((tb, B), [(T, tt), (F, tf)]), t0));

fun add_appconst (c, appgen) thy =
  let
    val i = (length o fst o strip_type o Sign.the_const_type thy) c;
    val _ = Program.change thy (K CodeThingol.empty_code);
  in
    Appgens.map (Symtab.update (c, (i, (appgen, stamp ())))) thy
  end;


(** code generation interfaces **)

(* generic generation combinators *)

fun generate thy funcgr gen it =
  let
    val naming = NameSpace.qualified_names NameSpace.default_naming;
    val consttab = Consts.empty
      |> fold (fn c => Consts.declare naming
           ((c, CodeFuncgr.typ funcgr c), true))
           (CodeFuncgr.all funcgr);
    val algbr = (Code.operational_algebra thy, consttab);
  in   
    Program.change_yield thy
      (CodeThingol.start_transact (gen thy algbr funcgr it))
    |> fst
  end;

fun raw_eval f thy g =
  let
    val value_name = "Isabelle_Eval.EVAL.EVAL";
    fun ensure_eval thy algbr funcgr t = 
      let
        val ty = fastype_of t;
        val vs = typ_tfrees ty;
        val defgen_eval =
          fold_map (exprgen_tyvar_sort thy algbr funcgr) vs
          ##>> exprgen_typ thy algbr funcgr ty
          ##>> exprgen_term' thy algbr funcgr t
          #>> (fn ((vs, ty), t) => CodeThingol.Fun ((vs, ty), [([], t)]));
        fun result (dep, code) =
          let
            val CodeThingol.Fun ((vs, ty), [([], t)]) = Graph.get_node code value_name;
            val deps = Graph.imm_succs code value_name;
            val code' = Graph.del_nodes [value_name] code;
            val code'' = CodeThingol.project_code false [] (SOME deps) code';
          in ((code'', ((vs, ty), t), deps), (dep, code')) end;
      in
        ensure_def thy defgen_eval "evaluation" value_name
        #> result
      end;
    fun h funcgr ct =
      let
        val (code, vs_ty_t, deps) = generate thy funcgr ensure_eval (Thm.term_of ct);
      in g code vs_ty_t deps ct end;
  in f thy h end;

fun eval_conv thy = raw_eval CodeFuncgr.eval_conv thy;
fun eval_term thy = raw_eval CodeFuncgr.eval_term thy;

val satisfies_ref : bool option ref = ref NONE;

fun satisfies thy ct witnesses =
  let
    fun evl code ((vs, ty), t) deps ct =
      let
        val t0 = Thm.term_of ct
        val _ = (Term.map_types o Term.map_atyps) (fn _ =>
          error ("Term " ^ Sign.string_of_term thy t0 ^ " contains polymorphic type"))
          t0;
      in
        CodeTarget.eval_term thy ("CodePackage.satisfies_ref", satisfies_ref)
          code (t, ty) witnesses
      end;
  in eval_term thy evl ct end;

fun filter_generatable thy consts =
  let
    val (consts', funcgr) = CodeFuncgr.make_consts thy consts;
    val consts'' = generate thy funcgr (fold_map ooo perhaps_def_const) consts';
    val consts''' = map_filter (fn (const, SOME _) => SOME const | (_, NONE) => NONE)
      (consts' ~~ consts'');
  in consts''' end;


(** toplevel interface and setup **)

local

structure P = OuterParse
and K = OuterKeyword

fun code raw_cs seris thy =
  let
    val (perm1, cs) = CodeUnit.read_const_exprs thy
      (filter_generatable thy) raw_cs;
    val (perm2, cs') = case generate thy (CodeFuncgr.make thy cs) (fold_map ooo ensure_def_const') cs
     of [] => (true, NONE)
      | cs => (false, SOME cs);
    val code = Program.get thy;
    val seris' = map (fn (((target, module), file), args) =>
      CodeTarget.get_serializer thy target (perm1 orelse perm2) module file args
        CodeName.labelled_name cs') seris;
  in
    (map (fn f => f code) seris' : unit list; ())
  end;

fun code_thms_cmd thy =
  code_thms thy o snd o CodeUnit.read_const_exprs thy (fst o CodeFuncgr.make_consts thy);

fun code_deps_cmd thy =
  code_deps thy o snd o CodeUnit.read_const_exprs thy (fst o CodeFuncgr.make_consts thy);

val (inK, module_nameK, fileK) = ("in", "module_name", "file");

val code_exprP =
  (Scan.repeat P.term
  -- Scan.repeat (P.$$$ inK |-- P.name
     -- Scan.option (P.$$$ module_nameK |-- P.name)
     -- Scan.option (P.$$$ fileK |-- P.name)
     -- Scan.optional (P.$$$ "(" |-- P.arguments --| P.$$$ ")") []
  ) >> (fn (raw_cs, seris) => code raw_cs seris));

val _ = OuterSyntax.add_keywords [inK, module_nameK, fileK];

val (codeK, code_thmsK, code_depsK) = ("export_code", "code_thms", "code_deps");

in

val codeP =
  OuterSyntax.improper_command codeK "generate executable code for constants"
    K.diag (P.!!! code_exprP >> (fn f => Toplevel.keep (f o Toplevel.theory_of)));

fun codegen_command thy cmd =
  case Scan.read OuterLex.stopper (P.!!! code_exprP) ((filter OuterLex.is_proper o OuterSyntax.scan) cmd)
   of SOME f => (writeln "Now generating code..."; f thy)
    | NONE => error ("Bad directive " ^ quote cmd);

val code_thmsP =
  OuterSyntax.improper_command code_thmsK "print system of defining equations for code" OuterKeyword.diag
    (Scan.repeat P.term
      >> (fn cs => Toplevel.no_timing o Toplevel.unknown_theory
        o Toplevel.keep ((fn thy => code_thms_cmd thy cs) o Toplevel.theory_of)));

val code_depsP =
  OuterSyntax.improper_command code_depsK "visualize dependencies of defining equations for code" OuterKeyword.diag
    (Scan.repeat P.term
      >> (fn cs => Toplevel.no_timing o Toplevel.unknown_theory
        o Toplevel.keep ((fn thy => code_deps_cmd thy cs) o Toplevel.theory_of)));

val _ = OuterSyntax.add_parsers [codeP, code_thmsP, code_depsP];

end; (* local *)

end; (* struct *)

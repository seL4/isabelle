(*  Title:      Pure/Tools/codegen_package.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Code generator from Isabelle theories to
intermediate language ("Thin-gol").
*)

signature CODEGEN_PACKAGE =
sig
  include BASIC_CODEGEN_THINGOL;
  val codegen_term: theory -> term -> thm * iterm;
  val eval_term: theory -> (string (*reference name!*) * 'a option ref) * term -> 'a;
  val const_of_idf: theory -> string -> string * typ;
  val get_root_module: theory -> CodegenThingol.module;

  type appgen;
  val add_appconst: string * appgen -> theory -> theory;
  val appgen_numeral: (theory -> term -> IntInf.int) -> appgen;
  val appgen_char: (term -> int option) -> appgen;
  val appgen_case: (theory -> term
    -> ((string * typ) list * ((term * typ) * (term * term) list)) option)
    -> appgen;
  val appgen_let: appgen;

  val print_code: theory -> unit;
  val purge_code: theory -> CodegenThingol.module;
  structure CodegenPackageData: THEORY_DATA;
  structure Code: CODE_DATA;
end;

structure CodegenPackage : CODEGEN_PACKAGE =
struct

open CodegenThingol;

(** preliminaries **)

val nsp_module = CodegenNames.nsp_module;
val nsp_class = CodegenNames.nsp_class;
val nsp_tyco = CodegenNames.nsp_tyco;
val nsp_inst = CodegenNames.nsp_inst;
val nsp_fun = CodegenNames.nsp_fun;
val nsp_classop = CodegenNames.nsp_classop;
val nsp_dtco = CodegenNames.nsp_dtco;
val nsp_eval = CodegenNames.nsp_eval;



(** code extraction **)

(* theory data *)

type appgen = theory -> ((sort -> sort) * Sorts.algebra) * Consts.T
  -> CodegenFuncgr.T
  -> bool * string list option -> (string * typ) * term list -> transact -> iterm * transact;

type appgens = (int * (appgen * stamp)) Symtab.table;

fun merge_appgens (x : appgens * appgens) =
  Symtab.merge (fn ((bounds1, (_, stamp1)), (bounds2, (_, stamp2))) =>
    bounds1 = bounds2 andalso stamp1 = stamp2) x;

structure Code = CodeDataFun
(struct
  val name = "Pure/code";
  type T = module;
  val empty = empty_module;
  fun merge _ = merge_module;
  fun purge _ _ = CodegenThingol.empty_module;
end);

structure CodegenPackageData = TheoryDataFun
(struct
  val name = "Pure/codegen_package";
  type T = appgens;
  val empty = Symtab.empty;
  val copy = I;
  val extend = I;
  fun merge _ = merge_appgens;
  fun print _ _ = ();
end);

val _ = Context.add_setup (Code.init #> CodegenPackageData.init);

fun print_code thy =
  let
    val code = Code.get thy;
  in (Pretty.writeln o Pretty.chunks) [pretty_module code, pretty_deps code] end;

fun purge_code thy = Code.change thy (K CodegenThingol.empty_module);


(* extraction kernel *)

fun check_strict has_seri x (false, _) =
      false
  | check_strict has_seri x (_, SOME targets) =
      not (has_seri targets x)
  | check_strict has_seri x (true, _) =
      true;

fun ensure_def_class thy algbr funcgr strct cls trns =
  let
    fun defgen_class thy (algbr as ((proj_sort, _), _)) funcgr strct cls trns =
      case CodegenNames.class_rev thy cls
       of SOME cls =>
            let
              val (v, cs) = (ClassPackage.the_consts_sign thy) cls;
              val superclasses = (proj_sort o Sign.super_classes thy) cls
              val idfs = map (CodegenNames.const thy o CodegenConsts.norm_of_typ thy) cs;
            in
              trns
              |> tracing (fn _ => "trying defgen class declaration for " ^ quote cls)
              |> fold_map (ensure_def_class thy algbr funcgr strct) superclasses
              ||>> (fold_map (exprgen_type thy algbr funcgr strct) o map snd) cs
              |-> (fn (supcls, memtypes) => succeed
                (Class (supcls, (unprefix "'" v, idfs ~~ memtypes))))
            end
        | _ =>
            trns
            |> fail ("No class definition found for " ^ quote cls);
    val cls' = CodegenNames.class thy cls;
  in
    trns
    |> tracing (fn _ => "generating class " ^ quote cls)
    |> ensure_def (defgen_class thy algbr funcgr strct) true ("generating class " ^ quote cls) cls'
    |> pair cls'
  end
and ensure_def_tyco thy algbr funcgr strct tyco trns =
  let
    val tyco' = CodegenNames.tyco thy tyco;
    val strict = check_strict (CodegenSerializer.tyco_has_serialization thy) tyco' strct;
    fun defgen_datatype thy algbr funcgr strct dtco trns =
      case CodegenNames.tyco_rev thy dtco
       of SOME dtco =>
         (case CodegenData.get_datatype thy dtco
             of SOME (vs, cos) =>
                  trns
                  |> tracing (fn _ => "trying defgen datatype for " ^ quote dtco)
                  |> fold_map (exprgen_tyvar_sort thy algbr funcgr strct) vs
                  ||>> fold_map (fn (c, tys) =>
                    fold_map (exprgen_type thy algbr funcgr strct) tys
                    #-> (fn tys' =>
                      pair ((CodegenNames.const thy o CodegenConsts.norm_of_typ thy)
                        (c, tys ---> Type (dtco, map TFree vs)), tys'))) cos
                  |-> (fn (vs, cos) => succeed (Datatype (vs, cos)))
              | NONE =>
                  trns
                  |> fail ("No datatype found for " ^ quote dtco))
        | NONE =>
            trns
            |> fail ("Not a type constructor: " ^ quote dtco)
  in
    trns
    |> tracing (fn _ => "generating type constructor " ^ quote tyco)
    |> ensure_def (defgen_datatype thy algbr funcgr strct) strict
        ("generating type constructor " ^ quote tyco) tyco'
    |> pair tyco'
  end
and exprgen_tyvar_sort thy (algbr as ((proj_sort, _), _)) funcgr strct (v, sort) trns =
  trns
  |> fold_map (ensure_def_class thy algbr funcgr strct) (proj_sort sort)
  |-> (fn sort => pair (unprefix "'" v, sort))
and exprgen_type thy algbr funcgr strct (TVar _) trns =
      error "TVar encountered in typ during code generation"
  | exprgen_type thy algbr funcgr strct (TFree vs) trns =
      trns
      |> exprgen_tyvar_sort thy algbr funcgr strct vs
      |-> (fn (v, sort) => pair (ITyVar v))
  | exprgen_type thy algbr funcgr strct (Type ("fun", [t1, t2])) trns =
      trns
      |> exprgen_type thy algbr funcgr strct t1
      ||>> exprgen_type thy algbr funcgr strct t2
      |-> (fn (t1', t2') => pair (t1' `-> t2'))
  | exprgen_type thy algbr funcgr strct (Type (tyco, tys)) trns =
      trns
      |> ensure_def_tyco thy algbr funcgr strct tyco
      ||>> fold_map (exprgen_type thy algbr funcgr strct) tys
      |-> (fn (tyco, tys) => pair (tyco `%% tys));

exception CONSTRAIN of (string * typ) * typ;

fun exprgen_typinst thy (algbr as ((proj_sort, algebra), consts)) funcgr strct (ty_ctxt, sort_decl) trns =
  let
    val pp = Sign.pp thy;
    datatype inst =
        Inst of (class * string) * inst list list
      | Contxt of (string * sort) * (class list * int);
    fun classrel (l as Contxt (v_sort, (classes, n)), _) class  =
          Contxt (v_sort, (class :: classes, n))
      | classrel (Inst ((_, tyco), lss), _) class =
          Inst ((class, tyco), lss);
    fun constructor tyco iss class =
      Inst ((class, tyco), (map o map) fst iss);
    fun variable (TFree (v, sort)) =
      let
        val sort' = proj_sort sort;
      in map_index (fn (n, class) => (Contxt ((v, sort'), ([], n)), class)) sort' end;
    val insts = Sorts.of_sort_derivation pp algebra
      {classrel = classrel, constructor = constructor, variable = variable}
      (ty_ctxt, proj_sort sort_decl);
    fun mk_dict (Inst (inst, instss)) trns =
          trns
          |> ensure_def_inst thy algbr funcgr strct inst
          ||>> (fold_map o fold_map) mk_dict instss
          |-> (fn (inst, instss) => pair (Instance (inst, instss)))
      | mk_dict (Contxt ((v, sort), (classes, k))) trns =
          trns
          |> fold_map (ensure_def_class thy algbr funcgr strct) classes
          |-> (fn classes => pair (Context (classes, (unprefix "'" v,
                if length sort = 1 then ~1 else k))))
  in
    trns
    |> fold_map mk_dict insts
  end
and exprgen_typinst_const thy (algbr as (_, consts)) funcgr strct (c, ty_ctxt) trns =
  let
    val c' = CodegenConsts.norm_of_typ thy (c, ty_ctxt)
    val idf = CodegenNames.const thy c';
    val ty_decl = Consts.declaration consts idf;
    val insts = (op ~~ o apsnd (map (snd o dest_TVar)) oo pairself)
      (curry (Consts.typargs consts) idf) (ty_ctxt, ty_decl);
    val _ = if exists not (map (Sign.of_sort thy) insts)
      then raise CONSTRAIN ((c, ty_decl), ty_ctxt) else ();
  in
    trns
    |> fold_map (exprgen_typinst thy algbr funcgr strct) insts
  end
and ensure_def_inst thy algbr funcgr strct (cls, tyco) trns =
  let
    fun defgen_inst thy (algbr as ((proj_sort, _), _)) funcgr strct inst trns =
      case CodegenNames.instance_rev thy inst
       of SOME (class, tyco) =>
            let
              val (vs, memdefs) = ClassPackage.the_inst_sign thy (class, tyco);
              val (_, members) = ClassPackage.the_consts_sign thy class;
              val arity_typ = Type (tyco, (map TFree vs));
              val superclasses = (proj_sort o Sign.super_classes thy) class
              fun gen_suparity supclass trns =
                trns
                |> ensure_def_class thy algbr funcgr strct supclass
                ||>> exprgen_typinst thy algbr funcgr strct (arity_typ, [supclass])
                |-> (fn (supclass, [Instance (supints, lss)]) => pair (supclass, (supints, lss)));
              fun gen_membr ((m0, ty0), (m, ty)) trns =
                trns
                |> ensure_def_const thy algbr funcgr strct (CodegenConsts.norm_of_typ thy (m0, ty0))
                ||>> exprgen_term thy algbr funcgr strct (Const (m, ty));
            in
              trns
              |> tracing (fn _ => "trying defgen class instance for (" ^ quote cls
                   ^ ", " ^ quote tyco ^ ")")
              |> ensure_def_class thy algbr funcgr strct class
              ||>> ensure_def_tyco thy algbr funcgr strct tyco
              ||>> fold_map (exprgen_tyvar_sort thy algbr funcgr strct) vs
              ||>> fold_map gen_suparity superclasses
              ||>> fold_map gen_membr (members ~~ memdefs)
              |-> (fn ((((class, tyco), arity), suparities), memdefs) =>
                     succeed (Classinst ((class, (tyco, arity)), (suparities, memdefs))))
            end
        | _ =>
            trns |> fail ("No class instance found for " ^ quote inst);
    val inst = CodegenNames.instance thy (cls, tyco);
  in
    trns
    |> tracing (fn _ => "generating instance " ^ quote cls ^ " / " ^ quote tyco)
    |> ensure_def (defgen_inst thy algbr funcgr strct) true
         ("generating instance " ^ quote cls ^ " / " ^ quote tyco) inst
    |> pair inst
  end
and ensure_def_const thy algbr funcgr strct (c, tys) trns =
  let
    fun defgen_datatypecons thy algbr funcgr strct co trns =
      case CodegenData.get_datatype_of_constr thy ((the o CodegenNames.const_rev thy) co)
       of SOME tyco =>
            trns
            |> tracing (fn _ => "trying defgen datatype constructor for " ^ quote co)
            |> ensure_def_tyco thy algbr funcgr strct tyco
            |-> (fn _ => succeed Bot)
        | _ =>
            trns
            |> fail ("Not a datatype constructor: "
                ^ (quote o CodegenConsts.string_of_const thy) (c, tys));
    fun defgen_clsmem thy algbr funcgr strct m trns =
      case AxClass.class_of_param thy ((fst o the o CodegenNames.const_rev thy) m)
       of SOME class =>
            trns
            |> tracing (fn _ => "trying defgen class operation for " ^ quote m)
            |> ensure_def_class thy algbr funcgr strct class
            |-> (fn _ => succeed Bot)
        | _ =>
            trns |> fail ("No class found for " ^ (quote o CodegenConsts.string_of_const thy) (c, tys))
    fun defgen_funs thy (algbr as (_, consts)) funcgr strct c' trns =
      case CodegenFuncgr.get_funcs funcgr ((the o CodegenNames.const_rev thy) c')
       of eq_thms as eq_thm :: _ =>
            let
              val msg = cat_lines ("generating code for theorems " :: map string_of_thm eq_thms);
              val ty = (Logic.unvarifyT o CodegenData.typ_func thy) eq_thm;
              val vs = (map dest_TFree o Consts.typargs consts) (c', ty);
              val dest_eqthm =
                apfst (snd o strip_comb) o Logic.dest_equals o Logic.unvarify o prop_of;
              fun exprgen_eq (args, rhs) trns =
                trns
                |> fold_map (exprgen_term thy algbr funcgr strct) args
                ||>> exprgen_term thy algbr funcgr strct rhs;
            in
              trns
              |> message msg (fn trns => trns
              |> fold_map (exprgen_eq o dest_eqthm) eq_thms
              ||>> fold_map (exprgen_tyvar_sort thy algbr funcgr strct) vs
              ||>> exprgen_type thy algbr funcgr strct ty
              |-> (fn ((eqs, vs), ty) => succeed (Fun (eqs, (vs, ty)))))
            end
        | [] =>
              trns
              |> fail ("No defining equations found for "
                   ^ (quote o CodegenConsts.string_of_const thy) (c, tys));
    fun get_defgen funcgr strct idf strict =
      if CodegenNames.has_nsp nsp_fun idf
      then defgen_funs thy algbr funcgr strct strict
      else if CodegenNames.has_nsp nsp_classop idf
      then defgen_clsmem thy algbr funcgr strct strict
      else if CodegenNames.has_nsp nsp_dtco idf
      then defgen_datatypecons thy algbr funcgr strct strict
      else error ("Illegal shallow name space for constant: " ^ quote idf);
    val idf = CodegenNames.const thy (c, tys);
    val strict = check_strict (CodegenSerializer.const_has_serialization thy) idf strct;
  in
    trns
    |> tracing (fn _ => "generating constant "
        ^ (quote o CodegenConsts.string_of_const thy) (c, tys))
    |> ensure_def (get_defgen funcgr strct idf) strict ("generating constant "
         ^ CodegenConsts.string_of_const thy (c, tys)) idf
    |> pair idf
  end
and exprgen_term thy algbr funcgr strct (Const (f, ty)) trns =
      trns
      |> appgen thy algbr funcgr strct ((f, ty), [])
      |-> (fn e => pair e)
  | exprgen_term thy algbr funcgr strct (Var _) trns =
      error "Var encountered in term during code generation"
  | exprgen_term thy algbr funcgr strct (Free (v, ty)) trns =
      trns
      |> exprgen_type thy algbr funcgr strct ty
      |-> (fn ty => pair (IVar v))
  | exprgen_term thy algbr funcgr strct (Abs (raw_v, ty, raw_t)) trns =
      let
        val (v, t) = Syntax.variant_abs (CodegenNames.purify_var raw_v, ty, raw_t);
      in
        trns
        |> exprgen_type thy algbr funcgr strct ty
        ||>> exprgen_term thy algbr funcgr strct t
        |-> (fn (ty, e) => pair ((v, ty) `|-> e))
      end
  | exprgen_term thy algbr funcgr strct (t as t1 $ t2) trns =
      let
        val (t', ts) = strip_comb t
      in case t'
       of Const (f, ty) =>
            trns
            |> appgen thy algbr funcgr strct ((f, ty), ts)
            |-> (fn e => pair e)
        | _ =>
            trns
            |> exprgen_term thy algbr funcgr strct t'
            ||>> fold_map (exprgen_term thy algbr funcgr strct) ts
            |-> (fn (e, es) => pair (e `$$ es))
      end
and appgen_default thy algbr funcgr strct ((c, ty), ts) trns =
  trns
  |> ensure_def_const thy algbr funcgr strct (CodegenConsts.norm_of_typ thy (c, ty))
  ||>> exprgen_type thy algbr funcgr strct ty
  ||>> exprgen_typinst_const thy algbr funcgr strct (c, ty)
  ||>> fold_map (exprgen_term thy algbr funcgr strct) ts
  |-> (fn (((c, ty), ls), es) =>
         pair (IConst (c, (ls, ty)) `$$ es))
and appgen thy algbr funcgr strct ((f, ty), ts) trns =
  case Symtab.lookup (CodegenPackageData.get thy) f
   of SOME (i, (ag, _)) =>
        if length ts < i then
          let
            val tys = Library.take (i - length ts, ((fst o strip_type) ty));
            val vs = Name.names (Name.declare f Name.context) "a" tys;
          in
            trns
            |> fold_map (exprgen_type thy algbr funcgr strct) tys
            ||>> ag thy algbr funcgr strct ((f, ty), ts @ map Free vs)
            |-> (fn (tys, e) => pair (map2 (fn (v, _) => pair v) vs tys `|--> e))
          end
        else if length ts > i then
          trns
          |> ag thy algbr funcgr strct ((f, ty), Library.take (i, ts))
          ||>> fold_map (exprgen_term thy algbr funcgr strct) (Library.drop (i, ts))
          |-> (fn (e, es) => pair (e `$$ es))
        else
          trns
          |> ag thy algbr funcgr strct ((f, ty), ts)
    | NONE =>
        trns
        |> appgen_default thy algbr funcgr strct ((f, ty), ts);


(* entrance points into extraction kernel *)

fun ensure_def_const' thy algbr funcgr strct c trns =
  ensure_def_const thy algbr funcgr strct c trns
  handle CONSTRAIN ((c, ty), ty_decl) => error (
    "Constant " ^ c ^ " with most general type\n"
    ^ Sign.string_of_typ thy ty
    ^ "\noccurs with type\n"
    ^ Sign.string_of_typ thy ty_decl);
fun exprgen_term' thy algbr funcgr strct t trns =
  exprgen_term thy algbr funcgr strct t trns
  handle CONSTRAIN ((c, ty), ty_decl) => error ("In term " ^ (quote o Sign.string_of_term thy) t
    ^ ",\nconstant " ^ c ^ " with most general type\n"
    ^ Sign.string_of_typ thy ty
    ^ "\noccurs with type\n"
    ^ Sign.string_of_typ thy ty_decl);


(* parametrized application generators, for instantiation in object logic *)
(* (axiomatic extensions of extraction kernel *)

fun appgen_numeral int_of_numeral thy algbr funcgr strct (app as (c, ts)) trns =
  case try (int_of_numeral thy) (list_comb (Const c, ts))
   of SOME i =>
        trns
        |> appgen_default thy algbr funcgr strct app
        |-> (fn e => pair (CodegenThingol.INum (i, e)))
    | NONE =>
        trns
        |> appgen_default thy algbr funcgr strct app;

fun appgen_char char_to_index thy algbr funcgr strct (app as ((_, ty), _)) trns =
  case (char_to_index o list_comb o apfst Const) app
   of SOME i =>
        trns
        |> exprgen_type thy algbr funcgr strct ty
        ||>> appgen_default thy algbr funcgr strct app
        |-> (fn (_, e0) => pair (IChar (chr i, e0)))
    | NONE =>
        trns
        |> appgen_default thy algbr funcgr strct app;

fun appgen_case dest_case_expr thy algbr funcgr strct (app as (c_ty, ts)) trns =
  let
    val SOME ([], ((st, sty), ds)) = dest_case_expr thy (list_comb (Const c_ty, ts));
    fun clausegen (dt, bt) trns =
      trns
      |> exprgen_term thy algbr funcgr strct dt
      ||>> exprgen_term thy algbr funcgr strct bt;
  in
    trns
    |> exprgen_term thy algbr funcgr strct st
    ||>> exprgen_type thy algbr funcgr strct sty
    ||>> fold_map clausegen ds
    ||>> appgen_default thy algbr funcgr strct app
    |-> (fn (((se, sty), ds), e0) => pair (ICase (((se, sty), ds), e0)))
  end;

fun appgen_let thy algbr funcgr strct (app as (_, [st, ct])) trns =
  trns
  |> exprgen_term thy algbr funcgr strct ct
  ||>> exprgen_term thy algbr funcgr strct st
  ||>> appgen_default thy algbr funcgr strct app
  |-> (fn (((v, ty) `|-> be, se), e0) =>
            pair (ICase (((se, ty), case be
              of ICase (((IVar w, _), ds), _) => if v = w then ds else [(IVar v, be)]
               | _ => [(IVar v, be)]
            ), e0))
        | (_, e0) => pair e0);

fun add_appconst (c, appgen) thy =
  let
    val i = (length o fst o strip_type o Sign.the_const_type thy) c
  in CodegenPackageData.map (Symtab.update (c, (i, (appgen, stamp ())))) thy end;



(** code generation interfaces **)

fun generate thy (cs, rhss) targets init gen it =
  let
    val funcgr = CodegenFuncgr.mk_funcgr thy cs rhss;
    val qnaming = NameSpace.qualified_names NameSpace.default_naming
    val algebr = ClassPackage.operational_algebra thy;
    val consttab = Consts.empty
      |> fold (fn (c, ty) => Consts.declare qnaming
           ((CodegenNames.const thy c, ty), true))
           (CodegenFuncgr.get_func_typs funcgr)
    val algbr = (algebr, consttab);
  in   
    Code.change_yield thy (start_transact init (gen thy algbr funcgr
        (true, targets) it))
    |> (fn (x, modl) => x)
  end;

fun codegen_term thy t =
  let
    fun const_typ (c, ty) =
      let
        val const = CodegenConsts.norm_of_typ thy (c, ty);
        val funcgr = CodegenFuncgr.mk_funcgr thy [const] [];
      in case CodegenFuncgr.get_funcs funcgr const
       of (thm :: _) => CodegenData.typ_func thy thm
        | [] => Sign.the_const_type thy c
      end;
    val ct = Thm.cterm_of thy t;
    val (thm, ct') = CodegenData.preprocess_cterm thy
      (const_typ) ct;
    val t' = Thm.term_of ct';
    val cs_rhss = CodegenConsts.consts_of thy t';
  in
    (thm, generate thy cs_rhss (SOME []) NONE exprgen_term' t')
  end;

fun const_of_idf thy =
  CodegenConsts.typ_of_inst thy o the o CodegenNames.const_rev thy;

fun get_root_module thy =
  Code.get thy;

fun eval_term thy (ref_spec, t) =
  let
    val _ = Term.fold_atyps (fn _ =>
      error ("Term" ^ Sign.string_of_term thy t ^ "is polymorhpic"))
      (Term.fastype_of t);
    val (_, t') = codegen_term thy t;
  in
    CodegenSerializer.eval_term thy (ref_spec, t') (Code.get thy)
  end;



(** toplevel interface and setup **)

local

structure P = OuterParse
and K = OuterKeyword

fun code raw_cs seris thy =
  let
    val cs = map (CodegenConsts.read_const thy) raw_cs;
    val targets = case map fst seris
     of [] => NONE
      | xs => SOME xs;
    val seris' = map_filter (fn (target, SOME seri) => SOME (target, seri) | _ => NONE) seris;
    fun generate' thy = case cs
     of [] => []
      | _ =>
          generate thy (cs, []) targets NONE (fold_map oooo ensure_def_const') cs;
    fun serialize' [] code (_, seri) =
          seri thy NONE code 
      | serialize' cs code (_, seri) =
          seri thy (SOME cs) code;
    val cs = generate' thy;
    val code = Code.get thy;
  in
    (map (serialize' cs code) seris'; ())
  end;

fun reader_tyco thy rhss target dep =
  generate thy rhss (SOME [target]) (SOME dep) (fold_map oooo exprgen_type);

fun reader_const thy rhss target dep =
  generate thy rhss (SOME [target]) (SOME dep) (fold_map oooo exprgen_term');

val parse_target = P.name >> tap CodegenSerializer.check_serializer;

fun zip_list (x::xs) f g =
  f x #-> (fn y => fold_map (fn x => g |-- f x >> pair x) xs
    #-> (fn xys => pair ((x, y) :: xys)));

fun parse_multi_syntax parse_thing parse_syntax =
  P.and_list1 parse_thing
  #-> (fn things => Scan.repeat1 (P.$$$ "(" |-- parse_target :--
      (fn target => zip_list things (parse_syntax target)
        (P.$$$ "and")) --| P.$$$ ")"))


in

val (codeK,
     syntax_classK, syntax_instK, syntax_tycoK, syntax_constK) =
  ("code_gen",
   "code_class", "code_instance", "code_type", "code_const");

val codeP =
  OuterSyntax.improper_command codeK "generate and serialize executable code for constants" K.diag (
    Scan.repeat P.term
    -- Scan.repeat (P.$$$ "(" |--
        P.name :-- (fn target => (CodegenSerializer.parse_serializer target >> SOME) || pair NONE)
        --| P.$$$ ")")
    >> (fn (raw_cs, seris) => Toplevel.keep (code raw_cs seris o Toplevel.theory_of))
  );

val syntax_classP =
  OuterSyntax.command syntax_classK "define code syntax for class" K.thy_decl (
    parse_multi_syntax P.xname
      (fn _ => fn _ => P.string -- Scan.optional (P.$$$ "where" |-- Scan.repeat1
        (P.term --| (P.$$$ "\\<equiv>" || P.$$$ "==") -- P.string)) [])
    >> (Toplevel.theory oo fold) (fn (target, syns) =>
          fold (fn (raw_class, syn) => CodegenSerializer.add_syntax_class target raw_class syn) syns)
  );

val syntax_instP =
  OuterSyntax.command syntax_instK "define code syntax for instance" K.thy_decl (
    parse_multi_syntax (P.xname --| P.$$$ "::" -- P.xname)
      (fn _ => fn _ => P.name #->
        (fn "-" => Scan.succeed () | _ => Scan.fail_with (fn _ => "\"-\" expected") ()))
    >> (Toplevel.theory oo fold) (fn (target, syns) =>
          fold (fn (raw_inst, ()) => CodegenSerializer.add_syntax_inst target raw_inst) syns)
  );

val syntax_tycoP =
  OuterSyntax.command syntax_tycoK "define code syntax for type constructor" K.thy_decl (
    Scan.repeat1 (
      parse_multi_syntax P.xname (CodegenSerializer.parse_syntax_tyco reader_tyco)
    )
    >> (Toplevel.theory o (fold o fold) (fold snd o snd))
  );

val syntax_constP =
  OuterSyntax.command syntax_constK "define code syntax for constant" K.thy_decl (
    Scan.repeat1 (
      parse_multi_syntax P.term (CodegenSerializer.parse_syntax_const reader_const)
    )
    >> (Toplevel.theory o (fold o fold) (fold snd o snd))
  );

val _ = OuterSyntax.add_parsers [codeP,
  syntax_classP, syntax_instP, syntax_tycoP, syntax_constP];

end; (* local *)

end; (* struct *)

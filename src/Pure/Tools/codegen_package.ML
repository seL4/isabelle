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
  val is_dtcon: string -> bool;
  val consts_of_idfs: theory -> string list -> (string * typ) list;
  val idfs_of_consts: theory -> (string * typ) list -> string list;
  val get_root_module: theory -> CodegenThingol.module;
  val get_ml_fun_datatype: theory -> (string -> string)
    -> ((string * ((iterm list * iterm) list * CodegenThingol.typscheme)) list -> Pretty.T)
        * ((string * ((vname * sort) list * (string * itype list) list)) list -> Pretty.T);

  val add_pretty_list: string -> string -> string -> (Pretty.T list -> Pretty.T)
   -> ((string -> string) * (string -> string)) option -> int * string
   -> theory -> theory;
  val add_pretty_ml_string: string -> string -> string -> string
   -> (string -> string) -> (string -> string) -> string -> theory -> theory;

  type appgen;
  val add_appconst: string * appgen -> theory -> theory;
  val appgen_default: appgen;
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

(* shallow name spaces *)

val nsp_module = ""; (*a dummy by convention*)
val nsp_class = "class";
val nsp_tyco = "tyco";
val nsp_const = "const";
val nsp_dtcon = "dtcon";
val nsp_mem = "mem";
val nsp_inst = "inst";
val nsp_eval = "EVAL"; (*only for evaluation*)

fun add_nsp shallow name =
  name
  |> NameSpace.unpack
  |> split_last
  |> apsnd (single #> cons shallow)
  |> (op @)
  |> NameSpace.pack;

fun dest_nsp nsp idf =
  let
    val idf' = NameSpace.unpack idf;
    val (idf'', idf_base) = split_last idf';
    val (modl, shallow) = split_last idf'';
  in
    if nsp = shallow
   then (SOME o NameSpace.pack) (modl @ [idf_base])
    else NONE
  end;

fun if_nsp nsp f idf =
  Option.map f (dest_nsp nsp idf);

val serializers = ref (
  Symtab.empty
  |> Symtab.update (
       #SML CodegenSerializer.serializers
       |> apsnd (fn seri => seri
            nsp_dtcon
            [[nsp_module], [nsp_class, nsp_tyco],
              [nsp_const, nsp_dtcon, nsp_class, nsp_mem, nsp_inst]]
          )
     )
  |> Symtab.update (
       #Haskell CodegenSerializer.serializers
       |> apsnd (fn seri => seri
            (nsp_dtcon, [nsp_module, nsp_class, nsp_tyco, nsp_dtcon])
            [[nsp_module], [nsp_class], [nsp_tyco], [nsp_const,  nsp_mem],
              [nsp_dtcon], [nsp_inst]]
          )
     )
);


(* theory data  *)

type appgen = theory -> ((sort -> sort) * Sorts.algebra) * Consts.T
  -> CodegenFuncgr.T
  -> bool * string list option -> (string * typ) * term list -> transact -> iterm * transact;

type appgens = (int * (appgen * stamp)) Symtab.table;

fun merge_appgens (x : appgens * appgens) =
  Symtab.merge (fn ((bounds1, (_, stamp1)), (bounds2, (_, stamp2))) =>
    bounds1 = bounds2 andalso stamp1 = stamp2) x;

type target_data = {
  syntax_class: ((string * (string -> string option)) * stamp) Symtab.table,
  syntax_inst: unit Symtab.table,
  syntax_tyco: (itype CodegenSerializer.pretty_syntax * stamp) Symtab.table,
  syntax_const: (iterm CodegenSerializer.pretty_syntax * stamp) Symtab.table
};

fun merge_target_data
  ({ syntax_class = syntax_class1, syntax_inst = syntax_inst1,
       syntax_tyco = syntax_tyco1, syntax_const = syntax_const1 },
   { syntax_class = syntax_class2, syntax_inst = syntax_inst2,
       syntax_tyco = syntax_tyco2, syntax_const = syntax_const2 }) =
  { syntax_class = Symtab.merge (eq_snd (op =)) (syntax_class1, syntax_class2),
    syntax_inst = Symtab.merge (op =) (syntax_inst1, syntax_inst2),
    syntax_tyco = Symtab.merge (eq_snd (op =)) (syntax_tyco1, syntax_tyco2),
    syntax_const = Symtab.merge (eq_snd (op =)) (syntax_const1, syntax_const2) } : target_data;

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
  type T = {
    appgens: appgens,
    target_data: target_data Symtab.table
  };
  val empty = {
    appgens = Symtab.empty,
    target_data =
      Symtab.empty
      |> Symtab.fold (fn (target, _) =>
           Symtab.update (target,
             { syntax_class = Symtab.empty, syntax_inst = Symtab.empty,
               syntax_tyco = Symtab.empty, syntax_const = Symtab.empty })
         ) (! serializers)
  } : T;
  val copy = I;
  val extend = I;
  fun merge _ (
    { appgens = appgens1, target_data = target_data1 },
    { appgens = appgens2, target_data = target_data2 }
  ) = {
    appgens = merge_appgens (appgens1, appgens2),
    target_data = Symtab.join (K merge_target_data) (target_data1, target_data2)
  };
  fun print _ _ = ();
end);

val _ = Context.add_setup (Code.init #> CodegenPackageData.init);

fun map_codegen_data f thy =
  case CodegenPackageData.get thy
   of { appgens, target_data } =>
      let val (appgens, target_data) =
        f (appgens, target_data)
      in CodegenPackageData.put { appgens = appgens,
           target_data = target_data } thy end;

fun check_serializer target =
  case Symtab.lookup (!serializers) target
   of SOME seri => ()
    | NONE => error ("Unknown code target language: " ^ quote target);

fun get_serializer target =
  case Symtab.lookup (!serializers) target
   of SOME seri => seri
    | NONE => Scan.fail_with (fn _ => "Unknown code target language: " ^ quote target) ();

fun serialize thy target seri cs =
  let
    val data = CodegenPackageData.get thy;
    val code = Code.get thy;
    val target_data =
      (the oo Symtab.lookup) (#target_data data) target;
    val syntax_class = #syntax_class target_data;
    val syntax_inst = #syntax_inst target_data;
    val syntax_tyco = #syntax_tyco target_data;
    val syntax_const = #syntax_const target_data;
    fun fun_of syntax = (Option.map fst oo Symtab.lookup) syntax;
  in
    seri (fun_of syntax_class, fun_of syntax_tyco, fun_of syntax_const)
      (Symtab.keys syntax_class @ Symtab.keys syntax_inst
         @ Symtab.keys syntax_tyco @ Symtab.keys syntax_const, cs) code : unit
  end;

fun map_target_data target f =
  let
    val _ = check_serializer target;
  in
    map_codegen_data (fn (appgens, target_data) => 
      (appgens, Symtab.map_entry target (fn { syntax_class, syntax_inst, syntax_tyco, syntax_const } =>
          let
            val (syntax_class, syntax_inst, syntax_tyco, syntax_const) =
              f (syntax_class, syntax_inst, syntax_tyco, syntax_const)
          in {
            syntax_class = syntax_class,
            syntax_inst = syntax_inst,
            syntax_tyco = syntax_tyco,
            syntax_const = syntax_const } : target_data
          end
      ) target_data)
    )
  end;

fun print_code thy =
  let
    val code = Code.get thy;
  in (Pretty.writeln o Pretty.chunks) [pretty_module code, pretty_deps code] end;

fun purge_code thy = Code.change thy (K CodegenThingol.empty_module);

(* name handling *)

fun idf_of_class thy class =
  CodegenNames.class thy class
  |> add_nsp nsp_class;

fun class_of_idf thy = if_nsp nsp_class (CodegenNames.class_rev thy);

fun idf_of_tyco thy tyco =
  CodegenNames.tyco thy tyco
  |> add_nsp nsp_tyco;

fun tyco_of_idf thy = if_nsp nsp_tyco (CodegenNames.tyco_rev thy);

fun idf_of_inst thy inst =
  CodegenNames.instance thy inst
  |> add_nsp nsp_inst;

fun inst_of_idf thy = if_nsp nsp_inst (CodegenNames.instance_rev thy);

fun idf_of_const thy c_tys =
  if (is_some o CodegenData.get_datatype_of_constr thy) c_tys then
    CodegenNames.const thy c_tys
    |> add_nsp nsp_dtcon
  else if (is_some o CodegenConsts.class_of_classop thy) c_tys then
    CodegenNames.const thy c_tys
    |> add_nsp nsp_mem
  else
    CodegenNames.const thy c_tys
    |> add_nsp nsp_const;

fun idf_of_classop thy c_ty =
  CodegenNames.const thy c_ty
  |> add_nsp nsp_mem;

fun const_of_idf thy idf =
  case dest_nsp nsp_const idf
   of SOME c => CodegenNames.const_rev thy c |> SOME
    | _ => (case dest_nsp nsp_dtcon idf
   of SOME c => CodegenNames.const_rev thy c |> SOME
    | _ => (case dest_nsp nsp_mem idf
   of SOME c => CodegenNames.const_rev thy c |> SOME
    | _ => NONE));



(** code extraction **)

(* extraction kernel *)

fun check_strict thy f x (false, _) =
      false
  | check_strict thy f x (_, SOME targets) =
      exists (
        is_none o (fn tab => Symtab.lookup tab x) o f o the
          o (Symtab.lookup ((#target_data o CodegenPackageData.get) thy))
      ) targets
  | check_strict thy f x (true, _) =
      true;

fun no_strict (_, targets) = (false, targets);

fun ensure_def_class thy algbr funcgr strct cls trns =
  let
    fun defgen_class thy (algbr as ((proj_sort, _), _)) funcgr strct cls trns =
      case class_of_idf thy cls
       of SOME cls =>
            let
              val (v, cs) = (ClassPackage.the_consts_sign thy) cls;
              val superclasses = (proj_sort o Sign.super_classes thy) cls
              val idfs = map (idf_of_const thy o CodegenConsts.norm_of_typ thy) cs;
            in
              trns
              |> debug_msg (fn _ => "trying defgen class declaration for " ^ quote cls)
              |> fold_map (ensure_def_class thy algbr funcgr strct) superclasses
              ||>> (fold_map (exprgen_type thy algbr funcgr strct) o map snd) cs
              |-> (fn (supcls, memtypes) => succeed
                (Class (supcls, (unprefix "'" v, idfs ~~ memtypes))))
            end
        | _ =>
            trns
            |> fail ("No class definition found for " ^ quote cls);
    val cls' = idf_of_class thy cls;
  in
    trns
    |> debug_msg (fn _ => "generating class " ^ quote cls)
    |> ensure_def (defgen_class thy algbr funcgr strct) true ("generating class " ^ quote cls) cls'
    |> pair cls'
  end
and ensure_def_tyco thy algbr funcgr strct tyco trns =
  let
    val tyco' = idf_of_tyco thy tyco;
    val strict = check_strict thy #syntax_tyco tyco' strct;
    fun defgen_datatype thy algbr funcgr strct dtco trns =
      case tyco_of_idf thy dtco
       of SOME dtco =>
         (case CodegenData.get_datatype thy dtco
             of SOME (vs, cos) =>
                  trns
                  |> debug_msg (fn _ => "trying defgen datatype for " ^ quote dtco)
                  |> fold_map (exprgen_tyvar_sort thy algbr funcgr strct) vs
                  ||>> fold_map (fn (c, tys) =>
                    fold_map (exprgen_type thy algbr funcgr strct) tys
                    #-> (fn tys' =>
                      pair ((idf_of_const thy o CodegenConsts.norm_of_typ thy)
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
    |> debug_msg (fn _ => "generating type constructor " ^ quote tyco)
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

exception CONSTRAIN of ((string * typ) * typ) * term option;

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
    val idf = idf_of_const thy c';
    val ty_decl = Consts.declaration consts idf;
    val insts = (op ~~ o apsnd (map (snd o dest_TVar)) oo pairself)
      (curry (Consts.typargs consts) idf) (ty_ctxt, ty_decl);
    val _ = if exists not (map (Sign.of_sort thy) insts)
      then raise CONSTRAIN (((c, ty_decl), ty_ctxt), NONE) else ();
  in
    trns
    |> fold_map (exprgen_typinst thy algbr funcgr strct) insts
  end
and ensure_def_inst thy algbr funcgr strct (cls, tyco) trns =
  let
    fun defgen_inst thy (algbr as ((proj_sort, _), _)) funcgr strct inst trns =
      case inst_of_idf thy inst
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
              |> debug_msg (fn _ => "trying defgen class instance for (" ^ quote cls
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
    val inst = idf_of_inst thy (cls, tyco);
  in
    trns
    |> debug_msg (fn _ => "generating instance " ^ quote cls ^ " / " ^ quote tyco)
    |> ensure_def (defgen_inst thy algbr funcgr strct) true
         ("generating instance " ^ quote cls ^ " / " ^ quote tyco) inst
    |> pair inst
  end
and ensure_def_const thy algbr funcgr strct (c, tys) trns =
  let
    fun defgen_datatypecons thy algbr funcgr strct co trns =
      case CodegenData.get_datatype_of_constr thy ((the o const_of_idf thy) co)
       of SOME tyco =>
            trns
            |> debug_msg (fn _ => "trying defgen datatype constructor for " ^ quote co)
            |> ensure_def_tyco thy algbr funcgr strct tyco
            |-> (fn _ => succeed Bot)
        | _ =>
            trns
            |> fail ("Not a datatype constructor: "
                ^ (quote o CodegenConsts.string_of_const thy) (c, tys));
    fun defgen_clsmem thy algbr funcgr strct m trns =
      case CodegenConsts.class_of_classop thy ((the o const_of_idf thy) m)
       of SOME class =>
            trns
            |> debug_msg (fn _ => "trying defgen class member for " ^ quote m)
            |> ensure_def_class thy algbr funcgr strct class
            |-> (fn _ => succeed Bot)
        | _ =>
            trns |> fail ("No class operation found for " ^ (quote o CodegenConsts.string_of_const thy) (c, tys))
    fun defgen_funs thy (algbr as (_, consts)) funcgr strct c' trns =
      case CodegenFuncgr.get_funcs funcgr ((the o const_of_idf thy) c')
       of eq_thms as eq_thm :: _ =>
            let
              val msg = cat_lines ("generating code for theorems " :: map string_of_thm eq_thms);
              val ty = (Logic.unvarifyT o CodegenData.typ_func thy) eq_thm;
              val vs = (map dest_TFree o Consts.typargs consts) (c', ty);
              fun dest_eqthm eq_thm =
                let
                  val ((t, args), rhs) =
                    (apfst strip_comb o Logic.dest_equals o Logic.unvarify o prop_of) eq_thm;
                in case t
                 of Const (c', _) => if c' = c then (args, rhs)
                     else error ("Illegal function equation for " ^ quote c
                       ^ ", actually defining " ^ quote c')
                  | _ => error ("Illegal function equation for " ^ quote c)
                end;
              fun exprgen_eq (args, rhs) trns =
                trns
                |> fold_map (exprgen_term thy algbr funcgr strct) args
                ||>> exprgen_term thy algbr funcgr strct rhs;
              fun checkvars (args, rhs) =
                if CodegenThingol.vars_distinct args then (args, rhs)
                else error ("Repeated variables on left hand side of function")
            in
              trns
              |> message msg (fn trns => trns
              |> fold_map (exprgen_eq o dest_eqthm) eq_thms
              |-> (fn eqs => pair (map checkvars eqs))
              ||>> fold_map (exprgen_tyvar_sort thy algbr funcgr strct) vs
              ||>> exprgen_type thy algbr funcgr strct ty
              |-> (fn ((eqs, vs), ty) => succeed (Fun (eqs, (vs, ty)))))
            end
        | [] =>
              trns
              |> fail ("No defining equations found for "
                   ^ (quote o CodegenConsts.string_of_const thy) (c, tys));
    fun get_defgen funcgr strct idf strict =
      if (is_some oo dest_nsp) nsp_const idf
      then defgen_funs thy algbr funcgr strct strict
      else if (is_some oo dest_nsp) nsp_mem idf
      then defgen_clsmem thy algbr funcgr strct strict
      else if (is_some oo dest_nsp) nsp_dtcon idf
      then defgen_datatypecons thy algbr funcgr strct strict
      else error ("Illegal shallow name space for constant: " ^ quote idf);
    val idf = idf_of_const thy (c, tys);
    val strict = check_strict thy #syntax_const idf strct;
  in
    trns
    |> debug_msg (fn _ => "generating constant "
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
  case Symtab.lookup ((#appgens o CodegenPackageData.get) thy) f
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


(* entry points into extraction kernel *)

fun ensure_def_const' thy algbr funcgr strct c trns =
  ensure_def_const thy algbr funcgr strct c trns
  handle CONSTRAIN (((c, ty), ty_decl), NONE) => error (
    "Constant " ^ c ^ " with most general type\n"
    ^ Sign.string_of_typ thy ty
    ^ "\noccurs with type\n"
    ^ Sign.string_of_typ thy ty_decl)
  handle CONSTRAIN (((c, ty), ty_decl), SOME t) => error ("In term " ^ (quote o Sign.string_of_term thy) t
    ^ ",\nconstant " ^ c ^ " with most general type\n"
    ^ Sign.string_of_typ thy ty
    ^ "\noccurs with type\n"
    ^ Sign.string_of_typ thy ty_decl);

fun exprgen_term' thy algbr funcgr strct t trns =
  exprgen_term thy algbr funcgr strct t trns
  handle CONSTRAIN (((c, ty), ty_decl), _) => error ("In term " ^ (quote o Sign.string_of_term thy) t
    ^ ",\nconstant " ^ c ^ " with most general type\n"
    ^ Sign.string_of_typ thy ty
    ^ "\noccurs with type\n"
    ^ Sign.string_of_typ thy ty_decl);


(* parametrized application generators, for instantiation in object logic *)
(* (axiomatic extensions of extraction kernel *)

fun appgen_numeral int_of_numeral thy algbr funcgr strct (app as (c, ts)) trns =
  case try (int_of_numeral thy) (list_comb (Const c, ts))
   of SOME i => (*if i < 0 then (*preprocessor eliminates negative numerals*)
        trns
        |> appgen_default thy algbr funcgr (no_strict strct) app
      else*)
        trns
        |> appgen_default thy algbr funcgr (no_strict strct) app
        |-> (fn e => pair (CodegenThingol.INum (i, e)))
    | NONE =>
        trns
        |> appgen_default thy algbr funcgr (no_strict strct) app;

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
  in map_codegen_data
    (fn (appgens, target_data) =>
       (appgens |> Symtab.update (c, (i, (appgen, stamp ()))),
        target_data)) thy
  end;



(** code generation interfaces **)

fun generate thy (cs, rhss) targets init gen it =
  let
    val funcgr = CodegenFuncgr.mk_funcgr thy cs rhss;
    val qnaming = NameSpace.qualified_names NameSpace.default_naming
    val algebr = ClassPackage.operational_algebra thy;
    val consttab = Consts.empty
      |> fold (fn (c, ty) => Consts.declare qnaming
           ((idf_of_const thy c, ty), true))
           (CodegenFuncgr.get_func_typs funcgr)
    val algbr = (algebr, consttab);
  in   
    Code.change_yield thy (start_transact init (gen thy algbr funcgr
        (true, targets) it))
    |> (fn (x, modl) => x)
  end;

fun consts_of thy t =
  fold_aterms (fn Const c => cons (CodegenConsts.norm_of_typ thy c, c) | _ => I) t []
  |> split_list;

fun codegen_term thy t =
  let
    val ct = Thm.cterm_of thy t;
    val thm = CodegenData.preprocess_cterm thy ct;
    val t' = (snd o Logic.dest_equals o Drule.plain_prop_of) thm;
    val cs_rhss = consts_of thy t';
  in
    (thm, generate thy cs_rhss (SOME []) NONE exprgen_term' t')
  end;

val is_dtcon = has_nsp nsp_dtcon;

fun consts_of_idfs thy =
  map (CodegenConsts.typ_of_inst thy o the o const_of_idf thy);

fun idfs_of_consts thy cs =
  let
    val cs' = map (CodegenConsts.norm_of_typ thy) cs;
  in map (idf_of_const thy) cs' end;

fun get_root_module thy =
  Code.get thy;

fun eval_term thy (ref_spec, t) =
  let
    val _ = Term.fold_atyps (fn _ =>
      error ("Term" ^ Sign.string_of_term thy t ^ "is polymorhpic"))
      (Term.fastype_of t);
    fun preprocess_term t =
      let
        val x = Free (Name.variant (add_term_names (t, [])) "x", fastype_of t);
        (* fake definition *)
        val eq = setmp quick_and_dirty true (SkipProof.make_thm thy)
          (Logic.mk_equals (x, t));
        fun err () = error "preprocess_term: bad preprocessor"
      in case map prop_of (CodegenFuncgr.preprocess thy [eq])
       of [Const ("==", _) $ x' $ t'] => if x = x' then t' else err ()
        | _ => err ()
      end;
    val target_data =
      ((fn data => (the o Symtab.lookup data) "SML") o #target_data o CodegenPackageData.get) thy;
    val eval = CodegenSerializer.eval_term nsp_eval nsp_dtcon [[nsp_module], [nsp_class, nsp_tyco], [nsp_const, nsp_dtcon, nsp_class, nsp_mem, nsp_inst], [nsp_eval]]
      ((Option.map fst oo Symtab.lookup) (#syntax_tyco target_data),
       (Option.map fst oo Symtab.lookup) (#syntax_const target_data))
      (Symtab.keys (#syntax_tyco target_data) @ Symtab.keys (#syntax_const target_data));
    val (_, t') = codegen_term thy (preprocess_term t);
    val modl = Code.get thy;
  in
    eval (ref_spec, t') modl
  end;

fun get_ml_fun_datatype thy resolv =
  let
    val target_data =
      ((fn data => (the o Symtab.lookup data) "SML") o #target_data o CodegenPackageData.get) thy;
  in
    CodegenSerializer.ml_fun_datatype nsp_dtcon
      ((Option.map fst oo Symtab.lookup o #syntax_tyco) target_data,
      (Option.map fst oo Symtab.lookup o #syntax_const) target_data)
      resolv
  end;



(** target syntax **)

local

fun gen_add_syntax_class prep_class prep_const target raw_class (syntax, raw_ops) thy =
  let
    val class = (idf_of_class thy o prep_class thy) raw_class;
    val ops = (map o apfst) (idf_of_classop thy o prep_const thy) raw_ops;
    val syntax_ops = AList.lookup (op =) ops;
  in
    thy
    |> map_target_data target (fn (syntax_class, syntax_inst, syntax_tyco, syntax_const) =>
        (syntax_class |> Symtab.update (class,
          ((syntax, syntax_ops), stamp ())),
            syntax_inst, syntax_tyco, syntax_const))
  end;

fun gen_add_syntax_inst prep_class prep_tyco target (raw_tyco, raw_class) thy =
  let
    val inst = idf_of_inst thy (prep_class thy raw_class, prep_tyco thy raw_tyco);
  in
    thy
    |> map_target_data target (fn (syntax_class, syntax_inst, syntax_tyco, syntax_const) =>
        (syntax_class, syntax_inst |> Symtab.update (inst, ()),
          syntax_tyco, syntax_const))
  end;

fun gen_add_syntax_tyco prep_tyco raw_tyco target syntax thy =
  let
    val tyco = (idf_of_tyco thy o prep_tyco thy) raw_tyco;
  in
    thy
    |> map_target_data target (fn (syntax_class, syntax_inst, syntax_tyco, syntax_const) =>
         (syntax_class, syntax_inst, syntax_tyco
            |> Symtab.update (tyco, (syntax, stamp ())), syntax_const))
  end;

fun gen_add_syntax_const prep_const raw_c target syntax thy =
  let
    val c' = prep_const thy raw_c;
    val c'' = idf_of_const thy c';
  in
    thy
    |> map_target_data target (fn (syntax_class, syntax_inst, syntax_tyco, syntax_const) =>
         (syntax_class, syntax_inst, syntax_tyco, syntax_const
            |> Symtab.update (c'', (syntax, stamp ()))))
  end;

fun read_type thy raw_tyco =
  let
    val tyco = Sign.intern_type thy raw_tyco;
    val _ = if Sign.declared_tyname thy tyco then ()
      else error ("No such type constructor: " ^ quote raw_tyco);
  in tyco end;

fun idfs_of_const_names thy cs =
  let
    val cs' = AList.make (fn c => Sign.the_const_type thy c) cs;
    val cs'' = map (CodegenConsts.norm_of_typ thy) cs';
  in AList.make (idf_of_const thy) cs'' end;

fun read_quote reader consts_of target get_init gen raw_it thy =
  let
    val it = reader thy raw_it;
    val cs = consts_of thy it;
  in
    generate thy cs (SOME [target]) ((SOME o get_init) thy) gen [it]
    |> (fn [it'] => (it', thy))
  end;

fun parse_quote num_of reader consts_of target get_init gen adder =
  CodegenSerializer.parse_syntax num_of
    (read_quote reader consts_of target get_init gen)
  #-> (fn modifier => pair (modifier #-> adder target));

in

val add_syntax_class = gen_add_syntax_class ClassPackage.read_class CodegenConsts.read_const;
val add_syntax_inst = gen_add_syntax_inst ClassPackage.read_class read_type;

fun parse_syntax_tyco target raw_tyco  =
  let
    fun intern thy = read_type thy raw_tyco;
    fun num_of thy = Sign.arity_number thy (intern thy);
    fun idf_of thy = idf_of_tyco thy (intern thy);
    fun read_typ thy =
      Sign.read_typ (thy, K NONE);
  in
    parse_quote num_of read_typ ((K o K) ([], [])) target idf_of (fold_map oooo exprgen_type)
      (gen_add_syntax_tyco read_type raw_tyco)
  end;

fun parse_syntax_const target raw_const =
  let
    fun intern thy = CodegenConsts.read_const thy raw_const;
    fun num_of thy = (length o fst o strip_type o Sign.the_const_type thy o fst o intern) thy;
    fun idf_of thy = (idf_of_const thy o intern) thy;
  in
    parse_quote num_of Sign.read_term consts_of target idf_of (fold_map oooo exprgen_term')
      (gen_add_syntax_const CodegenConsts.read_const raw_const)
  end;

fun add_pretty_list target nill cons mk_list mk_char_string target_cons thy =
  let
    val [(_, nil''), (cons', cons'')] = idfs_of_const_names thy [nill, cons];
    val pr = CodegenSerializer.pretty_list nil'' cons'' mk_list mk_char_string target_cons;
  in
    thy
    |> gen_add_syntax_const (K I) cons' target pr
  end;

fun add_pretty_ml_string target nill cons str mk_char mk_string target_implode thy =
  let
    val [(_, nil''), (_, cons''), (str', _)] = idfs_of_const_names thy [nill, cons, str];
    val pr = CodegenSerializer.pretty_ml_string nil'' cons'' mk_char mk_string target_implode;
  in
    thy
    |> gen_add_syntax_const (K I) str' target pr
  end;

end; (*local*)



(** toplevel interface and setup **)

local

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
    fun serialize' thy [] (target, seri) =
          serialize thy target seri NONE : unit
      | serialize' thy cs (target, seri) =
          serialize thy target seri (SOME cs) : unit;
    val cs = generate' thy;
  in
    (map (serialize' thy cs) seris'; ())
  end;

structure P = OuterParse
and K = OuterKeyword

val parse_target = P.name >> tap check_serializer;

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
  OuterSyntax.command codeK "generate and serialize executable code for constants" K.diag (
    Scan.repeat P.term
    -- Scan.repeat (P.$$$ "(" |--
        P.name :-- (fn target => (get_serializer target >> SOME) || pair NONE)
        --| P.$$$ ")")
    >> (fn (raw_cs, seris) => Toplevel.keep (code raw_cs seris o Toplevel.theory_of))
  );

val syntax_classP =
  OuterSyntax.command syntax_classK "define code syntax for class" K.thy_decl (
    parse_multi_syntax P.xname
      (fn _ => fn _ => P.string -- Scan.optional (P.$$$ "where" |-- Scan.repeat1
        (P.term --| (P.$$$ "\\<equiv>" || P.$$$ "==") -- P.string)) [])
    >> (Toplevel.theory oo fold) (fn (target, syns) =>
          fold (fn (raw_class, syn) => add_syntax_class target raw_class syn) syns)
  );

val syntax_instP =
  OuterSyntax.command syntax_instK "define code syntax for instance" K.thy_decl (
    parse_multi_syntax (P.xname --| P.$$$ "::" -- P.xname)
      (fn _ => fn _ => P.name #->
        (fn "-" => Scan.succeed () | _ => Scan.fail_with (fn _ => "\"-\" expected") ()))
    >> (Toplevel.theory oo fold) (fn (target, syns) =>
          fold (fn (raw_inst, ()) => add_syntax_inst target raw_inst) syns)
  );

val syntax_tycoP =
  OuterSyntax.command syntax_tycoK "define code syntax for type constructor" K.thy_decl (
    Scan.repeat1 (
      parse_multi_syntax P.xname parse_syntax_tyco
    )
    >> (Toplevel.theory o (fold o fold) (fold snd o snd))
  );

val syntax_constP =
  OuterSyntax.command syntax_constK "define code syntax for constant" K.thy_decl (
    Scan.repeat1 (
      parse_multi_syntax P.term parse_syntax_const
    )
    >> (Toplevel.theory o (fold o fold) (fold snd o snd))
  );

val _ = OuterSyntax.add_parsers [codeP,
  syntax_classP, syntax_instP, syntax_tycoP, syntax_constP];

end; (* local *)

end; (* struct *)

(*  Title:      Pure/Tools/codegen_package.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Code generator from Isabelle theories to
intermediate language ("Thin-gol").
*)

signature CODEGEN_PACKAGE =
sig
  val codegen_term: term -> theory -> CodegenThingol.iterm * theory;
  val eval_term: (string (*reference name!*) * 'a ref) * term
    -> theory -> 'a * theory;
  val is_dtcon: string -> bool;
  val consts_of_idfs: theory -> string list -> (string * typ) list;
  val idfs_of_consts: theory -> (string * typ) list -> string list;
  val get_root_module: theory -> CodegenThingol.module * theory;
  val get_ml_fun_datatype: theory -> (string -> string)
    -> ((string * CodegenThingol.funn) list -> Pretty.T)
        * ((string * CodegenThingol.datatyp) list -> Pretty.T);

  val add_pretty_list: string -> string -> string * (int * string)
    -> theory -> theory;
  val purge_code: theory -> theory;

  type appgen;
  val add_appconst: xstring * appgen -> theory -> theory;
  val add_appconst_i: string * appgen -> theory -> theory;
  val appgen_default: appgen;
  val appgen_rep_bin: (theory -> term -> IntInf.int) -> appgen;
  val appgen_char: (term -> int option) -> appgen;
  val appgen_case: (theory -> term
    -> ((string * typ) list * ((term * typ) * (term * term) list)) option)
    -> appgen;
  val appgen_let: appgen;
  val appgen_wfrec: appgen;

  val print_code: theory -> unit;

  structure CodegenData: THEORY_DATA;
  type auxtab;
  val mk_tabs: theory -> string list option -> (string * typ) list -> auxtab;
end;

structure CodegenPackage : CODEGEN_PACKAGE =
struct

open CodegenThingol;

(* shallow name spaces *)

val nsp_module = ""; (*a dummy by convention*)
val nsp_class = "class";
val nsp_tyco = "tyco";
val nsp_const = "const";
val nsp_dtcon = "dtcon";
val nsp_mem = "mem";
val nsp_inst = "inst";
val nsp_instmem = "instmem";
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


(* code generator basics *)

type auxtab = (bool * string list option) * CodegenTheorems.thmtab;
type appgen = theory -> auxtab
  -> (string * typ) * term list -> transact -> iterm * transact;

val serializers = ref (
  Symtab.empty
  |> Symtab.update (
       #ml CodegenSerializer.serializers
       |> apsnd (fn seri => seri
            nsp_dtcon
            [[nsp_module], [nsp_class, nsp_tyco],
              [nsp_const, nsp_dtcon, nsp_class, nsp_mem, nsp_inst, nsp_instmem]]
          )
     )
  |> Symtab.update (
       #haskell CodegenSerializer.serializers
       |> apsnd (fn seri => seri
            (nsp_dtcon, [nsp_module, nsp_class, nsp_tyco, nsp_dtcon])
            [[nsp_module], [nsp_class], [nsp_tyco], [nsp_const,  nsp_mem],
              [nsp_dtcon], [nsp_inst], [nsp_instmem]]
          )
     )
);


(* theory data for code generator *)

type appgens = (int * (appgen * stamp)) Symtab.table

fun merge_appgens (x : appgens * appgens) =
  Symtab.merge (fn ((bounds1, (_, stamp1)), (bounds2, (_, stamp2))) =>
    bounds1 = bounds2 andalso stamp1 = stamp2) x

type target_data = {
  syntax_class: string Symtab.table,
  syntax_tyco: (itype CodegenSerializer.pretty_syntax * stamp) Symtab.table,
  syntax_const: (iterm CodegenSerializer.pretty_syntax * stamp) Symtab.table
};

fun map_target_data f { syntax_class, syntax_tyco, syntax_const } =
  let
    val (syntax_class, syntax_tyco, syntax_const) =
      f (syntax_class, syntax_tyco, syntax_const)
  in {
    syntax_class = syntax_class,
    syntax_tyco = syntax_tyco,
    syntax_const = syntax_const } : target_data
  end;

fun merge_target_data
  ({ syntax_class = syntax_class1, syntax_tyco = syntax_tyco1, syntax_const = syntax_const1 },
   { syntax_class = syntax_class2, syntax_tyco = syntax_tyco2, syntax_const = syntax_const2 }) =
  { syntax_class = Symtab.merge (op =) (syntax_class1, syntax_class2),
    syntax_tyco = Symtab.merge (eq_snd (op =)) (syntax_tyco1, syntax_tyco2),
    syntax_const = Symtab.merge (eq_snd (op =)) (syntax_const1, syntax_const2) } : target_data;

structure CodegenData = TheoryDataFun
(struct
  val name = "Pure/codegen_package";
  type T = {
    modl: module,
    appgens: appgens,
    target_data: target_data Symtab.table
  };
  val empty = {
    modl = empty_module,
    appgens = Symtab.empty,
    target_data =
      Symtab.empty
      |> Symtab.fold (fn (target, _) =>
           Symtab.update (target,
             { syntax_class = Symtab.empty, syntax_tyco = Symtab.empty, syntax_const = Symtab.empty })
         ) (! serializers)
  } : T;
  val copy = I;
  val extend = I;
  fun merge _ (
    { modl = modl1, appgens = appgens1,
      target_data = target_data1 },
    { modl = modl2, appgens = appgens2,
      target_data = target_data2 }
  ) = {
    modl = merge_module (modl1, modl2),
    appgens = merge_appgens (appgens1, appgens2),
    target_data = Symtab.join (K merge_target_data) (target_data1, target_data2)
  };
  fun print thy (data : T) =
    let
      val module = #modl data
    in
      (Pretty.writeln o Pretty.chunks) [pretty_module module, pretty_deps module]
    end;
end);

val _ = Context.add_setup CodegenData.init;

fun map_codegen_data f thy =
  case CodegenData.get thy
   of { modl, appgens, target_data } =>
      let val (modl, appgens, target_data) =
        f (modl, appgens, target_data)
      in CodegenData.put { modl = modl, appgens = appgens,
           target_data = target_data } thy end;

val print_code = CodegenData.print;

val purge_code = map_codegen_data (fn (_, appgens, target_data) =>
  (empty_module, appgens, target_data));


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

fun idf_of_const thy thmtab (c_ty as (c, ty)) =
  if is_some (CodegenTheorems.get_dtyp_of_cons thmtab c_ty) then
    CodegenNames.const thy c_ty
    |> add_nsp nsp_dtcon
  else if (is_some o CodegenConsts.class_of_classop thy o CodegenConsts.typinst_of_typ thy) c_ty then
    CodegenNames.const thy c_ty
    |> add_nsp nsp_mem
  else
    CodegenNames.const thy c_ty
    |> add_nsp nsp_const;

fun const_of_idf thy idf =
  case dest_nsp nsp_const idf
   of SOME c => CodegenNames.const_rev thy c |> SOME
    | _ => (case dest_nsp nsp_dtcon idf
   of SOME c => CodegenNames.const_rev thy c |> SOME
    | _ => (case dest_nsp nsp_mem idf
   of SOME c => CodegenNames.const_rev thy c |> SOME
    | _ => NONE));


(* application generators *)

fun gen_add_appconst prep_const (raw_c, appgen) thy =
  let
    val c = prep_const thy raw_c;
    val i = (length o fst o strip_type o Sign.the_const_type thy) c
  in map_codegen_data
    (fn (modl, appgens, target_data) =>
       (modl,
        appgens |> Symtab.update (c, (i, (appgen, stamp ()))),
        target_data)) thy
  end;

val add_appconst = gen_add_appconst Sign.intern_const;
val add_appconst_i = gen_add_appconst (K I);


(* extraction kernel *)

fun check_strict thy f x ((false, _), _) =
      false
  | check_strict thy f x ((_, SOME targets), _) =
      exists (
        is_none o (fn tab => Symtab.lookup tab x) o f o the
          o (Symtab.lookup ((#target_data o CodegenData.get) thy))
      ) targets
  | check_strict thy f x ((true, _), _) =
      true;

fun no_strict ((_, targets), thmtab) = ((false, targets), thmtab);

fun sortlookups_const thy thmtab (c, typ_ctxt) =
  let
    val typ_decl = case CodegenTheorems.get_fun_thms thmtab (c, typ_ctxt)
     of thms as thm :: _ => CodegenTheorems.extr_typ thy thm
      | [] => (case AxClass.class_of_param thy c
         of SOME class => (case ClassPackage.the_consts_sign thy class of (v, cs) =>
              (Logic.varifyT o map_type_tfree (fn u as (w, _) =>
                if w = v then TFree (v, [class]) else TFree u))
              ((the o AList.lookup (op =) cs) c))
          | NONE => Sign.the_const_type thy c);
  in
    Vartab.empty
    |> Sign.typ_match thy (typ_decl, typ_ctxt) 
    |> Vartab.dest
    |> map (fn (_, (sort, ty)) => ClassPackage.sortlookup thy (ty, sort))
    |> filter_out null
  end;

fun ensure_def_class thy tabs cls trns =
  let
    fun defgen_class thy (tabs as (_, thmtab)) cls trns =
      case class_of_idf thy cls
       of SOME cls =>
            let
              val (v, cs) = (ClassPackage.the_consts_sign thy) cls;
              val sortctxts = map (ClassPackage.sortcontext_of_typ thy o snd) cs;
              val idfs = map (idf_of_const thy thmtab) cs;
            in
              trns
              |> debug_msg (fn _ => "trying defgen class declaration for " ^ quote cls)
              |> fold_map (ensure_def_class thy tabs) (ClassPackage.the_superclasses thy cls)
              ||>> (fold_map (exprgen_type thy tabs) o map snd) cs
              ||>> (fold_map o fold_map) (exprgen_tyvar_sort thy tabs) sortctxts
              |-> (fn ((supcls, memtypes), sortctxts) => succeed
                (Class (supcls, (unprefix "'" v, idfs ~~ (sortctxts ~~ memtypes)))))
            end
        | _ =>
            trns
            |> fail ("No class definition found for " ^ quote cls);
    val cls' = idf_of_class thy cls;
  in
    trns
    |> debug_msg (fn _ => "generating class " ^ quote cls)
    |> ensure_def (defgen_class thy tabs) true ("generating class " ^ quote cls) cls'
    |> pair cls'
  end
and ensure_def_tyco thy (tabs as (_, thmtab)) tyco trns =
  let
    val tyco' = idf_of_tyco thy tyco;
    val strict = check_strict thy #syntax_tyco tyco' tabs;
    fun defgen_datatype thy (tabs as (_, thmtab)) dtco trns =
      case tyco_of_idf thy dtco
       of SOME dtco =>
         (case CodegenTheorems.get_dtyp_spec thmtab dtco
             of SOME (vars, cos) =>
                  trns
                  |> debug_msg (fn _ => "trying defgen datatype for " ^ quote dtco)
                  |> fold_map (exprgen_tyvar_sort thy tabs) vars
                  ||>> fold_map (fn (c, tys) =>
                    fold_map (exprgen_type thy tabs) tys
                    #-> (fn tys' => pair (idf_of_const thy thmtab (c, tys ---> Type (dtco, map TFree vars)), tys'))) cos
                  |-> (fn (vars, cos) => succeed (Datatype
                       (vars, cos)))
              | NONE =>
                  trns
                  |> fail ("No datatype found for " ^ quote dtco))
        | NONE =>
            trns
            |> fail ("Not a type constructor: " ^ quote dtco)
  in
    trns
    |> debug_msg (fn _ => "generating type constructor " ^ quote tyco)
    |> ensure_def (defgen_datatype thy tabs) strict
        ("generating type constructor " ^ quote tyco) tyco'
    |> pair tyco'
  end
and exprgen_tyvar_sort thy tabs (v, sort) trns =
  trns
  |> fold_map (ensure_def_class thy tabs) (ClassPackage.operational_sort_of thy sort)
  |-> (fn sort => pair (unprefix "'" v, sort))
and exprgen_type thy tabs (TVar _) trns =
      error "TVar encountered in typ during code generation"
  | exprgen_type thy tabs (TFree v_s) trns =
      trns
      |> exprgen_tyvar_sort thy tabs v_s
      |-> (fn (v, sort) => pair (ITyVar v))
  | exprgen_type thy tabs (Type ("fun", [t1, t2])) trns =
      trns
      |> exprgen_type thy tabs t1
      ||>> exprgen_type thy tabs t2
      |-> (fn (t1', t2') => pair (t1' `-> t2'))
  | exprgen_type thy tabs (Type (tyco, tys)) trns =
      trns
      |> ensure_def_tyco thy tabs tyco
      ||>> fold_map (exprgen_type thy tabs) tys
      |-> (fn (tyco, tys) => pair (tyco `%% tys));

fun exprgen_classlookup thy tabs (ClassPackage.Instance (inst, ls)) trns =
      trns
      |> ensure_def_inst thy tabs inst
      ||>> (fold_map o fold_map) (exprgen_classlookup thy tabs) ls
      |-> (fn (inst, ls) => pair (Instance (inst, ls)))
  | exprgen_classlookup thy tabs (ClassPackage.Lookup (clss, (v, (i, j)))) trns =
      trns
      |> fold_map (ensure_def_class thy tabs) clss
      |-> (fn clss => pair (Lookup (clss, (v |> unprefix "'", if j = 1 then ~1 else i))))
and mk_fun thy (tabs as (_, thmtab)) (c, ty) trns =
  case CodegenTheorems.get_fun_thms thmtab (c, ty)
   of eq_thms as eq_thm :: _ =>
        let
          val msg = cat_lines ("generating code for theorems " :: map string_of_thm eq_thms);
          val ty = (Logic.unvarifyT o CodegenTheorems.extr_typ thy) eq_thm
          val sortcontext = ClassPackage.sortcontext_of_typ thy ty;
          fun dest_eqthm eq_thm =
            let
              val ((t, args), rhs) =
                (apfst strip_comb o Logic.dest_equals o Logic.legacy_unvarify o prop_of) eq_thm;
            in case t
             of Const (c', _) => if c' = c then (args, rhs)
                 else error ("Illegal function equation for " ^ quote c
                   ^ ", actually defining " ^ quote c')
              | _ => error ("Illegal function equation for " ^ quote c)
            end;
          fun exprgen_eq (args, rhs) trns =
            trns
            |> fold_map (exprgen_term thy tabs) args
            ||>> exprgen_term thy tabs rhs;
          fun checkvars (args, rhs) =
            if CodegenThingol.vars_distinct args then (args, rhs)
            else error ("Repeated variables on left hand side of function")
        in
          trns
          |> message msg (fn trns => trns
          |> fold_map (exprgen_eq o dest_eqthm) eq_thms
          |-> (fn eqs => pair (map checkvars eqs))
          ||>> fold_map (exprgen_tyvar_sort thy tabs) sortcontext
          ||>> exprgen_type thy tabs ty
          |-> (fn ((eqs, sortctxt), ty) => (pair o SOME) ((eqs, (sortctxt, ty)),
            map snd sortcontext)))
        end
    | [] => (NONE, trns)
and ensure_def_inst thy tabs (cls, tyco) trns =
  let
    fun defgen_inst thy (tabs as (_, thmtab)) inst trns =
      case inst_of_idf thy inst
       of SOME (class, tyco) =>
            let
              val (arity, memdefs) = ClassPackage.the_inst_sign thy (class, tyco);
              val (_, members) = ClassPackage.the_consts_sign thy class;
              val arity_typ = Type (tyco, (map TFree arity));
              val operational_arity = map_filter (fn (v, sort) =>
                case ClassPackage.operational_sort_of thy sort
                 of [] => NONE
                  | sort => SOME (v, sort)) arity;
              fun mk_instmemname (m, ty) =
                NameSpace.append (NameSpace.append ((NameSpace.drop_base o NameSpace.drop_base)
                  inst) nsp_instmem) (NameSpace.base (idf_of_const thy thmtab (m, ty)));
              fun gen_suparity supclass trns =
                trns
                |> ensure_def_class thy tabs supclass
                ||>> fold_map (exprgen_classlookup thy tabs)
                      (ClassPackage.sortlookup thy (arity_typ, [supclass]));
              fun gen_membr ((m0, ty0), (m, ty)) trns =
                trns
                |> ensure_def_const thy tabs (m0, ty0)
                ||>> exprgen_term thy tabs (Const (m, ty));
            in
              trns
              |> debug_msg (fn _ => "trying defgen class instance for (" ^ quote cls
                   ^ ", " ^ quote tyco ^ ")")
              |> ensure_def_class thy tabs class
              ||>> ensure_def_tyco thy tabs tyco
              ||>> fold_map (exprgen_tyvar_sort thy tabs) arity
              ||>> fold_map gen_suparity (ClassPackage.the_superclasses thy class)
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
    |> ensure_def (defgen_inst thy tabs) true
         ("generating instance " ^ quote cls ^ " / " ^ quote tyco) inst
    |> pair inst
  end
and ensure_def_const thy (tabs as (_, thmtab)) (c, ty) trns =
  let
    fun defgen_datatypecons thy (tabs as (_, thmtab)) co trns =
      case CodegenTheorems.get_dtyp_of_cons thmtab ((the o const_of_idf thy) co)
       of SOME tyco =>
            trns
            |> debug_msg (fn _ => "trying defgen datatype constructor for " ^ quote co)
            |> ensure_def_tyco thy tabs tyco
            |-> (fn _ => succeed Bot)
        | _ =>
            trns
            |> fail ("Not a datatype constructor: "
                ^ (quote o CodegenConsts.string_of_const_typ thy) (c, ty));
    fun defgen_clsmem thy (tabs as (_, thmtab)) m trns =
      case CodegenConsts.class_of_classop thy
        ((CodegenConsts.typinst_of_typ thy o the o const_of_idf thy) m)
       of SOME class =>
            trns
            |> debug_msg (fn _ => "trying defgen class member for " ^ quote m)
            |> ensure_def_class thy tabs class
            |-> (fn _ => succeed Bot)
        | _ =>
            trns |> fail ("No class found for " ^ (quote o CodegenConsts.string_of_const_typ thy) (c, ty))
    fun defgen_funs thy (tabs as (_, thmtab)) c' trns =
        trns
        |> mk_fun thy tabs ((the o const_of_idf thy) c')
        |-> (fn SOME (funn, _) => succeed (Fun funn)
              | NONE => fail ("No defining equations found for "
                   ^ (quote o CodegenConsts.string_of_const_typ thy) (c, ty)))
    fun get_defgen tabs idf strict =
      if (is_some oo dest_nsp) nsp_const idf
      then defgen_funs thy tabs strict
      else if (is_some oo dest_nsp) nsp_mem idf
      then defgen_clsmem thy tabs strict
      else if (is_some oo dest_nsp) nsp_dtcon idf
      then defgen_datatypecons thy tabs strict
      else error ("Illegal shallow name space for constant: " ^ quote idf);
    val idf = idf_of_const thy thmtab (c, ty);
    val strict = check_strict thy #syntax_const idf tabs;
  in
    trns
    |> debug_msg (fn _ => "generating constant "
        ^ (quote o CodegenConsts.string_of_const_typ thy) (c, ty))
    |> ensure_def (get_defgen tabs idf) strict ("generating constant "
         ^ CodegenConsts.string_of_const_typ thy (c, ty)) idf
    |> pair idf
  end
and exprgen_term thy tabs (Const (f, ty)) trns =
      trns
      |> appgen thy tabs ((f, ty), [])
      |-> (fn e => pair e)
  | exprgen_term thy tabs (Var _) trns =
      error "Var encountered in term during code generation"
  | exprgen_term thy tabs (Free (v, ty)) trns =
      trns
      |> exprgen_type thy tabs ty
      |-> (fn ty => pair (IVar v))
  | exprgen_term thy tabs (Abs (raw_v, ty, raw_t)) trns =
      let
        val (v, t) = Syntax.variant_abs (CodegenNames.purify_var raw_v, ty, raw_t);
      in
        trns
        |> exprgen_type thy tabs ty
        ||>> exprgen_term thy tabs t
        |-> (fn (ty, e) => pair ((v, ty) `|-> e))
      end
  | exprgen_term thy tabs (t as t1 $ t2) trns =
      let
        val (t', ts) = strip_comb t
      in case t'
       of Const (f, ty) =>
            trns
            |> appgen thy tabs ((f, ty), ts)
            |-> (fn e => pair e)
        | _ =>
            trns
            |> exprgen_term thy tabs t'
            ||>> fold_map (exprgen_term thy tabs) ts
            |-> (fn (e, es) => pair (e `$$ es))
      end
and appgen_default thy (tabs as (_, thmtab)) ((c, ty), ts) trns =
  trns
  |> ensure_def_const thy tabs (c, ty)
  ||>> exprgen_type thy tabs ty
  ||>> (fold_map o fold_map) (exprgen_classlookup thy tabs)
         (sortlookups_const thy thmtab (c, ty))
  ||>> fold_map (exprgen_term thy tabs) ts
  |-> (fn (((c, ty), ls), es) =>
         pair (IConst (c, (ls, ty)) `$$ es))
and appgen thy tabs ((f, ty), ts) trns =
  case Symtab.lookup ((#appgens o CodegenData.get) thy) f
   of SOME (i, (ag, _)) =>
        if length ts < i then
          let
            val tys = Library.take (i - length ts, ((fst o strip_type) ty));
            val vs = Name.names (Name.declare f Name.context) "a" tys;
          in
            trns
            |> fold_map (exprgen_type thy tabs) tys
            ||>> ag thy tabs ((f, ty), ts @ map Free vs)
            |-> (fn (tys, e) => pair (map2 (fn (v, _) => pair v) vs tys `|--> e))
          end
        else if length ts > i then
          trns
          |> ag thy tabs ((f, ty), Library.take (i, ts))
          ||>> fold_map (exprgen_term thy tabs) (Library.drop (i, ts))
          |-> (fn (e, es) => pair (e `$$ es))
        else
          trns
          |> ag thy tabs ((f, ty), ts)
    | NONE =>
        trns
        |> appgen_default thy tabs ((f, ty), ts);


(* parametrized generators, for instantiation in HOL *)

fun appgen_rep_bin int_of_numeral thy tabs (app as (c as (_, ty), [bin])) trns =
  case try (int_of_numeral thy) bin
   of SOME i => if i < 0 then (*preprocessor eliminates negative numerals*)
        trns
        |> appgen_default thy (no_strict tabs) app
      else
        trns
        |> exprgen_term thy (no_strict tabs) (Const c)
        ||>> exprgen_term thy (no_strict tabs) bin
        |-> (fn (e1, e2) => pair (CodegenThingol.INum (i, e1 `$ e2)))
    | NONE =>
        trns
        |> appgen_default thy tabs app;

fun appgen_char char_to_index thy tabs (app as ((_, ty), _)) trns =
  case (char_to_index o list_comb o apfst Const) app
   of SOME i =>
        trns
        |> exprgen_type thy tabs ty
        ||>> appgen_default thy tabs app
        |-> (fn (_, e0) => pair (IChar (chr i, e0)))
    | NONE =>
        trns
        |> appgen_default thy tabs app;

fun appgen_case dest_case_expr thy tabs (app as (c_ty, ts)) trns =
  let
    val SOME ([], ((st, sty), ds)) = dest_case_expr thy (list_comb (Const c_ty, ts));
    fun clausegen (dt, bt) trns =
      trns
      |> exprgen_term thy tabs dt
      ||>> exprgen_term thy tabs bt;
  in
    trns
    |> exprgen_term thy tabs st
    ||>> exprgen_type thy tabs sty
    ||>> fold_map clausegen ds
    ||>> appgen_default thy tabs app
    |-> (fn (((se, sty), ds), e0) => pair (ICase (((se, sty), ds), e0)))
  end;

fun appgen_let thy tabs (app as (_, [st, ct])) trns =
  trns
  |> exprgen_term thy tabs ct
  ||>> exprgen_term thy tabs st
  ||>> appgen_default thy tabs app
  |-> (fn (((v, ty) `|-> be, se), e0) =>
            pair (ICase (((se, ty), case be
              of ICase (((IVar w, _), ds), _) => if v = w then ds else [(IVar v, be)]
               | _ => [(IVar v, be)]
            ), e0))
        | (_, e0) => pair e0);

fun appgen_wfrec thy (tabs as (_, thmtab)) ((c, ty), [_, tf, tx]) trns =
  let
    val ty_def = (op ---> o apfst tl o strip_type o Logic.unvarifyT o Sign.the_const_type thy) c;
    val ty' = (op ---> o apfst tl o strip_type) ty;
    val idf = idf_of_const thy thmtab (c, ty);
  in
    trns
    |> ensure_def ((K o fail) "no extraction for wfrec") false ("generating wfrec") idf
    |> exprgen_type thy tabs ty'
    ||>> (fold_map o fold_map) (exprgen_classlookup thy tabs)
           (sortlookups_const thy thmtab (c, ty))
    ||>> exprgen_type thy tabs ty_def
    ||>> exprgen_term thy tabs tf
    ||>> exprgen_term thy tabs tx
    |-> (fn ((((_, ls), ty), tf), tx) => pair (IConst (idf, (ls, ty)) `$ tf `$ tx))
  end;



(** theory interface **)

fun mk_tabs thy targets cs =
  ((true, targets), CodegenTheorems.mk_thmtab thy cs);

fun get_serializer target =
  case Symtab.lookup (!serializers) target
   of SOME seri => seri
    | NONE => Scan.fail_with (fn _ => "Unknown code target language: " ^ quote target) ();

fun map_module f =
  map_codegen_data (fn (modl, gens, target_data) =>
    (f modl, gens, target_data));

fun purge_defs NONE thy =
      map_module (K CodegenThingol.empty_module) thy
  | purge_defs (SOME []) thy =
      thy
  | purge_defs (SOME cs) thy =
      map_module (K CodegenThingol.empty_module) thy;
      (*let
        val tabs = mk_tabs thy NONE;
        val idfs = map (idf_of_const' thy tabs) cs;
        fun purge idfs modl =
          CodegenThingol.purge_module (filter (can (get_def modl)) idfs) modl
      in
        map_module (purge idfs) thy
      end;*)

fun expand_module targets cs init gen arg thy =
  thy
  |> CodegenTheorems.notify_dirty
  |> `(#modl o CodegenData.get)
  |> (fn (modl, thy) =>
        (start_transact init (gen thy (mk_tabs thy targets cs) arg) modl, thy))
  |-> (fn (x, modl) => map_module (K modl) #> pair x);

fun consts_of t =
  fold_aterms (fn Const c => cons c | _ => I) t [];

fun codegen_term t thy =
  let
    val _ = Thm.cterm_of thy t;
(*     val _ = writeln "STARTING GENERATION";  *)
(*     val _ = (writeln o Sign.string_of_term thy) t;  *)
  in
    thy
    |> expand_module (SOME [] (*(Symtab.keys (#target_data (CodegenData.get thy)))*)) (consts_of t) NONE exprgen_term t
  end;

val is_dtcon = has_nsp nsp_dtcon;

fun consts_of_idfs thy =
  map (the o const_of_idf thy);

fun idfs_of_consts thy cs =
  map (idf_of_const thy (snd (mk_tabs thy NONE cs))) cs;

fun get_root_module thy =
  thy
  |> CodegenTheorems.notify_dirty
  |> `(#modl o CodegenData.get);

fun eval_term (ref_spec, t) thy =
  let
    fun preprocess_term t =
      let
        val x = Free (Name.variant (add_term_names (t, [])) "x", fastype_of t);
        (* fake definition *)
        val eq = setmp quick_and_dirty true (SkipProof.make_thm thy)
          (Logic.mk_equals (x, t));
        fun err () = error "preprocess_term: bad preprocessor"
      in case map prop_of (CodegenTheorems.preprocess thy [eq])
       of [Const ("==", _) $ x' $ t'] => if x = x' then t' else err ()
        | _ => err ()
      end;
    val target_data =
      ((fn data => (the o Symtab.lookup data) "ml") o #target_data o CodegenData.get) thy;
    val eval = CodegenSerializer.eval_term nsp_eval nsp_dtcon [[nsp_module], [nsp_class, nsp_tyco], [nsp_const, nsp_dtcon, nsp_class, nsp_mem, nsp_inst, nsp_instmem], [nsp_eval]]
      ((Option.map fst oo Symtab.lookup) (#syntax_tyco target_data),
       (Option.map fst oo Symtab.lookup) (#syntax_const target_data))
      (Symtab.keys (#syntax_tyco target_data) @ Symtab.keys (#syntax_const target_data))
  in
    thy
    |> codegen_term (preprocess_term t)
    ||>> `(#modl o CodegenData.get)
    |-> (fn (t', modl) => `(fn _ => eval (ref_spec, t') modl))
  end;

fun get_ml_fun_datatype thy resolv =
  let
    val target_data =
      ((fn data => (the o Symtab.lookup data) "ml") o #target_data o CodegenData.get) thy;
  in
    CodegenSerializer.ml_fun_datatype nsp_dtcon
      ((Option.map fst oo Symtab.lookup o #syntax_tyco) target_data,
      (Option.map fst oo Symtab.lookup o #syntax_const) target_data)
      resolv
  end;


(** target languages **)

(* syntax *)

fun read_typ thy =
  Sign.read_typ (thy, K NONE);

fun read_quote get reader consts_of gen raw thy =
  let
    val it = reader thy raw;
    val cs = consts_of it;
  in
    thy
    |> expand_module (SOME (Symtab.keys (#target_data (CodegenData.get thy)))) cs ((SOME o get) thy)
         (fn thy => fn tabs => gen thy tabs) [it]
    |-> (fn [x] => pair x)
  end;

fun gen_add_syntax_class prep_class class target pretty thy =
  thy
  |> map_codegen_data
    (fn (modl, gens, target_data) =>
       (modl, gens,
        target_data |> Symtab.map_entry target
          (map_target_data
            (fn (syntax_class, syntax_tyco, syntax_const) =>
             (syntax_class
              |> Symtab.update (prep_class thy class, pretty), syntax_tyco, syntax_const)))));

val add_syntax_class = gen_add_syntax_class Sign.intern_class;

fun parse_syntax_tyco raw_tyco =
  let
    fun prep_tyco thy raw_tyco =
      raw_tyco
      |> Sign.intern_type thy
      |> idf_of_tyco thy;
    fun no_args_tyco thy raw_tyco =
      AList.lookup (op =) ((NameSpace.dest_table o #types o Type.rep_tsig o Sign.tsig_of) thy)
        (Sign.intern_type thy raw_tyco)
      |> (fn SOME ((Type.LogicalType i), _) => i);
    fun mk reader target thy =
      let
        val _ = get_serializer target;
        val tyco = prep_tyco thy raw_tyco;
      in
        thy
        |> reader
        |-> (fn pretty => map_codegen_data
          (fn (modl, gens, target_data) =>
             (modl, gens,
              target_data |> Symtab.map_entry target
                (map_target_data
                  (fn (syntax_class, syntax_tyco, syntax_const) =>
                   (syntax_class, syntax_tyco |> Symtab.update
                      (tyco, (pretty, stamp ())),
                    syntax_const))))))
      end;
  in
    CodegenSerializer.parse_syntax (fn thy => no_args_tyco thy raw_tyco)
    (read_quote (fn thy => prep_tyco thy raw_tyco) read_typ (K [])
      (fn thy => fn tabs => fold_map (exprgen_type thy tabs)))
    #-> (fn reader => pair (mk reader))
  end;

fun add_pretty_syntax_const c target pretty =
  map_codegen_data
    (fn (modl, gens, target_data) =>
       (modl, gens,
        target_data |> Symtab.map_entry target
          (map_target_data
            (fn (syntax_class, syntax_tyco, syntax_const) =>
             (syntax_class, syntax_tyco,
              syntax_const
              |> Symtab.update
                 (c, (pretty, stamp ())))))));

fun parse_syntax_const raw_const =
  let
    fun prep_const thy raw_const =
      let
        val c_ty = CodegenConsts.read_const_typ thy raw_const
      in idf_of_const thy (snd (mk_tabs thy NONE [c_ty])) c_ty end;
    fun no_args_const thy raw_const =
      (length o fst o strip_type o snd o CodegenConsts.read_const_typ thy) raw_const;
    fun mk reader target thy =
      let
        val _ = get_serializer target;
        val c = prep_const thy raw_const;
      in
        thy
        |> reader
        |-> (fn pretty => add_pretty_syntax_const c target pretty)
      end;
  in
    CodegenSerializer.parse_syntax (fn thy => no_args_const thy raw_const)
      (read_quote (fn thy => prep_const thy raw_const) Sign.read_term consts_of
      (fn thy => fn tabs => fold_map (exprgen_term thy tabs)))
    #-> (fn reader => pair (mk reader))
  end;

fun add_pretty_list raw_nil raw_cons (target, seri) thy =
  let
    val _ = get_serializer target;
    fun prep_const raw =
      let
        val c = Sign.intern_const thy raw
      in (c, Sign.the_const_type thy c) end;
    val nil' = prep_const raw_nil;
    val cons' = prep_const raw_cons;
    val tabs = mk_tabs thy NONE [nil', cons'];
    fun mk_const c_ty =
      idf_of_const thy (snd tabs) c_ty;
    val nil'' = mk_const nil';
    val cons'' = mk_const cons';
    val pr = CodegenSerializer.pretty_list nil'' cons'' seri;
  in
    thy
    |> add_pretty_syntax_const cons'' target pr
  end;



(** code basis change notifications **)

val _ = Context.add_setup (CodegenTheorems.add_notify purge_defs);



(** toplevel interface **)

local

fun generate_code targets (SOME raw_consts) thy =
      let
        val consts = map (CodegenConsts.read_const_typ thy) raw_consts;
        val _ = case targets of SOME targets => (map get_serializer targets; ()) | _ => ();
      in
        thy
        |> expand_module targets consts NONE (fold_map oo ensure_def_const) consts
        |-> (fn cs => pair (SOME cs))
      end
  | generate_code _ NONE thy =
      (NONE, thy);

fun serialize_code target seri raw_consts thy =
  let
    fun serialize cs thy =
      let
        val module = (#modl o CodegenData.get) thy;
        val target_data =
          thy
          |> CodegenData.get
          |> #target_data
          |> (fn data => (the oo Symtab.lookup) data target);
        val s_class = #syntax_class target_data
        val s_tyco = #syntax_tyco target_data
        val s_const = #syntax_const target_data
      in
        (seri (
          Symtab.lookup s_class,
          (Option.map fst oo Symtab.lookup) s_tyco,
          (Option.map fst oo Symtab.lookup) s_const
        ) (Symtab.keys s_class @ Symtab.keys s_tyco @ Symtab.keys s_const, cs) module : unit; thy)
      end;
  in
    thy
    |> generate_code (SOME [target]) raw_consts
    |-> (fn cs => serialize cs)
  end;

fun purge_consts raw_ts thy =
  let
    val cs = map (CodegenConsts.read_const_typ thy) raw_ts;
  in fold CodegenTheorems.purge_defs cs thy end;

structure P = OuterParse
and K = OuterKeyword

in

val (generateK, serializeK,
     syntax_classK, syntax_tycoK, syntax_constK,
     purgeK) =
  ("code_generate", "code_serialize",
   "code_classapp", "code_typapp", "code_constapp",
   "code_purge");

val generateP =
  OuterSyntax.command generateK "generate executable code for constants" K.thy_decl (
    (Scan.option (P.$$$ "(" |-- P.list1 P.name --| P.$$$ ")")
    >> (fn SOME ["-"] => SOME [] | ts => ts))
    -- Scan.repeat1 P.term
    >> (fn (targets, raw_consts) =>
          Toplevel.theory (generate_code targets (SOME raw_consts) #> snd))
  );

val serializeP =
  OuterSyntax.command serializeK "serialize executable code for constants" K.thy_decl (
    P.name
    -- Scan.option (Scan.repeat1 P.term)
    #-> (fn (target, raw_consts) =>
          P.$$$ "("
          |-- get_serializer target
          --| P.$$$ ")"
          >> (fn seri =>
            Toplevel.theory (serialize_code target seri raw_consts)
          ))
  );

val syntax_classP =
  OuterSyntax.command syntax_classK "define code syntax for class" K.thy_decl (
    Scan.repeat1 (
      P.xname
      -- Scan.repeat1 (
           P.name -- P.string
         )
    )
    >> (Toplevel.theory oo fold) (fn (raw_class, syns) =>
          fold (fn (target, p) => add_syntax_class raw_class target p) syns)
  );

val syntax_tycoP =
  OuterSyntax.command syntax_tycoK "define code syntax for type constructor" K.thy_decl (
    Scan.repeat1 (
      P.xname
      #-> (fn raw_tyco => Scan.repeat1 (
             P.name -- parse_syntax_tyco raw_tyco
          ))
    )
    >> (Toplevel.theory oo fold o fold)
          (fn (target, modifier) => modifier target)
  );

val syntax_constP =
  OuterSyntax.command syntax_constK "define code syntax for constant" K.thy_decl (
    Scan.repeat1 (
      P.term
      #-> (fn raw_const => Scan.repeat1 (
             P.name -- parse_syntax_const raw_const
          ))
    )
    >> (Toplevel.theory oo fold o fold)
          (fn (target, modifier) => modifier target)
  );

val purgeP =
  OuterSyntax.command purgeK "purge all incrementally generated code" K.thy_decl
    (Scan.succeed (Toplevel.theory purge_code));

val _ = OuterSyntax.add_parsers [generateP, serializeP,
  syntax_classP, syntax_tycoP, syntax_constP,
  purgeP];

end; (* local *)

end; (* struct *)

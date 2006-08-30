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

  val add_pretty_list: string -> string -> string -> (Pretty.T list -> Pretty.T)
   -> ((string -> string) * (string -> string)) option -> int * string
   -> theory -> theory;
  val add_pretty_ml_string: string -> string -> string -> string
   -> (string -> string) -> (string -> string) -> string -> theory -> theory;
  val purge_code: theory -> theory;

  type appgen;
  val add_appconst: string * appgen -> theory -> theory;
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
       #ml CodegenSerializer.serializers
       |> apsnd (fn seri => seri
            nsp_dtcon
            [[nsp_module], [nsp_class, nsp_tyco],
              [nsp_const, nsp_dtcon, nsp_class, nsp_mem, nsp_inst]]
          )
     )
  |> Symtab.update (
       #haskell CodegenSerializer.serializers
       |> apsnd (fn seri => seri
            (nsp_dtcon, [nsp_module, nsp_class, nsp_tyco, nsp_dtcon])
            [[nsp_module], [nsp_class], [nsp_tyco], [nsp_const,  nsp_mem],
              [nsp_dtcon], [nsp_inst]]
          )
     )
);


(* theory data  *)

type appgen = theory -> CodegenTheorems.thmtab -> bool * string list option
  -> (string * typ) * term list -> transact -> iterm * transact;

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
             { syntax_class = Symtab.empty, syntax_inst = Symtab.empty,
               syntax_tyco = Symtab.empty, syntax_const = Symtab.empty })
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

fun get_serializer target =
  case Symtab.lookup (!serializers) target
   of SOME seri => seri
    | NONE => Scan.fail_with (fn _ => "Unknown code target language: " ^ quote target) ();

fun serialize thy target seri cs =
  let
    val data = CodegenData.get thy
    val code = #modl data;
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
    val _ = get_serializer target;
  in
    map_codegen_data (fn (modl, appgens, target_data) => 
      (modl, appgens, Symtab.map_entry target (fn { syntax_class, syntax_inst, syntax_tyco, syntax_const } =>
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

val print_code = CodegenData.print;

fun map_module f =
  map_codegen_data (fn (modl, gens, target_data) =>
    (f modl, gens, target_data));

val purge_code = map_module (K CodegenThingol.empty_module);

fun purge_defs NONE = purge_code
  | purge_defs (SOME []) = I
  | purge_defs (SOME cs) = purge_code;


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
          o (Symtab.lookup ((#target_data o CodegenData.get) thy))
      ) targets
  | check_strict thy f x (true, _) =
      true;

fun no_strict (_, targets) = (false, targets);

(*FIXME: provide a unified view on this in codegen_consts.ML*)
fun sortlookups_const thy thmtab (c, ty_ctxt) =
  let
    val ty_decl = case CodegenTheorems.get_fun_thms thmtab (c, ty_ctxt)
     of thms as thm :: _ => CodegenTheorems.extr_typ thy thm
      | [] => (case AxClass.class_of_param thy c
         of SOME class => (case ClassPackage.the_consts_sign thy class of (v, cs) =>
              (Logic.varifyT o map_type_tfree (fn u as (w, _) =>
                if w = v then TFree (v, [class]) else TFree u))
              ((the o AList.lookup (op =) cs) c))
          | NONE => Sign.the_const_type thy c);
  in
    Vartab.empty
    |> Sign.typ_match thy (ty_decl, ty_ctxt) 
    |> Vartab.dest
    |> map (fn (_, (sort, ty)) => ClassPackage.sortlookup thy (ty, sort))
    |> filter_out null
  end;

fun ensure_def_class thy thmtab strct cls trns =
  let
    fun defgen_class thy thmtab strct cls trns =
      case class_of_idf thy cls
       of SOME cls =>
            let
              val (v, cs) = (ClassPackage.the_consts_sign thy) cls;
              val sortctxts = map (ClassPackage.sortcontext_of_typ thy o snd) cs;
              val idfs = map (idf_of_const thy thmtab) cs;
            in
              trns
              |> debug_msg (fn _ => "trying defgen class declaration for " ^ quote cls)
              |> fold_map (ensure_def_class thy thmtab strct) (ClassPackage.the_superclasses thy cls)
              ||>> (fold_map (exprgen_type thy thmtab strct) o map snd) cs
              ||>> (fold_map o fold_map) (exprgen_tyvar_sort thy thmtab strct) sortctxts
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
    |> ensure_def (defgen_class thy thmtab strct) true ("generating class " ^ quote cls) cls'
    |> pair cls'
  end
and ensure_def_tyco thy thmtab strct tyco trns =
  let
    val tyco' = idf_of_tyco thy tyco;
    val strict = check_strict thy #syntax_tyco tyco' strct;
    fun defgen_datatype thy thmtab strct dtco trns =
      case tyco_of_idf thy dtco
       of SOME dtco =>
         (case CodegenTheorems.get_dtyp_spec thmtab dtco
             of SOME (vars, cos) =>
                  trns
                  |> debug_msg (fn _ => "trying defgen datatype for " ^ quote dtco)
                  |> fold_map (exprgen_tyvar_sort thy thmtab strct) vars
                  ||>> fold_map (fn (c, tys) =>
                    fold_map (exprgen_type thy thmtab strct) tys
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
    |> ensure_def (defgen_datatype thy thmtab strct) strict
        ("generating type constructor " ^ quote tyco) tyco'
    |> pair tyco'
  end
and exprgen_tyvar_sort thy thmtab strct (v, sort) trns =
  trns
  |> fold_map (ensure_def_class thy thmtab strct) (ClassPackage.operational_sort_of thy sort)
  |-> (fn sort => pair (unprefix "'" v, sort))
and exprgen_type thy thmtab strct (TVar _) trns =
      error "TVar encountered in typ during code generation"
  | exprgen_type thy thmtab strct (TFree v_s) trns =
      trns
      |> exprgen_tyvar_sort thy thmtab strct v_s
      |-> (fn (v, sort) => pair (ITyVar v))
  | exprgen_type thy thmtab strct (Type ("fun", [t1, t2])) trns =
      trns
      |> exprgen_type thy thmtab strct t1
      ||>> exprgen_type thy thmtab strct t2
      |-> (fn (t1', t2') => pair (t1' `-> t2'))
  | exprgen_type thy thmtab strct (Type (tyco, tys)) trns =
      trns
      |> ensure_def_tyco thy thmtab strct tyco
      ||>> fold_map (exprgen_type thy thmtab strct) tys
      |-> (fn (tyco, tys) => pair (tyco `%% tys));

fun exprgen_classlookup thy thmtab strct (ClassPackage.Instance (inst, ls)) trns =
      trns
      |> ensure_def_inst thy thmtab strct inst
      ||>> (fold_map o fold_map) (exprgen_classlookup thy thmtab strct) ls
      |-> (fn (inst, ls) => pair (Instance (inst, ls)))
  | exprgen_classlookup thy thmtab strct (ClassPackage.Lookup (clss, (v, (i, j)))) trns =
      trns
      |> fold_map (ensure_def_class thy thmtab strct) clss
      |-> (fn clss => pair (Lookup (clss, (v |> unprefix "'", if j = 1 then ~1 else i))))
and mk_fun thy thmtab strct (c, ty) trns =
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
            |> fold_map (exprgen_term thy thmtab strct) args
            ||>> exprgen_term thy thmtab strct rhs;
          fun checkvars (args, rhs) =
            if CodegenThingol.vars_distinct args then (args, rhs)
            else error ("Repeated variables on left hand side of function")
        in
          trns
          |> message msg (fn trns => trns
          |> fold_map (exprgen_eq o dest_eqthm) eq_thms
          |-> (fn eqs => pair (map checkvars eqs))
          ||>> fold_map (exprgen_tyvar_sort thy thmtab strct) sortcontext
          ||>> exprgen_type thy thmtab strct ty
          |-> (fn ((eqs, sortctxt), ty) => (pair o SOME) ((eqs, (sortctxt, ty)),
            map snd sortcontext)))
        end
    | [] => (NONE, trns)
and ensure_def_inst thy thmtab strct (cls, tyco) trns =
  let
    fun defgen_inst thy thmtab strct inst trns =
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
              fun gen_suparity supclass trns =
                trns
                |> ensure_def_class thy thmtab strct supclass
                ||>> fold_map (exprgen_classlookup thy thmtab strct)
                      (ClassPackage.sortlookup thy (arity_typ, [supclass]));
              fun gen_membr ((m0, ty0), (m, ty)) trns =
                trns
                |> ensure_def_const thy thmtab strct (m0, ty0)
                ||>> exprgen_term thy thmtab strct (Const (m, ty));
            in
              trns
              |> debug_msg (fn _ => "trying defgen class instance for (" ^ quote cls
                   ^ ", " ^ quote tyco ^ ")")
              |> ensure_def_class thy thmtab strct class
              ||>> ensure_def_tyco thy thmtab strct tyco
              ||>> fold_map (exprgen_tyvar_sort thy thmtab strct) arity
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
    |> ensure_def (defgen_inst thy thmtab strct) true
         ("generating instance " ^ quote cls ^ " / " ^ quote tyco) inst
    |> pair inst
  end
and ensure_def_const thy thmtab strct (c, ty) trns =
  let
    fun defgen_datatypecons thy thmtab strct co trns =
      case CodegenTheorems.get_dtyp_of_cons thmtab ((the o const_of_idf thy) co)
       of SOME tyco =>
            trns
            |> debug_msg (fn _ => "trying defgen datatype constructor for " ^ quote co)
            |> ensure_def_tyco thy thmtab strct tyco
            |-> (fn _ => succeed Bot)
        | _ =>
            trns
            |> fail ("Not a datatype constructor: "
                ^ (quote o CodegenConsts.string_of_const_typ thy) (c, ty));
    fun defgen_clsmem thy thmtab strct m trns =
      case CodegenConsts.class_of_classop thy
        ((CodegenConsts.typinst_of_typ thy o the o const_of_idf thy) m)
       of SOME class =>
            trns
            |> debug_msg (fn _ => "trying defgen class member for " ^ quote m)
            |> ensure_def_class thy thmtab strct class
            |-> (fn _ => succeed Bot)
        | _ =>
            trns |> fail ("No class found for " ^ (quote o CodegenConsts.string_of_const_typ thy) (c, ty))
    fun defgen_funs thy thmtab strct c' trns =
        trns
        |> mk_fun thy thmtab strct ((the o const_of_idf thy) c')
        |-> (fn SOME (funn, _) => succeed (Fun funn)
              | NONE => fail ("No defining equations found for "
                   ^ (quote o CodegenConsts.string_of_const_typ thy) (c, ty)))
    fun get_defgen thmtab strct idf strict =
      if (is_some oo dest_nsp) nsp_const idf
      then defgen_funs thy thmtab strct strict
      else if (is_some oo dest_nsp) nsp_mem idf
      then defgen_clsmem thy thmtab strct strict
      else if (is_some oo dest_nsp) nsp_dtcon idf
      then defgen_datatypecons thy thmtab strct strict
      else error ("Illegal shallow name space for constant: " ^ quote idf);
    val idf = idf_of_const thy thmtab (c, ty);
    val strict = check_strict thy #syntax_const idf strct;
  in
    trns
    |> debug_msg (fn _ => "generating constant "
        ^ (quote o CodegenConsts.string_of_const_typ thy) (c, ty))
    |> ensure_def (get_defgen thmtab strct idf) strict ("generating constant "
         ^ CodegenConsts.string_of_const_typ thy (c, ty)) idf
    |> pair idf
  end
and exprgen_term thy thmtab strct (Const (f, ty)) trns =
      trns
      |> appgen thy thmtab strct ((f, ty), [])
      |-> (fn e => pair e)
  | exprgen_term thy thmtab strct (Var _) trns =
      error "Var encountered in term during code generation"
  | exprgen_term thy thmtab strct (Free (v, ty)) trns =
      trns
      |> exprgen_type thy thmtab strct ty
      |-> (fn ty => pair (IVar v))
  | exprgen_term thy thmtab strct (Abs (raw_v, ty, raw_t)) trns =
      let
        val (v, t) = Syntax.variant_abs (CodegenNames.purify_var raw_v, ty, raw_t);
      in
        trns
        |> exprgen_type thy thmtab strct ty
        ||>> exprgen_term thy thmtab strct t
        |-> (fn (ty, e) => pair ((v, ty) `|-> e))
      end
  | exprgen_term thy thmtab strct (t as t1 $ t2) trns =
      let
        val (t', ts) = strip_comb t
      in case t'
       of Const (f, ty) =>
            trns
            |> appgen thy thmtab strct ((f, ty), ts)
            |-> (fn e => pair e)
        | _ =>
            trns
            |> exprgen_term thy thmtab strct t'
            ||>> fold_map (exprgen_term thy thmtab strct) ts
            |-> (fn (e, es) => pair (e `$$ es))
      end
and appgen_default thy thmtab strct ((c, ty), ts) trns =
  trns
  |> ensure_def_const thy thmtab strct (c, ty)
  ||>> exprgen_type thy thmtab strct ty
  ||>> (fold_map o fold_map) (exprgen_classlookup thy thmtab strct)
         (sortlookups_const thy thmtab (c, ty))
  ||>> fold_map (exprgen_term thy thmtab strct) ts
  |-> (fn (((c, ty), ls), es) =>
         pair (IConst (c, (ls, ty)) `$$ es))
and appgen thy thmtab strct ((f, ty), ts) trns =
  case Symtab.lookup ((#appgens o CodegenData.get) thy) f
   of SOME (i, (ag, _)) =>
        if length ts < i then
          let
            val tys = Library.take (i - length ts, ((fst o strip_type) ty));
            val vs = Name.names (Name.declare f Name.context) "a" tys;
          in
            trns
            |> fold_map (exprgen_type thy thmtab strct) tys
            ||>> ag thy thmtab strct ((f, ty), ts @ map Free vs)
            |-> (fn (tys, e) => pair (map2 (fn (v, _) => pair v) vs tys `|--> e))
          end
        else if length ts > i then
          trns
          |> ag thy thmtab strct ((f, ty), Library.take (i, ts))
          ||>> fold_map (exprgen_term thy thmtab strct) (Library.drop (i, ts))
          |-> (fn (e, es) => pair (e `$$ es))
        else
          trns
          |> ag thy thmtab strct ((f, ty), ts)
    | NONE =>
        trns
        |> appgen_default thy thmtab strct ((f, ty), ts);


(* parametrized application generators, for instantiation in object logic *)
(* (axiomatic extensions of extraction kernel *)

fun appgen_rep_bin int_of_numeral thy thmtab strct (app as (c as (_, ty), [bin])) trns =
  case try (int_of_numeral thy) bin
   of SOME i => if i < 0 then (*preprocessor eliminates negative numerals*)
        trns
        |> appgen_default thy thmtab (no_strict strct) app
      else
        trns
        |> exprgen_term thy thmtab (no_strict strct) (Const c)
        ||>> exprgen_term thy thmtab (no_strict strct) bin
        |-> (fn (e1, e2) => pair (CodegenThingol.INum (i, e1 `$ e2)))
    | NONE =>
        trns
        |> appgen_default thy thmtab strct app;

fun appgen_char char_to_index thy thmtab strct (app as ((_, ty), _)) trns =
  case (char_to_index o list_comb o apfst Const) app
   of SOME i =>
        trns
        |> exprgen_type thy thmtab strct ty
        ||>> appgen_default thy thmtab strct app
        |-> (fn (_, e0) => pair (IChar (chr i, e0)))
    | NONE =>
        trns
        |> appgen_default thy thmtab strct app;

fun appgen_case dest_case_expr thy thmtab strct (app as (c_ty, ts)) trns =
  let
    val SOME ([], ((st, sty), ds)) = dest_case_expr thy (list_comb (Const c_ty, ts));
    fun clausegen (dt, bt) trns =
      trns
      |> exprgen_term thy thmtab strct dt
      ||>> exprgen_term thy thmtab strct bt;
  in
    trns
    |> exprgen_term thy thmtab strct st
    ||>> exprgen_type thy thmtab strct sty
    ||>> fold_map clausegen ds
    ||>> appgen_default thy thmtab strct app
    |-> (fn (((se, sty), ds), e0) => pair (ICase (((se, sty), ds), e0)))
  end;

fun appgen_let thy thmtab strct (app as (_, [st, ct])) trns =
  trns
  |> exprgen_term thy thmtab strct ct
  ||>> exprgen_term thy thmtab strct st
  ||>> appgen_default thy thmtab strct app
  |-> (fn (((v, ty) `|-> be, se), e0) =>
            pair (ICase (((se, ty), case be
              of ICase (((IVar w, _), ds), _) => if v = w then ds else [(IVar v, be)]
               | _ => [(IVar v, be)]
            ), e0))
        | (_, e0) => pair e0);

fun appgen_wfrec thy thmtab strct ((c, ty), [_, tf, tx]) trns =
  let
    val ty_def = (op ---> o apfst tl o strip_type o Logic.unvarifyT o Sign.the_const_type thy) c;
    val ty' = (op ---> o apfst tl o strip_type) ty;
    val idf = idf_of_const thy thmtab (c, ty);
  in
    trns
    |> ensure_def ((K o fail) "no extraction for wfrec") false ("generating wfrec") idf
    |> exprgen_type thy thmtab strct ty'
    ||>> exprgen_type thy thmtab strct ty_def
    ||>> exprgen_term thy thmtab strct tf
    ||>> exprgen_term thy thmtab strct tx
    |-> (fn (((_, ty), tf), tx) => pair (IConst (idf, ([], ty)) `$ tf `$ tx))
  end;

fun add_appconst (c, appgen) thy =
  let
    val i = (length o fst o strip_type o Sign.the_const_type thy) c
  in map_codegen_data
    (fn (modl, appgens, target_data) =>
       (modl,
        appgens |> Symtab.update (c, (i, (appgen, stamp ()))),
        target_data)) thy
  end;



(** code generation interfaces **)

fun generate cs targets init gen it thy =
  thy
  |> CodegenTheorems.notify_dirty
  |> `(#modl o CodegenData.get)
  |> (fn (modl, thy) =>
        (start_transact init (gen thy (CodegenTheorems.mk_thmtab thy cs)
          (true, targets) it) modl, thy))
  |-> (fn (x, modl) => map_module (K modl) #> pair x);

fun consts_of t =
  fold_aterms (fn Const c => cons c | _ => I) t [];

fun codegen_term t thy =
  let
    val _ = Thm.cterm_of thy t;
  in
    thy
    |> generate (consts_of t) (SOME []) NONE exprgen_term t
  end;

val is_dtcon = has_nsp nsp_dtcon;

fun consts_of_idfs thy =
  map (the o const_of_idf thy);

fun idfs_of_consts thy cs =
  map (idf_of_const thy (CodegenTheorems.mk_thmtab thy cs)) cs;

fun get_root_module thy =
  thy
  |> CodegenTheorems.notify_dirty
  |> `(#modl o CodegenData.get);

fun eval_term (ref_spec, t) thy =
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
      in case map prop_of (CodegenTheorems.preprocess thy [eq])
       of [Const ("==", _) $ x' $ t'] => if x = x' then t' else err ()
        | _ => err ()
      end;
    val target_data =
      ((fn data => (the o Symtab.lookup data) "ml") o #target_data o CodegenData.get) thy;
    val eval = CodegenSerializer.eval_term nsp_eval nsp_dtcon [[nsp_module], [nsp_class, nsp_tyco], [nsp_const, nsp_dtcon, nsp_class, nsp_mem, nsp_inst], [nsp_eval]]
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



(** target syntax **)

local

fun gen_add_syntax_class prep_class prep_const raw_class target (syntax, raw_ops) thy =
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

fun gen_add_syntax_inst prep_class prep_tyco (raw_class, raw_tyco) target thy =
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
    val c_ty = prep_const thy raw_c;
    val c = idf_of_const thy (CodegenTheorems.mk_thmtab thy [c_ty]) c_ty;
  in
    thy
    |> map_target_data target (fn (syntax_class, syntax_inst, syntax_tyco, syntax_const) =>
         (syntax_class, syntax_inst, syntax_tyco, syntax_const
            |> Symtab.update (c, (syntax, stamp ()))))
  end;

fun idfs_of_const_names thy cs =
  let
    val cs' = AList.make (fn c => Sign.the_const_type thy c) cs
    val thmtab = CodegenTheorems.mk_thmtab thy cs'
  in AList.make (idf_of_const thy thmtab) cs' end;

fun read_quote reader consts_of target get_init gen raw_it thy =
  let
    val it = reader thy raw_it;
    val cs = consts_of it;
  in
    thy
    |> generate cs (SOME [target]) ((SOME o get_init) thy)
         (fn thy => fn thmtab => fn strct => gen thy thmtab strct) [it]
    |-> (fn [it'] => pair it')
  end;

fun parse_quote num_of reader consts_of target get_init gen adder =
  CodegenSerializer.parse_syntax num_of
    (read_quote reader consts_of target get_init gen)
  #-> (fn modifier => pair (modifier #-> adder target));

in

val add_syntax_class = gen_add_syntax_class Sign.intern_class CodegenConsts.read_const_typ;
val add_syntax_inst = gen_add_syntax_inst Sign.intern_class Sign.intern_type;

fun parse_syntax_tyco raw_tyco target =
  let
    fun intern thy = Sign.intern_type thy raw_tyco;
    fun num_of thy = Sign.arity_number thy (intern thy);
    fun idf_of thy = idf_of_tyco thy (intern thy);
    fun read_typ thy =
      Sign.read_typ (thy, K NONE);
  in
    parse_quote num_of read_typ (K []) target idf_of (fold_map ooo exprgen_type)
      (gen_add_syntax_tyco Sign.intern_type raw_tyco)
  end;

fun parse_syntax_const raw_const target =
  let
    fun intern thy = CodegenConsts.read_const_typ thy raw_const;
    fun num_of thy = (length o fst o strip_type o Sign.the_const_type thy o fst o intern) thy;
    fun idf_of thy =
      let
        val c_ty = intern thy;
        val c = idf_of_const thy (CodegenTheorems.mk_thmtab thy [c_ty]) c_ty;
      in c end;
  in
    parse_quote num_of Sign.read_term consts_of target idf_of (fold_map ooo exprgen_term)
      (gen_add_syntax_const CodegenConsts.read_const_typ raw_const)
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

fun generate_code targets (SOME raw_cs) thy =
      let
        val cs = map (CodegenConsts.read_const_typ thy) raw_cs;
        val _ = case targets of SOME targets => (map get_serializer targets; ()) | _ => ();
      in
        thy
        |> generate cs targets NONE (fold_map ooo ensure_def_const) cs
        |-> (fn cs => pair (SOME cs))
      end
  | generate_code _ NONE thy =
      (NONE, thy);

fun serialize_code target seri raw_cs thy =
  thy
  |> generate_code (SOME [target]) raw_cs
  |-> (fn cs => tap (fn thy => serialize thy target seri cs));

fun code raw_cs seris thy =
  let
    val cs = map (CodegenConsts.read_const_typ thy) raw_cs;
    val targets = map fst seris;
    val seris' = map_filter (fn (target, SOME seri) => SOME (target, seri) | _ => NONE) seris;
    fun generate' thy = case cs
     of [] => ([], thy)
      | _ =>
          thy
          |> generate cs (SOME targets) NONE (fold_map ooo ensure_def_const) cs;
    fun serialize' thy [] (target, seri) =
          serialize thy target seri NONE : unit
      | serialize' thy cs (target, seri) =
          serialize thy target seri (SOME cs) : unit;
  in
    thy
    |> generate'
    |-> (fn cs => tap (fn thy => map (serialize' thy cs) seris'))
  end;

fun purge_consts raw_ts thy =
  let
    val cs = map (CodegenConsts.read_const_typ thy) raw_ts;
  in fold CodegenTheorems.purge_defs cs thy end;

structure P = OuterParse
and K = OuterKeyword

in

val (codeK, generateK, serializeK,
     syntax_classK, syntax_instK, syntax_tycoK, syntax_constK,
     purgeK) =
  ("codeK", "code_generate", "code_serialize",
   "code_class", "code_instance", "code_typapp", "code_constapp",
   "code_purge");

val codeP =
  OuterSyntax.command codeK "generate and serialize executable code for constants" K.thy_decl (
    Scan.repeat P.term
    -- Scan.repeat (P.$$$ "(" |--
        P.name :-- (fn target => (get_serializer target >> SOME) || pair NONE)
        --| P.$$$ ")")
    >> (fn (raw_cs, seris) => Toplevel.theory (code raw_cs seris))
  );

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
           P.name -- (P.string -- Scan.optional
             (P.$$$ "(" |-- Scan.repeat1 (P.term -- P.string) --| P.$$$ ")") [])
         )
    )
    >> (Toplevel.theory oo fold) (fn (raw_class, syns) =>
          fold (fn (target, p) => add_syntax_class raw_class target p) syns)
  );

val syntax_instP =
  OuterSyntax.command syntax_instK "define code syntax for instance" K.thy_decl (
    Scan.repeat1 (
      P.$$$ "(" |-- P.xname --| P.$$$ "::" -- P.xname --| P.$$$ ")"
      -- Scan.repeat1 P.name
    )
    >> (Toplevel.theory oo fold) (fn (raw_inst, targets) =>
          fold (fn target => add_syntax_inst raw_inst target) targets)
  );

val syntax_tycoP =
  OuterSyntax.command syntax_tycoK "define code syntax for type constructor" K.thy_decl (
    Scan.repeat1 (
      P.xname
      #-> (fn raw_tyco => Scan.repeat1 (
             P.name #-> parse_syntax_tyco raw_tyco
          ))
    )
    >> (Toplevel.theory oo fold o fold)
          (fn modifier => modifier)
  );

val syntax_constP =
  OuterSyntax.command syntax_constK "define code syntax for constant" K.thy_decl (
    Scan.repeat1 (
      P.term
      #-> (fn raw_const => Scan.repeat1 (
             P.name #-> parse_syntax_const raw_const
          ))
    )
    >> (Toplevel.theory oo fold o fold)
          (fn modifier => modifier)
  );

val purgeP =
  OuterSyntax.command purgeK "purge all incrementally generated code" K.thy_decl
    (Scan.succeed (Toplevel.theory purge_code));

val _ = OuterSyntax.add_parsers [(*codeP, *)generateP, serializeP,
  syntax_classP, syntax_instP, syntax_tycoP, syntax_constP, purgeP];

end; (* local *)

(*code basis change notifications*)
val _ = Context.add_setup (CodegenTheorems.add_notify purge_defs);

end; (* struct *)

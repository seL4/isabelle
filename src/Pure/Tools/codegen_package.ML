(*  Title:      Pure/Tools/codegen_package.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Code generator from Isabelle theories to
intermediate language ("Thin-gol").
*)

signature CODEGEN_PACKAGE =
sig
  type auxtab;
  type eqextr = theory -> auxtab
    -> (string * typ) -> (thm list * typ) option;
  type defgen;
  type appgen = theory -> auxtab
    -> (string * typ) * term list -> CodegenThingol.transact
    -> CodegenThingol.iexpr * CodegenThingol.transact;

  val add_appconst: string * ((int * int) * appgen) -> theory -> theory;
  val add_appconst_i: xstring * ((int * int) * appgen) -> theory -> theory;
  val add_eqextr: string * eqextr -> theory -> theory;
  val add_defgen: string * defgen -> theory -> theory;
  val add_prim_class: xstring -> string list -> (string * string)
    -> theory -> theory;
  val add_prim_tyco: xstring -> string list -> (string * string)
    -> theory -> theory;
  val add_prim_const: xstring * string option -> string list -> (string * string)
    -> theory -> theory;
  val add_prim_i: string -> string list -> (string * Pretty.T)
    -> theory -> theory;
  val add_pretty_list: string -> string -> string * (int * string)
    -> theory -> theory;
  val add_alias: string * string -> theory -> theory;
  val set_is_datatype: (theory -> string -> bool) -> theory -> theory;
  val set_get_all_datatype_cons : (theory -> (string * string) list)
    -> theory -> theory;
  val set_int_tyco: string -> theory -> theory;

  val exprgen_type: theory -> auxtab
    -> typ -> CodegenThingol.transact -> CodegenThingol.itype * CodegenThingol.transact;
  val exprgen_term: theory -> auxtab
    -> term -> CodegenThingol.transact -> CodegenThingol.iexpr * CodegenThingol.transact;
  val appgen_default: appgen;

  val appgen_let: (int -> term -> term list * term)
    -> appgen;
  val appgen_split: (int -> term -> term list * term)
    -> appgen;
  val appgen_number_of: (term -> term) -> (term -> IntInf.int) -> string -> string
    -> appgen;
  val add_case_const: (theory -> string -> (string * int) list option) -> xstring
    -> theory -> theory;
  val add_case_const_i: (theory -> string -> (string * int) list option) -> string
    -> theory -> theory;
  val defgen_datatype: (theory -> string -> ((string * sort) list * string list) option)
    -> (theory -> string * string -> typ list option)
    -> defgen;

  val print_codegen_generated: theory -> unit;
  val rename_inconsistent: theory -> theory;
  val ensure_datatype_case_consts: (theory -> string list)
    -> (theory -> string -> (string * int) list option)
    -> theory -> theory;

  (*debugging purpose only*)
  structure InstNameMangler: NAME_MANGLER;
  structure ConstNameMangler: NAME_MANGLER;
  structure DatatypeconsNameMangler: NAME_MANGLER;
  structure CodegenData: THEORY_DATA;
  val mk_tabs: theory -> auxtab;
  val alias_get: theory -> string -> string;
  val idf_of_name: theory -> string -> string -> string;
  val idf_of_const: theory -> auxtab -> string * typ -> string;
end;

structure CodegenPackage : CODEGEN_PACKAGE =
struct

open CodegenThingol;
infix 8 `%%;
infixr 6 `->;
infixr 6 `-->;
infix 4 `$;
infix 4 `$$;
infixr 5 `|->;
infixr 5 `|-->;

(* auxiliary *)

fun devarify_type ty = (fst o Type.freeze_thaw_type) ty;
fun devarify_term t = (fst o Type.freeze_thaw) t;

val is_number = is_some o Int.fromString;

fun merge_opt _ (x1, NONE) = x1
  | merge_opt _ (NONE, x2) = x2
  | merge_opt eq (SOME x1, SOME x2) =
      if eq (x1, x2) then SOME x1 else error ("incompatible options during merge");


(* shallow name spaces *)

val nsp_class = "class";
val nsp_tyco = "tyco";
val nsp_const = "const";
val nsp_overl = "overl";
val nsp_dtcon = "dtcon";
val nsp_mem = "mem";
val nsp_inst = "inst";


(* code generator basics *)

structure InstNameMangler = NameManglerFun (
  type ctxt = theory;
  type src = string * (class * string);
  val ord = prod_ord string_ord (prod_ord string_ord string_ord);
  fun mk thy ((thyname, (cls, tyco)), i) =
    NameSpace.base cls ^ "_" ^ NameSpace.base tyco ^ implode (replicate i "'")
    |> NameSpace.append thyname;
  fun is_valid _ _ = true;
  fun maybe_unique _ _ = NONE;
  fun re_mangle _ dst = error ("no such instance: " ^ quote dst);
);

structure ConstNameMangler = NameManglerFun (
  type ctxt = theory;
  type src = string * (typ * typ);
  val ord = prod_ord string_ord (prod_ord Term.typ_ord Term.typ_ord);
  fun mk thy ((c, (ty_decl, ty)), i) =
    let
      fun mangle (Type (tyco, tys)) =
            NameSpace.base tyco :: Library.flat (List.mapPartial mangle tys) |> SOME
        | mangle _ =
            NONE
    in
      Vartab.empty
      |> Sign.typ_match thy (ty_decl, ty)
      |> map (snd o snd) o Vartab.dest
      |> List.mapPartial mangle
      |> Library.flat
      |> null ? K ["x"]
      |> cons c
      |> space_implode "_"
      |> curry (op ^ o swap) ((implode oo replicate) i "'")
    end;
  fun is_valid _ _ = true;
  fun maybe_unique _ _ = NONE;
  fun re_mangle _ dst = error ("no such constant: " ^ quote dst);
);

structure DatatypeconsNameMangler = NameManglerFun (
  type ctxt = theory;
  type src = string * string;
  val ord = prod_ord string_ord string_ord;
  fun mk thy ((co, dtco), i) =
        let
          fun basename 0 = NameSpace.base co
            | basename 1 = NameSpace.base dtco ^ "_" ^ NameSpace.base co
            | basename i = NameSpace.base dtco ^ "_" ^ NameSpace.base co ^ "_" ^ (implode oo replicate) (i-1) "'";
          fun strip_dtco name =
            case (rev o NameSpace.unpack) name
             of x1::x2::xs =>
                  if x2 = NameSpace.base dtco
                  then NameSpace.pack (x1::xs)
                  else name
              | _ => name;
        in
          NameSpace.append (NameSpace.drop_base dtco) (basename i)
          |> strip_dtco
        end;
  fun is_valid _ _ = true;
  fun maybe_unique _ _ = NONE;
  fun re_mangle _ dst = error ("no such datatype constructor: " ^ quote dst);
);

type auxtab = ((typ * thm) list Symtab.table * string Symtab.table)
  * (InstNameMangler.T * ((typ * typ list) Symtab.table * ConstNameMangler.T) * DatatypeconsNameMangler.T);
type eqextr = theory -> auxtab
  -> (string * typ) -> (thm list * typ) option;
type defgen = theory -> auxtab -> gen_defgen;
type appgen = theory -> auxtab -> (string * typ) * term list -> transact -> iexpr * transact;

val serializers = ref (
  Symtab.empty
  |> Symtab.update (
       #ml CodegenSerializer.serializers
       |> apsnd (fn seri => seri
            (nsp_dtcon, nsp_class, "")
            [[nsp_class, nsp_tyco], [nsp_const, nsp_overl, nsp_dtcon, nsp_mem, nsp_inst]]
          )
     )
  |> Symtab.update (
       #haskell CodegenSerializer.serializers
       |> apsnd (fn seri => seri
            nsp_dtcon
            [[nsp_class], [nsp_tyco], [nsp_const, nsp_overl, nsp_mem], [nsp_dtcon], [nsp_inst]]
          )
     )
);


(* theory data for code generator *)

type gens = {
  appconst: ((int * int) * (appgen * stamp)) Symtab.table,
  eqextrs: (string * (eqextr * stamp)) list,
  defgens: (string * (defgen * stamp)) list
};

fun map_gens f { appconst, eqextrs, defgens } =
  let
    val (appconst, eqextrs, defgens) =
      f (appconst, eqextrs, defgens)
  in { appconst = appconst, eqextrs = eqextrs, defgens = defgens } : gens end;

fun merge_gens
  ({ appconst = appconst1 , eqextrs = eqextrs1, defgens = defgens1 },
   { appconst = appconst2 , eqextrs = eqextrs2, defgens = defgens2 }) =
  { appconst = Symtab.merge
      (fn ((bounds1, (_, stamp1)), (bounds2, (_, stamp2))) => bounds1 = bounds2 andalso stamp1 = stamp2)
      (appconst1, appconst2),
    eqextrs = AList.merge (op =) (eq_snd (op =)) (eqextrs1, eqextrs2),
    defgens = AList.merge (op =) (eq_snd (op =)) (defgens1, defgens2)
  } : gens;

type logic_data = {
  is_datatype: ((theory -> string -> bool) * stamp) option,
  get_all_datatype_cons: ((theory -> (string * string) list) * stamp) option,
  alias: string Symtab.table * string Symtab.table
};

fun map_logic_data f { is_datatype, get_all_datatype_cons, alias } =
  let
    val ((is_datatype, get_all_datatype_cons), alias) =
      f ((is_datatype, get_all_datatype_cons), alias)
  in { is_datatype = is_datatype, get_all_datatype_cons = get_all_datatype_cons,
    alias = alias } : logic_data end;

fun merge_logic_data
  ({ is_datatype = is_datatype1, get_all_datatype_cons = get_all_datatype_cons1,
       alias = alias1 },
   { is_datatype = is_datatype2, get_all_datatype_cons = get_all_datatype_cons2,
       alias = alias2 }) =
  let
  in
    { is_datatype = merge_opt (eq_snd (op =)) (is_datatype1, is_datatype2),
      get_all_datatype_cons = merge_opt (eq_snd (op =)) (get_all_datatype_cons1, get_all_datatype_cons2),
      alias = (Symtab.merge (op =) (fst alias1, fst alias2),
               Symtab.merge (op =) (snd alias1, snd alias2)) } : logic_data
  end;

type target_data = {
  syntax_tyco: (itype CodegenSerializer.pretty_syntax * stamp) Symtab.table,
  syntax_const: (iexpr CodegenSerializer.pretty_syntax * stamp) Symtab.table
};

fun map_target_data f { syntax_tyco, syntax_const } =
  let
    val (syntax_tyco, syntax_const) =
      f (syntax_tyco, syntax_const)
  in { syntax_tyco = syntax_tyco, syntax_const = syntax_const } : target_data
  end;

fun merge_target_data
  ({ syntax_tyco = syntax_tyco1, syntax_const = syntax_const1 },
   { syntax_tyco = syntax_tyco2, syntax_const = syntax_const2 }) =
  { syntax_tyco = Symtab.merge (eq_snd (op =)) (syntax_tyco1, syntax_tyco2),
    syntax_const = Symtab.merge (eq_snd (op =)) (syntax_const1, syntax_const2) } : target_data;

structure CodegenData = TheoryDataFun
(struct
  val name = "Pure/codegen_package";
  type T = {
    modl: module,
    gens: gens,
    logic_data: logic_data,
    target_data: target_data Symtab.table
  };
  val empty = {
    modl = empty_module,
    gens = { appconst = Symtab.empty, eqextrs = [], defgens = [] } : gens,
    logic_data = { is_datatype = NONE, get_all_datatype_cons = NONE,
      alias = (Symtab.empty, Symtab.empty) } : logic_data,
    target_data =
      Symtab.empty
      |> Symtab.fold (fn (target, _) =>
           Symtab.update (target, { syntax_tyco = Symtab.empty, syntax_const = Symtab.empty })
         ) (! serializers)
  } : T;
  val copy = I;
  val extend = I;
  fun merge _ (
    { modl = modl1, gens = gens1,
      target_data = target_data1, logic_data = logic_data1 },
    { modl = modl2, gens = gens2,
      target_data = target_data2, logic_data = logic_data2 }
  ) = {
    modl = merge_module (modl1, modl2),
    gens = merge_gens (gens1, gens2),
    logic_data = merge_logic_data (logic_data1, logic_data2),
    target_data = Symtab.join (K (merge_target_data #> SOME))
      (target_data1, target_data2)
  };
  fun print _ _ = ();
end);

val _ = Context.add_setup CodegenData.init;

fun map_codegen_data f thy =
  case CodegenData.get thy
   of { modl, gens, target_data, logic_data } =>
      let val (modl, gens, target_data, logic_data) =
        f (modl, gens, target_data, logic_data)
      in CodegenData.put { modl = modl, gens = gens,
           target_data = target_data, logic_data = logic_data } thy end;

fun print_codegen_generated thy =
  let
    val module = (#modl o CodegenData.get) thy;
  in
    (writeln o Pretty.output o Pretty.chunks) [pretty_module module, pretty_deps module]
  end;

fun gen_add_appconst prep_const (raw_c, (bounds, ag)) thy =
  let
    val c = prep_const thy raw_c;
  in map_codegen_data
    (fn (modl, gens, target_data, logic_data) =>
       (modl,
        gens |> map_gens
          (fn (appconst, eqextrs, defgens) =>
            (appconst
             |> Symtab.update (c, (bounds, (ag, stamp ()))),
             eqextrs, defgens)), target_data, logic_data)) thy
  end;

val add_appconst = gen_add_appconst Sign.intern_const;
val add_appconst_i = gen_add_appconst (K I);

fun add_defgen (name, dg) =
  map_codegen_data
    (fn (modl, gens, target_data, logic_data) =>
       (modl,
        gens |> map_gens
          (fn (appconst, eqextrs, defgens) =>
            (appconst, eqextrs, defgens
             |> Output.update_warn (op =) ("overwriting existing definition definition generator " ^ name) (name, (dg, stamp ())))),
             target_data, logic_data));

fun get_defgens thy tabs =
  (map (apsnd (fn (dg, _) => dg thy tabs)) o #defgens o #gens o CodegenData.get) thy;

fun add_eqextr (name, eqx) =
  map_codegen_data
    (fn (modl, gens, target_data, logic_data) =>
       (modl,
        gens |> map_gens
          (fn (appconst, eqextrs, defgens) =>
            (appconst, eqextrs
             |> Output.update_warn (op =) ("overwriting existing equation extractor " ^ name) (name, (eqx, stamp ())),
             defgens)),
             target_data, logic_data));

fun get_eqextrs thy tabs =
  (map (fn (_, (eqx, _)) => eqx thy tabs) o #eqextrs o #gens o CodegenData.get) thy;

fun is_datatype thy =
  case (#is_datatype o #logic_data o CodegenData.get) thy
   of NONE => K false
    | SOME (f, _) => f thy;

fun get_all_datatype_cons thy =
  case (#get_all_datatype_cons o #logic_data o CodegenData.get) thy
   of NONE => []
    | SOME (f, _) => f thy;

fun add_alias (src, dst) =
  map_codegen_data
    (fn (modl, gens, target_data, logic_data) =>
       (modl, gens, target_data,
        logic_data |> map_logic_data
          (apsnd (fn (tab, tab_rev) =>
            (tab |> Symtab.update (src, dst),
             tab_rev |> Symtab.update (dst, src))))));


(* name handling *)

val alias_get = perhaps o Symtab.lookup o fst o #alias o #logic_data o CodegenData.get;
val alias_rev = perhaps o Symtab.lookup o snd o #alias o #logic_data o CodegenData.get;

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

fun idf_of_name thy shallow name =
  name
  |> alias_get thy
  |> add_nsp shallow;

fun name_of_idf thy shallow idf =
  idf
  |> dest_nsp shallow
  |> Option.map (alias_rev thy);

fun set_is_datatype f =
  map_codegen_data
    (fn (modl, gens, target_data, logic_data) =>
       (modl, gens, target_data,
        logic_data
        |> map_logic_data (apfst (fn (is_datatype, get_all_datatype_cons)
             => (SOME (f, stamp ()), get_all_datatype_cons)))));

fun set_get_all_datatype_cons f =
  map_codegen_data
    (fn (modl, gens, target_data, logic_data) =>
       (modl, gens, target_data,
        logic_data
        |> map_logic_data ((apfst (fn (is_datatype, get_all_datatype_cons)
             => (is_datatype, SOME (f, stamp ())))))));

fun set_int_tyco tyco thy =
  (serializers := (
    ! serializers
    |> Symtab.update (
         #ml CodegenSerializer.serializers
         |> apsnd (fn seri => seri
              (nsp_dtcon, nsp_class, idf_of_name thy nsp_tyco tyco)
              [[nsp_class, nsp_tyco], [nsp_const, nsp_overl, nsp_dtcon, nsp_mem, nsp_inst]]
            )
       )
    ); thy);


(* code generator instantiation *)

fun ensure_def_class thy tabs cls trns =
  let
    val cls' = idf_of_name thy nsp_class cls;
  in
    trns
    |> debug 4 (fn _ => "generating class " ^ quote cls)
    |> gen_ensure_def (get_defgens thy tabs) ("generating class " ^ quote cls) cls'
    |> pair cls'
  end;

fun ensure_def_inst thy (tabs as (_, (insttab, _, _))) (cls, tyco) trns =
  let
    val thyname = (the o AList.lookup (op =) (ClassPackage.the_instances thy cls)) tyco;
    val inst = idf_of_name thy nsp_inst (InstNameMangler.get thy insttab (thyname, (cls, tyco)));
  in
    trns
    |> debug 4 (fn _ => "generating instance " ^ quote cls ^ " / " ^ quote tyco)
    |> gen_ensure_def (get_defgens thy tabs) ("generating instance " ^ quote cls ^ " / " ^ quote tyco) inst
    |> pair inst
  end;

fun ensure_def_tyco thy tabs tyco trns =
  let
    val tyco' = idf_of_name thy nsp_tyco tyco;
  in
    trns
    |> debug 4 (fn _ => "generating type constructor " ^ quote tyco)
    |> gen_ensure_def (get_defgens thy tabs) ("generating type constructor " ^ quote tyco) tyco'
    |> pair tyco'
  end;

fun idf_of_const thy (tabs as ((_, clsmemtab), (_, (overltab1, overltab2), dtcontab))) (c, ty) =
  let
    fun get_overloaded (c, ty) =
      case Symtab.lookup overltab1 c
       of SOME (ty_decl, tys) =>
            (case find_first (curry (Sign.typ_instance thy) ty) tys
             of SOME ty' => ConstNameMangler.get thy overltab2
                  (idf_of_name thy nsp_overl c, (ty_decl, ty')) |> SOME
              | _ => NONE)
        | _ => NONE
    fun get_datatypecons (c, ty) =
      case (snd o strip_type) ty
       of Type (tyco, _) =>
            try (DatatypeconsNameMangler.get thy dtcontab) (c, tyco)
        | _ => NONE;
  in case get_datatypecons (c, ty)
   of SOME c' => idf_of_name thy nsp_dtcon c'
    | NONE => case get_overloaded (c, ty)
   of SOME idf => idf
    | NONE => case Symtab.lookup clsmemtab c
   of SOME _ => idf_of_name thy nsp_mem c
    | NONE => idf_of_name thy nsp_const c
  end;

fun recconst_of_idf thy (_, (_, (_, overltab2), _)) idf =
  case name_of_idf thy nsp_const idf
   of SOME c => SOME (c, Sign.the_const_type thy c)
    | NONE => (
        case dest_nsp nsp_overl idf
         of SOME _ =>
              idf
              |> ConstNameMangler.rev thy overltab2
              |> apfst (the o name_of_idf thy nsp_overl)
              |> apsnd snd
              |> SOME
          | NONE => NONE
      );

fun ensure_def_const thy (tabs as ((_, clsmemtab), (_, overltab, dtcontab))) (c, ty) trns =
  let
    val c' = idf_of_const thy tabs (c, ty);
  in
    trns
    |> debug 4 (fn _ => "generating constant " ^ quote c)
    |> gen_ensure_def (get_defgens thy tabs) ("generating constant " ^ quote c) c'
    |> pair c'
  end;

(* fun ensure_def_eq thy tabs (dtco, (eqpred, arity)) trns =
  let
    val name_dtco = (the ooo name_of_idf) thy nsp_tyco dtco;
    val idf_eqinst = idf_of_name thy nsp_eq_inst name_dtco;
    val idf_eqpred = idf_of_name thy nsp_eq_pred name_dtco;
    val inst_sortlookup = map (fn (v, _) => [ClassPackage.Lookup ([], (v, 0))]) arity;
    fun mk_eq_pred _ trns =
      trns
      |> succeed (eqpred)
    fun mk_eq_inst _ trns =
      trns
      |> gen_ensure_def [("eqpred", mk_eq_pred)] ("generating equality predicate for " ^ quote dtco) idf_eqpred
      |> succeed (Classinst ((class_eq, (dtco, arity)), ([], [(fun_eq, (idf_eqpred, inst_sortlookup))])));
  in
    trns
    |> gen_ensure_def [("eqinst", mk_eq_inst)] ("generating equality instance for " ^ quote dtco) idf_eqinst
  end; *)


(* expression generators *)

fun exprgen_tyvar_sort thy tabs (v, sort) trns =
  trns
  |> fold_map (ensure_def_class thy tabs) (ClassPackage.syntactic_sort_of thy sort)
  |-> (fn sort => pair (unprefix "'" v, sort));

fun exprgen_type thy tabs (TVar _) trns =
      error "TVar encountered during code generation"
  | exprgen_type thy tabs (TFree v_s) trns =
      trns
      |> exprgen_tyvar_sort thy tabs v_s
      |-> (fn v_s => pair (IVarT v_s))
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

fun mk_lookup thy tabs (ClassPackage.Instance (inst as (cls, tyco), ls)) trns =
      trns
      |> ensure_def_class thy tabs cls
      ||>> ensure_def_inst thy tabs inst
      ||>> (fold_map o fold_map) (mk_lookup thy tabs) ls
      |-> (fn ((cls, i), ls) => pair (ClassPackage.Instance ((cls, i), ls)))
  | mk_lookup thy tabs (ClassPackage.Lookup (clss, (v, i))) trns =
      trns
      |> fold_map (ensure_def_class thy tabs) clss
      |-> (fn clss => pair (ClassPackage.Lookup (clss, (v |> unprefix "'", i))));

fun appgen_default thy tabs ((c, ty), ts) trns =
  trns
  |> ensure_def_const thy tabs (c, ty)
  ||>> (fold_map o fold_map) (mk_lookup thy tabs)
    (ClassPackage.extract_sortlookup thy (c, ty))
  ||>> exprgen_type thy tabs ty
  ||>> fold_map (exprgen_term thy tabs) ts
  |-> (fn (((c, ls), ty), es) =>
         pair (Library.foldl IInst ((IConst (c, ty)), ls) `$$ es))
and appgen thy tabs ((f, ty), ts) trns =
  case Symtab.lookup ((#appconst o #gens o CodegenData.get) thy) f
   of SOME ((imin, imax), (ag, _)) =>
        if length ts < imin then
          let
            val d = imin - length ts;
            val vs = Term.invent_names (add_term_names (Const (f, ty), [])) "x" d;
            val tys = Library.take (d, ((fst o strip_type) ty));
          in
            trns
            |> debug 10 (fn _ => "eta-expanding")
            |> fold_map (exprgen_type thy tabs) tys
            ||>> ag thy tabs ((f, ty), ts @ map2 (curry Free) vs tys)
            |-> (fn (tys, e) => pair ((vs ~~ tys) `|--> e))
          end
        else if length ts > imax then
          trns
          |> debug 10 (fn _ => "splitting arguments (" ^ string_of_int imax ^ ", " ^ string_of_int (length ts) ^ ")")
          |> ag thy tabs ((f, ty), Library.take (imax, ts))
          ||>> fold_map (exprgen_term thy tabs) (Library.drop (imax, ts))
          |-> (fn es => pair (mk_apps es))
        else
          trns
          |> debug 10 (fn _ => "keeping arguments")
          |> ag thy tabs ((f, ty), ts)
    | NONE =>
        trns
        |> appgen_default thy tabs ((f, ty), ts)
and exprgen_term thy tabs (Const (f, ty)) trns =
      trns
      |> appgen thy tabs ((f, ty), [])
      |-> (fn e => pair e)
  | exprgen_term thy tabs (Var ((v, i), ty)) trns =
      trns
      |> exprgen_type thy tabs ty
      |-> (fn ty => pair (IVarE (if i = 0 then v else v ^ "_" ^ string_of_int i, ty)))
  | exprgen_term thy tabs (Free (v, ty)) trns =
      trns
      |> exprgen_type thy tabs ty
      |-> (fn ty => pair (IVarE (v, ty)))
  | exprgen_term thy tabs (Abs (v, ty, t)) trns =
      trns
      |> exprgen_type thy tabs ty
      ||>> exprgen_term thy tabs (subst_bound (Free (v, ty), t))
      |-> (fn (ty, e) => pair ((v, ty) `|-> e))
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
      end;


(* application generators *)

(* fun appgen_eq thy tabs (("op =", Type ("fun", [ty, _])), [t1, t2]) trns =
  trns
  |> invoke_eq (exprgen_type thy tabs) (ensure_def_eq thy tabs) ty
  |-> (fn false => error ("could not derive equality for " ^ Sign.string_of_typ thy ty)
        | true => fn trns => trns
  |> exprgen_term thy tabs t1
  ||>> exprgen_term thy tabs t2
  |-> (fn (e1, e2) => pair (Fun_eq `$ e1 `$ e2))); *)


(* function extractors *)

fun mk_fun thy tabs (c, ty) trns =
  case get_first (fn eqx => eqx (c, ty)) (get_eqextrs thy tabs)
   of SOME (eq_thms, ty) =>
        let
          val sortctxt = ClassPackage.extract_sortctxt thy ty;
          fun dest_eqthm eq_thm =
            let
              val ((t, args), rhs) = (apfst strip_comb o Logic.dest_equals o prop_of) eq_thm;
            in case t
             of Const (c', _) => if c' = c then (args, rhs)
                 else error ("illegal function equation for " ^ quote c
                   ^ ", actually defining " ^ quote c')
              | _ => error ("illegal function equation for " ^ quote c)
            end;
          fun mk_eq (args, rhs) trns =
            trns
            |> fold_map (exprgen_term thy tabs o devarify_term) args
            ||>> (exprgen_term thy tabs o devarify_term) rhs
            |-> (fn (args, rhs) => pair (map ipat_of_iexpr args, rhs))
        in
          trns
          |> fold_map (mk_eq o dest_eqthm) eq_thms
          ||>> exprgen_type thy tabs (devarify_type ty)
          ||>> fold_map (exprgen_tyvar_sort thy tabs) sortctxt
          |-> (fn ((eqs, ty), sortctxt) => (pair o SOME) (eqs, (sortctxt, ty)))
        end
    | NONE => (NONE, trns);

fun eqextr_defs thy ((deftab, _), _) (c, ty) =
  let
    fun eq_typ (ty1, ty2) = 
      Sign.typ_instance thy (ty1, ty2)
      andalso Sign.typ_instance thy (ty2, ty1)
  in
    Option.mapPartial (get_first (fn (ty', thm) => if eq_typ (ty, ty')
      then SOME ([thm], ty')
      else NONE
    )) (Symtab.lookup deftab c)
  end;


(* definition generators *)

fun defgen_clsdecl thy (tabs as (_, (insttab, _, _))) cls trns =
  case name_of_idf thy nsp_class cls
   of SOME cls =>
        let
          val cs = (snd o ClassPackage.the_consts_sign thy) cls;
          val sortctxts = map (ClassPackage.extract_sortctxt thy o snd) cs;
          val idfs = map (idf_of_name thy nsp_mem o fst) cs;
        in
          trns
          |> debug 5 (fn _ => "trying defgen class declaration for " ^ quote cls)
          |> fold_map (ensure_def_class thy tabs) (ClassPackage.the_superclasses thy cls)
          ||>> fold_map (exprgen_type thy tabs o snd) cs
          ||>> (fold_map o fold_map) (exprgen_tyvar_sort thy tabs) sortctxts
          |-> (fn ((supcls, memtypes), sortctxts) => succeed
            (Class ((supcls, ("a", idfs ~~ (sortctxts ~~ memtypes))), [])))
        end
    | _ =>
        trns
        |> fail ("no class definition found for " ^ quote cls);

fun defgen_funs thy tabs c trns =
  case recconst_of_idf thy tabs c
   of SOME (c, ty) =>
        trns
        |> mk_fun thy tabs (c, ty)
        |-> (fn (SOME funn) => succeed (Fun funn)
              | NONE => fail ("no defining equations found for " ^ quote c))
    | NONE =>
        trns
        |> fail ("not a constant: " ^ quote c);

fun defgen_datatypecons thy (tabs as (_, (_, _, dtcontab))) co trns =
  case Option.map (DatatypeconsNameMangler.rev thy dtcontab) (name_of_idf thy nsp_dtcon co)
   of SOME (co, dtco) =>
        trns
        |> debug 5 (fn _ => "trying defgen datatype constructor for " ^ quote co)
        |> ensure_def_tyco thy tabs dtco
        |-> (fn dtco => succeed Undef)
    | _ =>
        trns
        |> fail ("not a datatype constructor: " ^ quote co);

fun defgen_clsmem thy tabs m trns =
  case name_of_idf thy nsp_mem m
   of SOME m =>
        trns
        |> debug 5 (fn _ => "trying defgen class member for " ^ quote m)
        |> ensure_def_class thy tabs ((the o ClassPackage.lookup_const_class thy) m)
        |-> (fn cls => succeed Undef)
    | _ =>
        trns |> fail ("no class member found for " ^ quote m)

fun defgen_clsinst thy (tabs as (_, (insttab, _, _))) inst trns =
  case Option.map (InstNameMangler.rev thy insttab) (name_of_idf thy nsp_inst inst)
   of SOME (_, (cls, tyco)) =>
        let
          val (arity, memdefs) = ClassPackage.the_inst_sign thy (cls, tyco);
          fun gen_membr (m, ty) trns =
            trns
            |> mk_fun thy tabs (m, ty)
            |-> (fn SOME funn => pair (m, funn)
                  | NONE => error ("could not derive definition for member " ^ quote m));
        in
          trns
          |> debug 5 (fn _ => "trying defgen class instance for (" ^ quote cls ^ ", " ^ quote tyco ^ ")")
          |> ensure_def_class thy tabs cls
          ||>> ensure_def_tyco thy tabs tyco
          ||>> fold_map (exprgen_tyvar_sort thy tabs) arity
          ||>> fold_map gen_membr memdefs
          |-> (fn (((cls, tyco), arity), memdefs) =>
                 succeed (Classinst ((cls, (tyco, arity)), memdefs)))
        end
    | _ =>
        trns |> fail ("no class instance found for " ^ quote inst);


(* parametrized generators, for instantiation in HOL *)

fun appgen_let strip_abs thy tabs ((c, ty), [t2, t3]) trns =
  let
    fun dest_let (l as Const (c', _) $ t $ u) =
          if c = c' then
            case strip_abs 1 u
             of ([p], u') => apfst (cons (p, t)) (dest_let u')
              | _ => ([], l)
          else ([], t)
      | dest_let t = ([], t);
    fun mk_let (l, r) trns =
      trns
      |> exprgen_term thy tabs l
      ||>> exprgen_term thy tabs r
      |-> (fn (l, r) => pair (r, ipat_of_iexpr l));
    val (lets, body) = dest_let (Const (c, ty) $ t2 $ t3)
  in
    trns
    |> fold_map mk_let lets
    ||>> exprgen_term thy tabs body
    |-> (fn (lets, body) =>
         pair (Library.foldr (fn ((e, p), body) => ICase (e, [(p, body)])) (lets, body)))
  end

fun appgen_split strip_abs thy tabs (c, [t2]) trns =
  let
    val ([p], body) = strip_abs 1 (Const c $ t2)
  in
    trns
    |> exprgen_term thy tabs p
    ||>> exprgen_term thy tabs body
    |-> (fn (IVarE v, body) => pair (IAbs (v, body)))
  end;

fun appgen_number_of mk_int_to_nat bin_to_int tyco_int tyco_nat thy tabs ((_,
  Type (_, [_, ty as Type (tyco, [])])), [bin]) trns =
    if tyco = tyco_int then
      trns
      |> exprgen_type thy tabs ty
      |-> (fn ty => pair (CodegenThingol.IConst ((IntInf.toString o bin_to_int) bin, ty)))
    else if tyco = tyco_nat then
      trns
      |> exprgen_term thy tabs (mk_int_to_nat bin)
    else error ("invalid type constructor for numeral: " ^ quote tyco);

fun appgen_datatype_case cos thy tabs ((_, ty), ts) trns =
  let
    val (ts', t) = split_last ts;
    val (tys, dty) = (split_last o fst o strip_type) ty;
    fun gen_names i =
      variantlist (replicate i "x", foldr add_term_names
       (map (fst o fst o dest_Var) (foldr add_term_vars [] ts)) ts);
    fun cg_case_d (((cname, i), ty), t) trns =
      let
        val vs = gen_names i;
        val tys = Library.take (i, (fst o strip_type) ty);
        val frees = map2 (curry Free) vs tys;
        val t' = Envir.beta_norm (list_comb (t, frees));
      in
        trns
        |> exprgen_term thy tabs (list_comb (Const (cname, tys ---> dty), frees))
        ||>> exprgen_term thy tabs t'
        |-> (fn (ep, e) => pair (ipat_of_iexpr ep, e))
      end;
  in
    trns
    |> exprgen_term thy tabs t
    ||>> fold_map cg_case_d ((cos ~~ tys) ~~ ts')
    |-> (fn (t, ds) => pair (ICase (t, ds)))
  end;

fun gen_add_case_const prep_c get_case_const_data raw_c thy =
  let
    val c = prep_c thy raw_c;
    val (tys, dty) = (split_last o fst o strip_type o Sign.the_const_type thy) c;
    val cos = (the o get_case_const_data thy) c;
    val n_eta = length cos + 1;
  in
    thy
    |> add_appconst_i (c, ((n_eta, n_eta), appgen_datatype_case cos))
  end;

val add_case_const = gen_add_case_const Sign.intern_const;
val add_case_const_i = gen_add_case_const (K I);

fun defgen_datatype get_datatype get_datacons thy (tabs as (_, (_, _, dtcontab))) dtco trns =
  case name_of_idf thy nsp_tyco dtco
   of SOME dtco =>
        (case get_datatype thy dtco
         of SOME (vars, cos) =>
              let
                val cotys = map (the o get_datacons thy o rpair dtco) cos;
                val coidfs = map (fn co => (DatatypeconsNameMangler.get thy dtcontab (co, dtco)) |>
                  idf_of_name thy nsp_dtcon) cos;
              in
                trns
                |> debug 5 (fn _ => "trying defgen datatype for " ^ quote dtco)
                |> fold_map (exprgen_tyvar_sort thy tabs) vars
                ||>> (fold_map o fold_map) (exprgen_type thy tabs o devarify_type) cotys
                |-> (fn (sorts, tys) => succeed (Datatype
                     ((sorts, coidfs ~~ tys), [])))
              end
          | NONE =>
              trns
              |> fail ("no datatype found for " ^ quote dtco))
    | NONE =>
        trns
        |> fail ("not a type constructor: " ^ quote dtco)



(** theory interface **)

fun mk_tabs thy =
  let
    fun extract_defs thy =
      let
        fun dest tm =
          let
            val (lhs, rhs) = Logic.dest_equals (prop_of tm);
            val (t, args) = strip_comb lhs;
            val (c, ty) = dest_Const t
          in if forall is_Var args then SOME ((c, ty), tm) else NONE
          end handle TERM _ => NONE;
        fun prep_def def = (case Codegen.preprocess thy [def] of
          [def'] => def' | _ => error "mk_auxtab: bad preprocessor");
        fun add_def (name, _) =
          case (dest o prep_def o Thm.get_axiom thy) name
           of SOME ((c, ty), tm) =>
                Symtab.default (c, []) #> Symtab.map_entry c (cons (ty, tm))
            | NONE => I
      in
        Symtab.empty
        |> fold (Symtab.fold add_def o snd o #axioms o Theory.rep_theory)
             (thy :: Theory.ancestors_of thy)
      end;
    fun mk_insttab thy =
      InstNameMangler.empty
      |> Symtab.fold_map
          (fn (cls, (clsmems, clsinsts)) => fold_map
            (fn (tyco, thyname) => InstNameMangler.declare thy (thyname, (cls, tyco))) clsinsts)
                 (ClassPackage.get_classtab thy)
      |-> (fn _ => I);
    fun mk_overltabs thy deftab =
      (Symtab.empty, ConstNameMangler.empty)
      |> Symtab.fold
          (fn (c, [_]) => I
            | (c, tytab) =>
                (fn (overltab1, overltab2) => (
                  overltab1
                  |> Symtab.update_new (c, (Sign.the_const_constraint thy c, map fst tytab)),
                  overltab2
                  |> fold (fn (ty, _) => ConstNameMangler.declare thy
                       (idf_of_name thy nsp_overl c, (Sign.the_const_constraint thy c, ty)) #> snd) tytab
                ))) deftab;
    fun mk_dtcontab thy =
      DatatypeconsNameMangler.empty
      |> fold_map
          (fn (_, co_dtco) => DatatypeconsNameMangler.declare_multi thy co_dtco)
            (fold (fn (co, dtco) =>
              let
                val key = ((NameSpace.drop_base o NameSpace.drop_base) co, NameSpace.base co)
              in AList.default (op =) (key, []) #> AList.map_entry (op =) key (cons (co, dtco)) end
            ) (get_all_datatype_cons thy) [])
      |-> (fn _ => I);
    fun mk_clsmemtab thy =
      Symtab.empty
      |> Symtab.fold
          (fn (class, (clsmems, _)) => fold
            (fn clsmem => Symtab.update (clsmem, class)) clsmems)
              (ClassPackage.get_classtab thy);
    val deftab = extract_defs thy;
    val insttab = mk_insttab thy;
    val overltabs = mk_overltabs thy deftab;
    val dtcontab = mk_dtcontab thy;
    val clsmemtab = mk_clsmemtab thy;
  in ((deftab, clsmemtab), (insttab, overltabs, dtcontab)) end;

fun get_serializer target =
  case Symtab.lookup (!serializers) target
   of SOME seri => seri
    | NONE => error ("unknown code target language: " ^ quote target);

fun map_module f =
  map_codegen_data (fn (modl, gens, target_data, logic_data) =>
    (f modl, gens, target_data, logic_data));

fun expand_module gen thy =
  (#modl o CodegenData.get) thy
  |> start_transact (gen thy (mk_tabs thy))
  |-> (fn x:'a => fn modl => (x, map_module (K modl) thy));

fun rename_inconsistent thy =
  let
    fun get_inconsistent thyname =
      let
        val thy = theory thyname;
        fun own_tables get =
          (get thy)
          |> fold (Symtab.fold (Symtab.remove (K true)) o get) (Theory.parents_of thy)
          |> Symtab.keys;
        val names = own_tables (#2 o #types o Type.rep_tsig o Sign.tsig_of)
          @ own_tables (#2 o #declarations o Consts.dest o #consts o Sign.rep_sg);
        fun diff names =
          fold (fn name =>
            if is_prefix (op =) (NameSpace.unpack thyname) (NameSpace.unpack name)
            then I
            else cons (name, NameSpace.append thyname (NameSpace.base name))) names [];
      in diff names end;
    val inconsistent = map get_inconsistent (ThyInfo.names ()) |> Library.flat;
    fun add (src, dst) thy =
      if (is_some oo Symtab.lookup o fst o #alias o #logic_data o CodegenData.get) thy src
      then (warning ("code generator alias already defined for " ^ quote src ^ ", will not overwrite"); thy)
      else add_alias (src, dst) thy
  in fold add inconsistent thy end;

fun ensure_datatype_case_consts get_datatype_case_consts get_case_const_data thy =
  let
    fun ensure case_c thy =
      if
        Symtab.defined ((#appconst o #gens o CodegenData.get) thy) case_c
      then
        (warning ("case constant " ^ quote case_c ^ " already present in application table, will not overwrite"); thy)
      else
        add_case_const_i get_case_const_data case_c thy;
  in
    fold ensure (get_datatype_case_consts thy) thy
  end;



(** target languages **)

(* primitive definitions *)

fun read_typ thy =
  Sign.read_typ (thy, K NONE);

fun read_const thy (raw_c, raw_ty) =
  let
    val c = Sign.intern_const thy raw_c;
    val _ = if Sign.declared_const thy c
      then ()
      else error ("no such constant: " ^ quote c);
    val ty = case raw_ty
     of NONE => Sign.the_const_constraint thy c
      | SOME raw_ty => read_typ thy raw_ty;
  in (c, ty) end;

fun read_quote reader gen raw thy =
  expand_module
    (fn thy => fn tabs => gen thy tabs (reader thy raw))
    thy;

fun gen_add_prim prep_name prep_primdef raw_name deps (target, raw_primdef) thy =
  let
    val _ = if Symtab.defined ((#target_data o CodegenData.get) thy) target
      then () else error ("unknown target language: " ^ quote target);
    val tabs = mk_tabs thy;
    val name = prep_name thy tabs raw_name;
    val primdef = prep_primdef raw_primdef;
  in
    thy
    |> map_module (CodegenThingol.add_prim name deps (target, primdef))
  end;

val add_prim_i = gen_add_prim ((K o K) I) I;
val add_prim_class = gen_add_prim
  (fn thy => K (idf_of_name thy nsp_class o Sign.intern_class thy))
  (Pretty.str o CodegenSerializer.parse_targetdef I);
val add_prim_tyco = gen_add_prim
  (fn thy => K (idf_of_name thy nsp_tyco o Sign.intern_type thy))
  (Pretty.str o CodegenSerializer.parse_targetdef I);
val add_prim_const = gen_add_prim
  (fn thy => fn tabs => idf_of_const thy tabs o read_const thy)
  (Pretty.str o CodegenSerializer.parse_targetdef I);

val ensure_prim = (map_module oo CodegenThingol.ensure_prim);


(* syntax *)

val parse_syntax_tyco =
  let
    fun mk reader raw_tyco target thy =
      let
        val _ = get_serializer target;
        fun check_tyco tyco =
          if Sign.declared_tyname thy tyco
          then tyco
          else error ("no such type constructor: " ^ quote tyco);
        fun prep_tyco thy tyco =
          tyco
          |> Sign.intern_type thy
          |> check_tyco
          |> idf_of_name thy nsp_tyco;
        val tyco = prep_tyco thy raw_tyco;
      in
        thy
        |> ensure_prim tyco target
        |> reader
        |-> (fn pretty => map_codegen_data
          (fn (modl, gens, target_data, logic_data) =>
             (modl, gens,
              target_data |> Symtab.map_entry target
                (map_target_data
                  (fn (syntax_tyco, syntax_const) =>
                   (syntax_tyco |> Symtab.update
                      (tyco, (pretty, stamp ())),
                    syntax_const))),
              logic_data)))
      end;
  in
    CodegenSerializer.parse_syntax (read_quote read_typ exprgen_type)
    #-> (fn reader => pair (mk reader))
  end;

fun add_pretty_syntax_const c target pretty =
  map_codegen_data
    (fn (modl, gens, target_data, logic_data) =>
       (modl, gens,
        target_data |> Symtab.map_entry target
          (map_target_data
            (fn (syntax_tyco, syntax_const) =>
             (syntax_tyco,
              syntax_const
              |> Symtab.update
                 (c, (pretty, stamp ()))))),
        logic_data));

val parse_syntax_const =
  let
    fun mk reader raw_const target thy =
      let
        val _ = get_serializer target;
        val tabs = mk_tabs thy;
        val c = idf_of_const thy tabs (read_const thy raw_const);
      in
        thy
        |> ensure_prim c target
        |> reader
        |-> (fn pretty => add_pretty_syntax_const c target pretty)
      end;
  in
    CodegenSerializer.parse_syntax (read_quote Sign.read_term exprgen_term)
    #-> (fn reader => pair (mk reader))
  end;

fun add_pretty_list raw_nil raw_cons (target, seri) thy =
  let
    val _ = get_serializer target;
    val tabs = mk_tabs thy;
    fun mk_const raw_name =
      let
        val name = Sign.intern_const thy raw_name;
      in idf_of_const thy tabs (name, Sign.the_const_type thy name) end;
    val nil' = mk_const raw_nil;
    val cons' = mk_const raw_cons;
    val pr' = CodegenSerializer.pretty_list nil' cons' seri;
  in
    thy
    |> ensure_prim cons' target
    |> add_pretty_syntax_const cons' target pr'
  end;



(** toplevel interface **)

local

fun generate_code (SOME raw_consts) thy =
      let
        val consts = map (read_const thy) raw_consts;
        fun generate thy tabs = fold_map (ensure_def_const thy tabs) consts
      in
        thy
        |> expand_module generate
        |-> (fn cs => pair (SOME cs))
      end
  | generate_code NONE thy =
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
        in (seri (
          (Option.map fst oo Symtab.lookup o #syntax_tyco) target_data,
          (Option.map fst oo Symtab.lookup o #syntax_const) target_data
        ) cs module : unit; thy) end;
  in
    thy
    |> generate_code raw_consts
    |-> (fn cs => serialize cs)
  end;

structure P = OuterParse
and K = OuterKeyword

in

val (generateK, serializeK,
     primclassK, primtycoK, primconstK,
     syntax_tycoK, syntax_constK, aliasK) =
  ("code_generate", "code_serialize",
   "code_primclass", "code_primtyco", "code_primconst",
   "code_syntax_tyco", "code_syntax_const", "code_alias");
val dependingK =
  ("depending_on");

val generateP =
  OuterSyntax.command generateK "generate executable code for constants" K.thy_decl (
    Scan.repeat1 (P.name -- Scan.option (P.$$$ "::" |-- P.typ))
    >> (fn raw_consts =>
          Toplevel.theory (generate_code (SOME raw_consts) #> snd))
  );

val serializeP =
  OuterSyntax.command serializeK "serialize executable code for constants" K.thy_decl (
    P.name
    -- Scan.option (Scan.repeat1 (P.name -- Scan.option (P.$$$ "::" |-- P.typ)))
    #-> (fn (target, raw_consts) =>
          P.$$$ "("
          |-- get_serializer target
          --| P.$$$ ")"
          >> (fn seri =>
            Toplevel.theory (serialize_code target seri raw_consts)
          ))
  );

val aliasP =
  OuterSyntax.command aliasK "declare an alias for a theory identifier" K.thy_decl (
    Scan.repeat1 (P.name -- P.name)
      >> (Toplevel.theory oo fold) add_alias
  );

val primclassP =
  OuterSyntax.command primclassK "define target-lanugage specific class" K.thy_decl (
    P.xname
    -- Scan.optional (P.$$$ dependingK |--
         P.$$$ "(" |-- P.list1 P.name --| P.$$$ ")") []
    -- Scan.repeat1 (P.name -- P.text)
      >> (fn ((raw_class, depends), primdefs) =>
            (Toplevel.theory oo fold) (add_prim_class raw_class depends) primdefs)
  );

val primtycoP =
  OuterSyntax.command primtycoK "define target-lanugage specific type constructor" K.thy_decl (
    P.xname
    -- Scan.optional (P.$$$ dependingK |--
         P.$$$ "(" |-- P.list1 P.name --| P.$$$ ")") []
    -- Scan.repeat1 (P.name -- P.text)
      >> (fn ((raw_tyco, depends), primdefs) =>
            (Toplevel.theory oo fold) (add_prim_tyco raw_tyco depends) primdefs)
  );

val primconstP =
  OuterSyntax.command primconstK "define target-lanugage specific constant" K.thy_decl (
    (P.xname -- Scan.option (P.$$$ "::" |-- P.typ))
    -- Scan.optional (P.$$$ dependingK |--
         P.$$$ "(" |-- P.list1 P.name --| P.$$$ ")") []
    -- Scan.repeat1 (P.name -- P.text)
      >> (fn ((raw_const, depends), primdefs) =>
            (Toplevel.theory oo fold) (add_prim_const raw_const depends) primdefs)
  );

val syntax_tycoP =
  OuterSyntax.command syntax_tycoK "define code syntax for type constructor" K.thy_decl (
    Scan.repeat1 (
      P.xname
      -- Scan.repeat1 (
           P.name -- parse_syntax_tyco
         )
    )
    >> (Toplevel.theory oo fold) (fn (raw_tyco, syns) =>
          fold (fn (target, modifier) => modifier raw_tyco target) syns)
  );

val syntax_constP =
  OuterSyntax.command syntax_constK "define code syntax for constant" K.thy_decl (
    Scan.repeat1 (
      (P.xname -- Scan.option (P.$$$ "::" |-- P.typ))
      -- Scan.repeat1 (
           P.name -- parse_syntax_const
         )
    )
    >> (Toplevel.theory oo fold) (fn (raw_c, syns) =>
          fold (fn (target, modifier) => modifier raw_c target) syns)
  );

val _ = OuterSyntax.add_parsers [generateP, serializeP, aliasP,
  primclassP, primtycoP, primconstP, syntax_tycoP, syntax_constP];
val _ = OuterSyntax.add_keywords [dependingK];



(** theory setup **)

val _ = Context.add_setup (
  add_eqextr ("defs", eqextr_defs)
  #> add_defgen ("funs", defgen_funs)
  #> add_defgen ("clsdecl", defgen_clsdecl)
  #> add_defgen ("clsmem", defgen_clsmem)
  #> add_defgen ("clsinst", defgen_clsinst)
  #> add_defgen ("datatypecons", defgen_datatypecons)
(*   add_appconst_i ("op =", ((2, 2), appgen_eq))  *)
);

end; (* local *)

end; (* struct *)

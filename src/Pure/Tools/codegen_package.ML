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
    -> string * typ -> (thm list * typ) option;
  type eqextr_default = theory -> auxtab
    -> string * typ -> ((thm list * term option) * typ) option;
  type appgen = theory -> auxtab
    -> (string * typ) * term list -> CodegenThingol.transact
    -> CodegenThingol.iexpr * CodegenThingol.transact;

  val add_appconst: string * ((int * int) * appgen) -> theory -> theory;
  val add_appconst_i: xstring * ((int * int) * appgen) -> theory -> theory;
  val add_eqextr: string * eqextr -> theory -> theory;
  val add_eqextr_default: string * eqextr_default -> theory -> theory;
  val add_prim_class: xstring -> (string * string)
    -> theory -> theory;
  val add_prim_tyco: xstring -> (string * string)
    -> theory -> theory;
  val add_prim_const: xstring -> (string * string)
    -> theory -> theory;
  val add_prim_i: string -> (string * CodegenThingol.prim list)
    -> theory -> theory;
  val add_pretty_list: string -> string -> string * (int * string)
    -> theory -> theory;
  val add_alias: string * string -> theory -> theory;
  val set_get_all_datatype_cons : (theory -> (string * string) list)
    -> theory -> theory;
  val set_get_datatype: (theory -> string -> ((string * sort) list * (string * typ list) list) option)
    -> theory -> theory;
  val set_int_tyco: string -> theory -> theory;

  val codegen_term: term -> theory -> CodegenThingol.iexpr * theory;
  val is_dtcon: string -> bool;
  val consts_of_idfs: theory -> string list -> (string * typ) list;
  val idfs_of_consts: theory -> (string * typ) list -> string list;
  val get_root_module: theory -> CodegenThingol.module;
  val get_ml_fun_datatype: theory -> (string -> string)
    -> ((string * CodegenThingol.funn) list -> Pretty.T)
        * ((string * CodegenThingol.datatyp) list -> Pretty.T);

  val appgen_default: appgen;
  val appgen_let: (int -> term -> term list * term)
    -> appgen;
  val appgen_split: (int -> term -> term list * term)
    -> appgen;
  val appgen_number_of: (term -> term) -> (theory -> term -> IntInf.int) -> string -> string
    -> appgen;
  val appgen_wfrec: appgen;
  val eqextr_eq: (theory -> string -> thm list) -> term
    -> eqextr_default;
  val add_case_const: (theory -> string -> (string * int) list option) -> xstring
    -> theory -> theory;
  val add_case_const_i: (theory -> string -> (string * int) list option) -> string
    -> theory -> theory;

  val print_code: theory -> unit;
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

(* shallow name spaces *)

val alias_ref = ref (fn thy : theory => fn s : string => s, fn thy : theory => fn s : string => s);
fun alias_get name = (fst o !) alias_ref name;
fun alias_rev name = (snd o !) alias_ref name;

val nsp_module = ""; (* a dummy by convention *)
val nsp_class = "class";
val nsp_tyco = "tyco";
val nsp_const = "const";
val nsp_overl = "overl";
val nsp_dtcon = "dtcon";
val nsp_mem = "mem";
val nsp_inst = "inst";
val nsp_instmem = "instmem";

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


(* code generator basics *)

type deftab = (typ * (thm * string)) list Symtab.table;

fun eq_typ thy (ty1, ty2) =
  Sign.typ_instance thy (ty1, ty2)
    andalso Sign.typ_instance thy (ty2, ty1);

fun is_overloaded thy c = case Defs.specifications_of (Theory.defs_of thy) c
 of [] => true
  | [(ty, _)] => not (eq_typ thy (ty, Sign.the_const_type thy c))
  | _ => true;

structure InstNameMangler = NameManglerFun (
  type ctxt = theory;
  type src = string * (class * string);
  val ord = prod_ord string_ord (prod_ord string_ord string_ord);
  fun mk thy ((thyname, (cls, tyco)), i) =
    (NameSpace.base o alias_get thy) cls ^ "_" ^ (NameSpace.base o alias_get thy) tyco ^ implode (replicate i "'")
    |> NameSpace.append thyname;
  fun is_valid _ _ = true;
  fun maybe_unique _ _ = NONE;
  fun re_mangle _ dst = error ("no such instance: " ^ quote dst);
);

structure ConstNameMangler = NameManglerFun (
  type ctxt = theory;
  type src = string * typ;
  val ord = prod_ord string_ord Term.typ_ord;
  fun mk thy ((c, ty), i) =
    let
      val c' = idf_of_name thy nsp_overl c;
      val prefix = 
        case (AList.lookup (eq_typ thy)
            (Defs.specifications_of (Theory.defs_of thy) c)) ty
         of SOME thyname => NameSpace.append thyname nsp_overl
          | NONE => if c = "op ="
              then
                NameSpace.append
                  (((fn s => Codegen.thyname_of_type s thy) o fst o dest_Type o hd o fst o strip_type) ty)
                  nsp_overl
              else
                NameSpace.drop_base c';
      val c'' = NameSpace.append prefix (NameSpace.base c');
      fun mangle (Type (tyco, tys)) =
            (NameSpace.base o alias_get thy) tyco :: Library.flat (List.mapPartial mangle tys) |> SOME
        | mangle _ =
            NONE
    in
      Vartab.empty
      |> Sign.typ_match thy (Sign.the_const_type thy c, ty)
      |> map (snd o snd) o Vartab.dest
      |> List.mapPartial mangle
      |> Library.flat
      |> null ? K ["x"]
      |> cons c''
      |> space_implode "_"
      |> curry (op ^ o swap) ((implode oo replicate) i "'")
    end;
  fun is_valid _ _ = true;
  fun maybe_unique thy (c, ty) =
    if is_overloaded thy c
      then NONE
      else (SOME o idf_of_name thy nsp_const) c;
  fun re_mangle thy idf =
   case name_of_idf thy nsp_const idf
    of NONE => error ("no such constant: " ^ quote idf)
     | SOME c => (c, Sign.the_const_type thy c);
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

type auxtab = deftab
  * (InstNameMangler.T * (typ list Symtab.table * ConstNameMangler.T)
  * DatatypeconsNameMangler.T);
type eqextr = theory -> auxtab
  -> string * typ -> (thm list * typ) option;
type eqextr_default = theory -> auxtab
  -> string * typ -> ((thm list * term option) * typ) option;
type appgen = theory -> auxtab
  -> (string * typ) * term list -> transact -> iexpr * transact;

val serializers = ref (
  Symtab.empty
  |> Symtab.update (
       #ml CodegenSerializer.serializers
       |> apsnd (fn seri => seri
            (nsp_dtcon, nsp_class, K false)
            [[nsp_module], [nsp_class, nsp_tyco], [nsp_const, nsp_overl, nsp_dtcon, nsp_class, nsp_mem, nsp_inst, nsp_instmem]]
          )
     )
  |> Symtab.update (
       #haskell CodegenSerializer.serializers
       |> apsnd (fn seri => seri
            [nsp_module, nsp_class, nsp_tyco, nsp_dtcon]
            [[nsp_module], [nsp_class], [nsp_tyco], [nsp_const, nsp_overl, nsp_mem], [nsp_dtcon], [nsp_inst], [nsp_instmem]]
          )
     )
);


(* theory data for code generator *)

fun merge_opt _ (x1, NONE) = x1
  | merge_opt _ (NONE, x2) = x2
  | merge_opt eq (SOME x1, SOME x2) =
      if eq (x1, x2) then SOME x1 else error ("incompatible options during merge");

type gens = {
  appconst: ((int * int) * (appgen * stamp)) Symtab.table,
  eqextrs: (string * (eqextr_default * stamp)) list
};

fun map_gens f { appconst, eqextrs } =
  let
    val (appconst, eqextrs) =
      f (appconst, eqextrs)
  in { appconst = appconst, eqextrs = eqextrs } : gens end;

fun merge_gens
  ({ appconst = appconst1 , eqextrs = eqextrs1 },
   { appconst = appconst2 , eqextrs = eqextrs2 }) =
  { appconst = Symtab.merge
      (fn ((bounds1, (_, stamp1)), (bounds2, (_, stamp2))) => bounds1 = bounds2
         andalso stamp1 = stamp2)
      (appconst1, appconst2),
    eqextrs = AList.merge (op =) (eq_snd (op =)) (eqextrs1, eqextrs2)
  } : gens;

type logic_data = {
  get_all_datatype_cons: ((theory -> (string * string) list) * stamp) option,
  get_datatype: ((theory -> string -> ((string * sort) list * (string * typ list) list) option) * stamp) option,
  alias: string Symtab.table * string Symtab.table
};

fun map_logic_data f { get_all_datatype_cons, get_datatype, alias } =
  let
    val ((get_all_datatype_cons, get_datatype), alias) =
      f ((get_all_datatype_cons, get_datatype), alias)
  in { get_all_datatype_cons = get_all_datatype_cons,
    get_datatype = get_datatype, alias = alias } : logic_data end;

fun merge_logic_data
  ({ get_all_datatype_cons = get_all_datatype_cons1,
       get_datatype = get_datatype1, alias = alias1 },
   { get_all_datatype_cons = get_all_datatype_cons2,
       get_datatype = get_datatype2, alias = alias2 }) =
  let
  in
    { get_all_datatype_cons = merge_opt (eq_snd (op =))
        (get_all_datatype_cons1, get_all_datatype_cons2),
      get_datatype = merge_opt (eq_snd (op =))
        (get_datatype1, get_datatype2),
      alias = (Symtab.merge (op =) (fst alias1, fst alias2),
               Symtab.merge (op =) (snd alias1, snd alias2)) } : logic_data
  end;

type target_data = {
  syntax_class: string Symtab.table,
  syntax_tyco: (itype CodegenSerializer.pretty_syntax * stamp) Symtab.table,
  syntax_const: (iexpr CodegenSerializer.pretty_syntax * stamp) Symtab.table
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
    gens: gens,
    logic_data: logic_data,
    target_data: target_data Symtab.table
  };
  val empty = {
    modl = empty_module,
    gens = { appconst = Symtab.empty, eqextrs = [] } : gens,
    logic_data = { get_all_datatype_cons = NONE,
      get_datatype = NONE,
      alias = (Symtab.empty, Symtab.empty) } : logic_data,
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
    { modl = modl1, gens = gens1,
      target_data = target_data1, logic_data = logic_data1 },
    { modl = modl2, gens = gens2,
      target_data = target_data2, logic_data = logic_data2 }
  ) = {
    modl = merge_module (modl1, modl2),
    gens = merge_gens (gens1, gens2),
    logic_data = merge_logic_data (logic_data1, logic_data2),
    target_data = Symtab.join (K merge_target_data) (target_data1, target_data2)
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

fun print_code thy =
  let
    val module = (#modl o CodegenData.get) thy;
  in
    (Pretty.writeln o Pretty.chunks) [pretty_module module, pretty_deps module]
  end;


(* advanced name handling *)

fun add_alias (src, dst) =
  map_codegen_data
    (fn (modl, gens, target_data, logic_data) =>
       (modl, gens, target_data,
        logic_data |> map_logic_data
          (apsnd (fn (tab, tab_rev) =>
            (tab |> Symtab.update (src, dst),
             tab_rev |> Symtab.update (dst, src))))));

val _ = alias_ref := (perhaps o Symtab.lookup o fst o #alias o #logic_data o CodegenData.get,
  perhaps o Symtab.lookup o snd o #alias o #logic_data o CodegenData.get);

fun idf_of_const thy (tabs as (deftab, (_, (overltab1, overltab2), dtcontab)))
      (c, ty) =
  let
    fun get_overloaded (c, ty) =
      (case Symtab.lookup overltab1 c
       of SOME tys =>
            (case find_first (curry (Sign.typ_instance thy) ty) tys
             of SOME ty' => ConstNameMangler.get thy overltab2
                  (c, ty') |> SOME
              | _ => NONE)
        | _ => NONE)
    fun get_datatypecons (c, ty) =
      case (snd o strip_type) ty
       of Type (tyco, _) =>
            try (DatatypeconsNameMangler.get thy dtcontab) (c, tyco)
        | _ => NONE;
  in case get_datatypecons (c, ty)
   of SOME c' => idf_of_name thy nsp_dtcon c'
    | NONE => case get_overloaded (c, ty)
   of SOME idf => idf
    | NONE => case ClassPackage.lookup_const_class thy c
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
              |> SOME
          | NONE => NONE
      );

fun const_of_idf thy (tabs as (_, (_, _, dtcontab))) idf =
  case recconst_of_idf thy tabs idf
   of SOME c_ty => SOME c_ty
    | NONE => case dest_nsp nsp_mem idf
       of SOME c => SOME (c, Sign.the_const_constraint thy c)
        | NONE => case name_of_idf thy nsp_dtcon idf
           of SOME idf' => let
                val c = (fst o DatatypeconsNameMangler.rev thy dtcontab) idf'
              in SOME (c, Sign.the_const_type thy c) end
            | NONE => NONE;

(* further theory data accessors *)

fun gen_add_appconst prep_const (raw_c, (bounds, ag)) thy =
  let
    val c = prep_const thy raw_c;
  in map_codegen_data
    (fn (modl, gens, target_data, logic_data) =>
       (modl,
        gens |> map_gens
          (fn (appconst, eqextrs) =>
            (appconst
             |> Symtab.update (c, (bounds, (ag, stamp ()))),
             eqextrs)), target_data, logic_data)) thy
  end;

val add_appconst = gen_add_appconst Sign.intern_const;
val add_appconst_i = gen_add_appconst (K I);

fun add_eqextr (name, eqx) =
  map_codegen_data
    (fn (modl, gens, target_data, logic_data) =>
       (modl,
        gens |> map_gens
          (fn (appconst, eqextrs) =>
            (appconst, eqextrs
             |> Output.update_warn (op =) ("overwriting existing equation extractor " ^ name)
                 (name, ((Option.map o apfst o rpair) NONE ooo eqx , stamp ())))),
             target_data, logic_data));

fun add_eqextr_default (name, eqx) =
  map_codegen_data
    (fn (modl, gens, target_data, logic_data) =>
       (modl,
        gens |> map_gens
          (fn (appconst, eqextrs) =>
            (appconst, eqextrs
    |> Output.update_warn (op =) ("overwriting existing equation extractor " ^ name)
                 (name, (eqx, stamp ())))),
             target_data, logic_data));

fun get_eqextrs thy tabs =
  (map (fn (name, (eqx, _)) => (name, eqx thy tabs)) o #eqextrs o #gens o CodegenData.get) thy;

fun set_get_all_datatype_cons f =
  map_codegen_data
    (fn (modl, gens, target_data, logic_data) =>
       (modl, gens, target_data,
        logic_data
        |> map_logic_data ((apfst (fn (get_all_datatype_cons, get_datatype)
             => (SOME (f, stamp ()), get_datatype))))));

fun get_all_datatype_cons thy =
  case (#get_all_datatype_cons o #logic_data o CodegenData.get) thy
   of NONE => []
    | SOME (f, _) => f thy;

fun set_get_datatype f =
  map_codegen_data
    (fn (modl, gens, target_data, logic_data) =>
       (modl, gens, target_data,
        logic_data
        |> map_logic_data ((apfst (fn (get_all_datatype_cons, get_datatype)
             => (get_all_datatype_cons, SOME (f, stamp ())))))));

fun get_datatype thy =
  case (#get_datatype o #logic_data o CodegenData.get) thy
   of NONE => K NONE
    | SOME (f, _) => f thy;

fun set_int_tyco tyco thy =
  (serializers := (
    ! serializers
    |> Symtab.update (
         #ml CodegenSerializer.serializers
         |> apsnd (fn seri => seri
            (nsp_dtcon, nsp_class, fn tyco' => tyco' = idf_of_name thy nsp_tyco tyco)
              [[nsp_module], [nsp_class, nsp_tyco], [nsp_const, nsp_overl, nsp_dtcon, nsp_mem, nsp_inst, nsp_instmem]]
            )
       )
    ); thy);


(* sophisticated devarification *)

fun devarify_typs tys =
  let
    fun add_rename (vi as (v, _), sorts) used =
      let
        val v' = "'" ^ variant used (unprefix "'" v)
      in (map (fn sort => (((vi, sort), TFree (v', sort)), (v', TVar (vi, sort)))) sorts, v' :: used) end;
    fun typ_names (Type (tyco, tys)) (vars, names) =
          (vars, names |> insert (op =) (NameSpace.base tyco))
          |> fold typ_names tys
      | typ_names (TFree (v, _)) (vars, names) =
          (vars, names |> insert (op =) (unprefix "'" v))
      | typ_names (TVar (vi, sort)) (vars, names) =
          (vars
           |> AList.default (op =) (vi, [])
           |> AList.map_entry (op =) vi (cons sort),
           names);
    val (vars, used) = fold typ_names tys ([], []);
    val (renames, reverse) = fold_map add_rename vars used |> fst |> Library.flat |> split_list;
  in
    (reverse, map (Term.instantiateT renames) tys)
  end;

fun burrow_typs_yield f ts =
  let
    val typtab =
      fold (fold_types (fn ty => Typtab.update (ty, dummyT)))
        ts Typtab.empty;
    val typs = Typtab.keys typtab;
    val (x, typs') = f typs;
    val typtab' = fold2 (Typtab.update oo pair) typs typs' typtab;
  in
    (x, (map o map_term_types) (the o Typtab.lookup typtab') ts)
  end;

fun devarify_terms ts =
  let
    fun add_rename (vi as (v, _), tys) used =
      let
        val v' = variant used v
      in (map (fn ty => (((vi, ty), Free (v', ty)), (v', Var (vi, ty)))) tys, v' :: used) end;
    fun term_names (Const (c, _)) (vars, names) =
          (vars, names |> insert (op =) (NameSpace.base c))
      | term_names (Free (v, _)) (vars, names) =
          (vars, names |> insert (op =) v)
      | term_names (Var (vi, ty)) (vars, names) =
          (vars
           |> AList.default (op =) (vi, [])
           |> AList.map_entry (op =) vi (cons ty),
           names)
      | term_names (Bound _) vars_names =
          vars_names
      | term_names (Abs (v, _, _)) (vars, names) =
          (vars, names |> insert (op =) v)
      | term_names (t1 $ t2) vars_names =
          vars_names |> term_names t1 |> term_names t2
    val (vars, used) = fold term_names ts ([], []);
    val (renames, reverse) = fold_map add_rename vars used |> fst |> Library.flat |> split_list;
  in
    (reverse, map (Term.instantiate ([], renames)) ts)
  end;

fun devarify_term_typs ts =
  ts
  |> devarify_terms
  |-> (fn reverse => burrow_typs_yield devarify_typs
  #-> (fn reverseT => pair (reverseT, reverse)));

(* definition and expression generators *)

fun ensure_def_class thy tabs cls trns =
  let
    fun defgen_class thy (tabs as (_, (insttab, _, _))) cls trns =
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
              ||>> (exprsgen_type thy tabs o map snd) cs
              ||>> (fold_map o fold_map) (exprgen_tyvar_sort thy tabs) sortctxts
              |-> (fn ((supcls, memtypes), sortctxts) => succeed
                (Class (supcls, ("a", idfs ~~ (sortctxts ~~ memtypes)))))
            end
        | _ =>
            trns
            |> fail ("no class definition found for " ^ quote cls);
    val cls' = idf_of_name thy nsp_class cls;
  in
    trns
    |> debug 4 (fn _ => "generating class " ^ quote cls)
    |> ensure_def [("class", defgen_class thy tabs)] ("generating class " ^ quote cls) cls'
    |> pair cls'
  end
and ensure_def_tyco thy tabs tyco trns =
  let
    fun defgen_datatype thy (tabs as (_, (_, _, dtcontab))) dtco trns =
      case name_of_idf thy nsp_tyco dtco
       of SOME dtco =>
        (case get_datatype thy dtco
             of SOME (vars, cos) =>
                  let
                    val cos' = map (fn (co, tys) => (DatatypeconsNameMangler.get thy dtcontab (co, dtco) |>
                      idf_of_name thy nsp_dtcon, tys)) cos;
                  in
                    trns
                    |> debug 5 (fn _ => "trying defgen datatype for " ^ quote dtco)
                    |> fold_map (exprgen_tyvar_sort thy tabs) vars
                    ||>> fold_map (fn (c, ty) => exprsgen_type thy tabs ty #-> (fn ty' => pair (c, ty'))) cos'
                    |-> (fn (sorts, cos'') => succeed (Datatype
                         (sorts, cos'')))
                  end
              | NONE =>
                  trns
                  |> fail ("no datatype found for " ^ quote dtco))
        | NONE =>
            trns
            |> fail ("not a type constructor: " ^ quote dtco)
    val tyco' = idf_of_name thy nsp_tyco tyco;
  in
    trns
    |> debug 4 (fn _ => "generating type constructor " ^ quote tyco)
    |> ensure_def [("datatype", defgen_datatype thy tabs)] ("generating type constructor " ^ quote tyco) tyco'
    |> pair tyco'
  end
and exprgen_tyvar_sort thy tabs (v, sort) trns =
  trns
  |> fold_map (ensure_def_class thy tabs) (ClassPackage.operational_sort_of thy sort)
  |-> (fn sort => pair (unprefix "'" v, sort))
and exprgen_type thy tabs (TVar _) trns =
      error "TVar encountered during code generation"
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
      |-> (fn (tyco, tys) => pair (tyco `%% tys))
and exprsgen_type thy tabs =
  fold_map (exprgen_type thy tabs) o snd o devarify_typs;

fun exprgen_classlookup thy tabs (ClassPackage.Instance (inst, ls)) trns =
      trns
      |> ensure_def_inst thy tabs inst
      ||>> (fold_map o fold_map) (exprgen_classlookup thy tabs) ls
      |-> (fn (inst, ls) => pair (Instance (inst, ls)))
  | exprgen_classlookup thy tabs (ClassPackage.Lookup (clss, (v, (i, j)))) trns =
      trns
      |> fold_map (ensure_def_class thy tabs) clss
      |-> (fn clss => pair (Lookup (clss, (v |> unprefix "'", if j = 1 then ~1 else i))))
and mk_fun thy tabs restrict (c, ty1) trns =
  case get_first (fn (name, eqx) => (eqx (c, ty1))) (get_eqextrs thy tabs)
   of SOME ((eq_thms, default), ty2) =>
        let
          val ty3 = if restrict then ty1 else ty2;
          val sortctxt = ClassPackage.extract_sortctxt thy ty3;
          val instantiate = if restrict
            then
              let
                val tab_lookup = snd o the o Vartab.lookup (Sign.typ_match thy (ty2, ty1) Vartab.empty);
              in map_term_types (map_atyps (fn (TVar (vi, _)) => tab_lookup vi
                                             | ty => ty)) end
            else I
          fun dest_eqthm eq_thm =
            let
              val ((t, args), rhs) =
                (apfst strip_comb o Logic.dest_equals o instantiate
                  o prop_of o Drule.zero_var_indexes) eq_thm;
            in case t
             of Const (c', _) => if c' = c then (args, rhs)
                 else error ("illegal function equation for " ^ quote c
                   ^ ", actually defining " ^ quote c')
              | _ => error ("illegal function equation for " ^ quote c)
            end;
          fun mk_default t =
            let
              val (tys, ty') = strip_type ty3;
              val vs = Term.invent_names (add_term_names (t, [])) "x" (length tys);
            in
              if (not o eq_typ thy) (type_of t, ty')
              then error ("inconsistent type for default rule")
              else (map2 (curry Free) vs tys, t)
            end;
        in
          trns
          |> (exprsgen_eqs thy tabs o map dest_eqthm) eq_thms
          ||>> (exprsgen_eqs thy tabs o the_list o Option.map mk_default) default
          ||>> exprsgen_type thy tabs [ty3]
          ||>> fold_map (exprgen_tyvar_sort thy tabs) sortctxt
          |-> (fn (((eqs, eq_default), [ty]), sortctxt) => (pair o SOME) ((eqs @ eq_default, (sortctxt, ty)), ty3))
        end
    | NONE => (NONE, trns)
and ensure_def_inst thy (tabs as (_, (insttab, _, _))) (cls, tyco) trns =
  let
    fun defgen_inst thy (tabs as (_, (insttab, _, _))) inst trns =
      case Option.map (InstNameMangler.rev thy insttab) (name_of_idf thy nsp_inst inst)
       of SOME (_, (class, tyco)) =>
            let
              val (arity, memdefs) = ClassPackage.the_inst_sign thy (class, tyco);
              fun gen_suparity supclass trns =
                trns
                |> ensure_def_class thy tabs supclass
                ||>> ensure_def_inst thy tabs (supclass, tyco)
                ||>> (fold_map o fold_map) (exprgen_classlookup thy tabs)
                      (ClassPackage.extract_classlookup_inst thy (class, tyco) supclass)
                |-> (fn ((supclass, inst), lss) => pair (supclass, (inst, lss)));
              fun gen_membr (m, ty) trns =
                trns
                |> mk_fun thy tabs true (m, ty)
                |-> (fn NONE => error ("could not derive definition for member "
                          ^ quote m ^ " :: " ^ Sign.string_of_typ thy ty)
                      | SOME (funn, ty_use) =>
                    (fold_map o fold_map) (exprgen_classlookup thy tabs)
                       (ClassPackage.extract_classlookup_member thy (ty, ty_use))
                #-> (fn lss =>
                       pair (idf_of_name thy nsp_mem m, ((idf_of_name thy nsp_instmem m, funn), lss))));
            in
              trns
              |> debug 5 (fn _ => "trying defgen class instance for (" ^ quote cls
                   ^ ", " ^ quote tyco ^ ")")
              |> ensure_def_class thy tabs class
              ||>> ensure_def_tyco thy tabs tyco
              ||>> fold_map (exprgen_tyvar_sort thy tabs) arity
              ||>> fold_map gen_suparity (ClassPackage.the_superclasses thy class)
              ||>> fold_map gen_membr memdefs
              |-> (fn ((((class, tyco), arity), suparities), memdefs) =>
                     succeed (Classinst (((class, (tyco, arity)), suparities), memdefs)))
            end
        | _ =>
            trns |> fail ("no class instance found for " ^ quote inst);
    val (_, thyname) = (the o AList.lookup (op =) (ClassPackage.the_instances thy cls)) tyco;
    val inst = idf_of_name thy nsp_inst (InstNameMangler.get thy insttab (thyname, (cls, tyco)));
  in
    trns
    |> debug 4 (fn _ => "generating instance " ^ quote cls ^ " / " ^ quote tyco)
    |> ensure_def [("instance", defgen_inst thy tabs)]
         ("generating instance " ^ quote cls ^ " / " ^ quote tyco) inst
    |> pair inst
  end
and ensure_def_const thy (tabs as (_, (_, overltab, dtcontab))) (c, ty) trns =
  let
    fun defgen_funs thy tabs c trns =
      case recconst_of_idf thy tabs c
       of SOME (c, ty) =>
            trns
            |> mk_fun thy tabs false (c, ty)
            |-> (fn SOME (funn, _) => succeed (Fun funn)
                  | NONE => fail ("no defining equations found for " ^ quote c))
        | NONE =>
            trns
            |> fail ("not a constant: " ^ quote c);
    fun defgen_clsmem thy tabs m trns =
      case name_of_idf thy nsp_mem m
       of SOME m =>
            trns
            |> debug 5 (fn _ => "trying defgen class member for " ^ quote m)
            |> ensure_def_class thy tabs ((the o ClassPackage.lookup_const_class thy) m)
            |-> (fn cls => succeed Undef)
        | _ =>
            trns |> fail ("no class member found for " ^ quote m)
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
    fun get_defgen idf =
      if (is_some oo name_of_idf thy) nsp_const idf
        orelse (is_some oo name_of_idf thy) nsp_overl idf
      then ("funs", defgen_funs thy tabs)
      else if (is_some oo name_of_idf thy) nsp_mem idf
      then ("clsmem", defgen_clsmem thy tabs)
      else if (is_some oo name_of_idf thy) nsp_dtcon idf
      then ("datatypecons", defgen_datatypecons thy tabs)
      else error ("illegal shallow name space for constant: " ^ quote idf);
    val idf = idf_of_const thy tabs (c, ty);
  in
    trns
    |> debug 4 (fn _ => "generating constant " ^ quote c)
    |> ensure_def ((single o get_defgen) idf) ("generating constant " ^ quote c) idf
    |> pair idf
  end
and exprgen_term thy tabs (Const (f, ty)) trns =
      trns
      |> appgen thy tabs ((f, ty), [])
      |-> (fn e => pair e)
  | exprgen_term thy tabs (Var _) trns =
      error "Var encountered during code generation"
  | exprgen_term thy tabs (Free (v, ty)) trns =
      trns
      |> exprgen_type thy tabs ty
      |-> (fn ty => pair (IVar v))
  | exprgen_term thy tabs (Abs (abs as (_, ty, _))) trns =
      let
        val (v, t) = Term.variant_abs abs
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
and exprsgen_term thy tabs =
  fold_map (exprgen_term thy tabs) o snd o devarify_term_typs
and exprsgen_eqs thy tabs =
  apfst (map (fn (rhs::args) => (args, rhs)))
    oo fold_burrow (exprsgen_term thy tabs)
    o map (fn (args, rhs) => (rhs :: args))
and appgen_default thy tabs ((c, ty), ts) trns =
  trns
  |> ensure_def_const thy tabs (c, ty)
  ||>> exprsgen_type thy tabs [ty]
  ||>> (fold_map o fold_map) (exprgen_classlookup thy tabs)
         (ClassPackage.extract_classlookup thy (c, ty))
  ||>> fold_map (exprgen_term thy tabs) ts
  |-> (fn (((c, [ty]), ls), es) =>
         pair (IConst (c, (ls, ty)) `$$ es))
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
            |-> (fn (tys, e) => pair (vs ~~ tys `|--> e))
          end
        else if length ts > imax then
          trns
          |> debug 10 (fn _ => "splitting arguments (" ^ string_of_int imax ^ ", "
               ^ string_of_int (length ts) ^ ")")
          |> ag thy tabs ((f, ty), Library.take (imax, ts))
          ||>> fold_map (exprgen_term thy tabs) (Library.drop (imax, ts))
          |-> (fn (e, es) => pair (e `$$ es))
        else
          trns
          |> debug 10 (fn _ => "keeping arguments")
          |> ag thy tabs ((f, ty), ts)
    | NONE =>
        trns
        |> appgen_default thy tabs ((f, ty), ts);


(* function extractors *)

fun eqextr_defs thy (deftab, _) (c, ty) =
  Option.mapPartial (get_first (fn (ty', (thm, _)) =>
    if Sign.typ_instance thy (ty, ty') 
    then SOME ([thm], ty')
    else NONE
  )) (Symtab.lookup deftab c);


(* parametrized generators, for instantiation in HOL *)

fun appgen_split strip_abs thy tabs (app as (c_ty, [t])) trns =
  case strip_abs 1 (Const c_ty $ t)
   of ([vt], bt) =>
        trns
        |> exprgen_term thy tabs vt
        ||>> exprgen_type thy tabs (type_of vt)
        ||>> exprgen_term thy tabs bt
        ||>> appgen_default thy tabs app
        |-> (fn (((ve, vty), be), e0) => pair (IAbs (((ve, vty), be), e0)))
    | _ =>
        trns
        |> appgen_default thy tabs app;

fun appgen_let strip_abs thy tabs (app as ((c, ty), [dt, ct])) trns =
  case strip_abs 1 ct
   of ([st], bt) =>
        trns
        |> exprgen_term thy tabs dt
        ||>> exprgen_type thy tabs (type_of dt)
        ||>> exprgen_term thy tabs st
        ||>> exprgen_term thy tabs bt
        ||>> appgen_default thy tabs app
        |-> (fn ((((de, dty), se), be), e0) => pair (ICase (((de, dty), [(se, be)]), e0)))
    | _ =>
        trns
        |> appgen_default thy tabs app;

fun appgen_number_of mk_int_to_nat bin_to_int tyco_int tyco_nat thy tabs ((_,
  Type (_, [_, ty as Type (tyco, [])])), [bin]) trns =
    if tyco = tyco_nat then
      trns
      |> exprgen_term thy tabs (mk_int_to_nat bin) (*should be a preprocessor's work*)
    else
      let
        val i = bin_to_int thy bin;
        val _ = if i < 0 then error ("negative numeral: " ^ IntInf.toString i) else ();
          (*should be a preprocessor's work*)
      in
        trns
        |> exprgen_type thy tabs ty
        |-> (fn ty => pair (CodegenThingol.INum ((i, ty), ())))
      end;

fun appgen_wfrec thy tabs ((c, ty), [_, tf, tx]) trns =
  let
    val ty_def = (op ---> o apfst tl o strip_type o Sign.the_const_type thy) c;
    val ty' = (op ---> o apfst tl o strip_type) ty;
    val idf = idf_of_const thy tabs (c, ty);
  in
    trns
    |> ensure_def [("wfrec", (K o succeed) Undef)] ("generating wfrec") idf
    |> exprgen_type thy tabs ty'
    ||>> (fold_map o fold_map) (exprgen_classlookup thy tabs)
           (ClassPackage.extract_classlookup thy (c, ty))
    ||>> exprsgen_type thy tabs [ty_def]
    ||>> exprgen_term thy tabs tf
    ||>> exprgen_term thy tabs tx
    |-> (fn ((((_, ls), [ty]), tf), tx) => pair (IConst (idf, (ls, ty)) `$ tf `$ tx))
  end;

fun eqextr_eq f fals thy tabs ("op =", ty) =
      (case ty
       of Type ("fun", [Type (dtco, _), _]) =>
            (case f thy dtco
             of [] => NONE
              | [eq] => SOME ((Codegen.preprocess thy [eq], NONE), ty)
              | eqs => SOME ((Codegen.preprocess thy eqs, SOME fals), ty))
        | _ => NONE)
  | eqextr_eq f fals thy tabs _ =
      NONE;

fun appgen_datatype_case cos thy tabs (app as ((_, ty), ts)) trns =
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
        |-> (fn (ep, e) => pair (ep, e))
      end;
  in
    trns
    |> exprgen_term thy tabs t
    ||>> exprgen_type thy tabs dty
    ||>> fold_map cg_case_d ((cos ~~ tys) ~~ ts')
    ||>> appgen_default thy tabs app
    |-> (fn (((de, dty), bses), e0) => pair (ICase (((de, dty), bses), e0)))
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



(** theory interface **)

fun mk_tabs thy =
  let
    fun extract_defs thy =
      let
        fun dest thm =
          let
            val (lhs, rhs) = Logic.dest_equals (prop_of thm);
            val (t, args) = strip_comb lhs;
            val (c, ty) = dest_Const t
          in if forall is_Var args then SOME ((c, ty), thm) else NONE
          end handle TERM _ => NONE;
        fun prep_def def = (case Codegen.preprocess thy [def] of
          [def'] => def' | _ => error "mk_tabs: bad preprocessor");
        fun add_def thyname (name, _) =
          case (dest o prep_def o Thm.get_axiom thy) name
           of SOME ((c, ty), thm) =>
                Symtab.default (c, [])
                #> Symtab.map_entry c (cons (ty, (thm, thyname)))
            | NONE => I
        fun get_defs thy =
          let
            val thyname = Context.theory_name thy;
            val defs = (snd o #axioms o Theory.rep_theory) thy;
          in Symtab.fold (add_def thyname) defs end;
      in
        Symtab.empty
        |> fold get_defs (thy :: Theory.ancestors_of thy)
      end;
    fun mk_insttab thy =
      InstNameMangler.empty
      |> Symtab.fold_map
          (fn (cls, clsinsts) => fold_map
            (fn (tyco, thyname) => InstNameMangler.declare thy (thyname, (cls, tyco))) clsinsts)
                 (ClassPackage.get_classtab thy)
      |-> (fn _ => I);
    fun mk_overltabs thy =
      (Symtab.empty, ConstNameMangler.empty)
      |> Symtab.fold
          (fn (c, _) =>
            let
              val deftab = Defs.specifications_of (Theory.defs_of thy) c
              val is_overl = (is_none o ClassPackage.lookup_const_class thy) c
               andalso case deftab
               of [] => false
                | [(ty, _)] => not (eq_typ thy (ty, Sign.the_const_type thy c))
                | _ => true;
            in if is_overl then (fn (overltab1, overltab2) => (
              overltab1
              |> Symtab.update_new (c, map fst deftab),
              overltab2
              |> fold_map (fn (ty, _) => ConstNameMangler.declare thy (c, ty)) deftab
              |-> (fn _ => I))) else I
            end) ((#2 o #constants o Consts.dest o #consts o Sign.rep_sg) thy)
      |> (fn (overltab1, overltab2) =>
            let
              val c = "op =";
              val ty = Sign.the_const_type thy c;
              fun inst dtco =
                map_atyps (fn _ => Type (dtco,
                  (map (fn (v, sort) => TVar ((v, 0), sort)) o fst o the o get_datatype thy) dtco)) ty
              val dtcos = fold (insert (op =) o snd) (get_all_datatype_cons thy) [];
              val tys = map inst dtcos;
            in
              (overltab1
               |> Symtab.update_new (c, tys),
               overltab2
               |> fold (fn ty => ConstNameMangler.declare thy (c, ty) #> snd) tys)
            end);
    fun mk_dtcontab thy =
      DatatypeconsNameMangler.empty
      |> fold_map
          (fn (_, co_dtco) => DatatypeconsNameMangler.declare_multi thy co_dtco)
            (fold (fn (co, dtco) =>
              let
                val key = ((NameSpace.drop_base o NameSpace.drop_base) co, NameSpace.base co);
              in AList.default (op =) (key, []) #> AList.map_entry (op =) key (cons (co, dtco)) end
            ) (get_all_datatype_cons thy) [])
      |-> (fn _ => I);
    val deftab = extract_defs thy;
    val insttab = mk_insttab thy;
    val overltabs = mk_overltabs thy;
    val dtcontab = mk_dtcontab thy;
  in (deftab, (insttab, overltabs, dtcontab)) end;

fun get_serializer target =
  case Symtab.lookup (!serializers) target
   of SOME seri => seri
    | NONE => Scan.fail_with (fn _ => "unknown code target language: " ^ quote target) ();

fun map_module f =
  map_codegen_data (fn (modl, gens, target_data, logic_data) =>
    (f modl, gens, target_data, logic_data));

fun expand_module init gen arg thy =
  (#modl o CodegenData.get) thy
  |> start_transact init (gen thy (mk_tabs thy) arg)
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
          @ own_tables (#2 o #constants o Consts.dest o #consts o Sign.rep_sg);
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

fun codegen_term t thy =
  thy
  |> expand_module NONE exprsgen_term [Codegen.preprocess_term thy t]
  |-> (fn [t] => pair t);

val is_dtcon = has_nsp nsp_dtcon;

fun consts_of_idfs thy =
  map (the o const_of_idf thy (mk_tabs thy));

fun idfs_of_consts thy =
  map (idf_of_const thy (mk_tabs thy));

val get_root_module = (#modl o CodegenData.get);

fun get_ml_fun_datatype thy resolv =
  let
    val target_data =
      ((fn data => (the o Symtab.lookup data) "ml") o #target_data o CodegenData.get) thy;
  in
    CodegenSerializer.ml_fun_datatype (nsp_dtcon, nsp_class, K false)
      ((Option.map fst oo Symtab.lookup o #syntax_tyco) target_data,
      (Option.map fst oo Symtab.lookup o #syntax_const) target_data)
      resolv
  end;


(** target languages **)

(* primitive definitions *)

fun read_typ thy =
  Sign.read_typ (thy, K NONE);

fun read_const thy =
  (dest_Const o Sign.read_term thy);

fun read_quote get reader gen raw thy =
  thy
  |> expand_module ((SOME o get) thy)
       (fn thy => fn tabs => gen thy tabs o single o reader thy) raw
  |-> (fn [x] => pair x);

fun gen_add_prim prep_name prep_primdef raw_name (target, raw_primdef) thy =
  let
    val _ = if Symtab.defined ((#target_data o CodegenData.get) thy) target
      then () else error ("unknown target language: " ^ quote target);
    val tabs = mk_tabs thy;
    val name = prep_name thy tabs raw_name;
    val primdef = prep_primdef raw_primdef;
  in
    thy
    |> map_module (CodegenThingol.add_prim name (target, primdef))
  end;

val add_prim_i = gen_add_prim ((K o K) I) I;
val add_prim_class = gen_add_prim
  (fn thy => K (idf_of_name thy nsp_class o Sign.intern_class thy))
  CodegenSerializer.parse_targetdef;
val add_prim_tyco = gen_add_prim
  (fn thy => K (idf_of_name thy nsp_tyco o Sign.intern_type thy))
  CodegenSerializer.parse_targetdef;
val add_prim_const = gen_add_prim
  (fn thy => fn tabs => idf_of_const thy tabs o read_const thy)
  CodegenSerializer.parse_targetdef;

val ensure_prim = map_module oo CodegenThingol.ensure_prim;


(* syntax *)

fun gen_add_syntax_class prep_class class target pretty thy =
  thy
  |> map_codegen_data
    (fn (modl, gens, target_data, logic_data) =>
       (modl, gens,
        target_data |> Symtab.map_entry target
          (map_target_data
            (fn (syntax_class, syntax_tyco, syntax_const) =>
             (syntax_class
              |> Symtab.update (prep_class thy class, pretty), syntax_tyco, syntax_const))),
        logic_data));

val add_syntax_class = gen_add_syntax_class Sign.intern_class;

fun parse_syntax_tyco raw_tyco =
  let
    fun check_tyco thy tyco =
      if Sign.declared_tyname thy tyco
      then tyco
      else error ("no such type constructor: " ^ quote tyco);
    fun prep_tyco thy raw_tyco =
      raw_tyco
      |> Sign.intern_type thy
      |> check_tyco thy
      |> idf_of_name thy nsp_tyco;
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
        |> ensure_prim tyco target
        |> reader
        |-> (fn pretty => map_codegen_data
          (fn (modl, gens, target_data, logic_data) =>
             (modl, gens,
              target_data |> Symtab.map_entry target
                (map_target_data
                  (fn (syntax_class, syntax_tyco, syntax_const) =>
                   (syntax_class, syntax_tyco |> Symtab.update
                      (tyco, (pretty, stamp ())),
                    syntax_const))),
              logic_data)))
      end;
  in
    CodegenSerializer.parse_syntax (fn thy => no_args_tyco thy raw_tyco)
    (read_quote (fn thy => prep_tyco thy raw_tyco) read_typ exprsgen_type)
    #-> (fn reader => pair (mk reader))
  end;

fun add_pretty_syntax_const c target pretty =
  map_codegen_data
    (fn (modl, gens, target_data, logic_data) =>
       (modl, gens,
        target_data |> Symtab.map_entry target
          (map_target_data
            (fn (syntax_class, syntax_tyco, syntax_const) =>
             (syntax_class, syntax_tyco,
              syntax_const
              |> Symtab.update
                 (c, (pretty, stamp ()))))),
        logic_data));

fun parse_syntax_const raw_const =
  let
    fun prep_const thy raw_const =
      idf_of_const thy (mk_tabs thy) (read_const thy raw_const);
    fun no_args_const thy raw_const =
      (length o fst o strip_type o snd o read_const thy) raw_const;
    fun mk reader target thy =
      let
        val _ = get_serializer target;
        val c = prep_const thy raw_const;
      in
        thy
        |> ensure_prim c target
        |> reader
        |-> (fn pretty => add_pretty_syntax_const c target pretty)
      end;
  in
    CodegenSerializer.parse_syntax (fn thy => no_args_const thy raw_const)
      (read_quote (fn thy => prep_const thy raw_const) Sign.read_term exprsgen_term)
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
      in
        thy
        |> expand_module NONE (fold_map oo ensure_def_const) consts
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
          (Symtab.lookup o #syntax_class) target_data,
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
     syntax_classK, syntax_tycoK, syntax_constK, aliasK) =
  ("code_generate", "code_serialize",
   "code_primclass", "code_primtyco", "code_primconst",
   "code_syntax_class", "code_syntax_tyco", "code_syntax_const", "code_alias");

val generateP =
  OuterSyntax.command generateK "generate executable code for constants" K.thy_decl (
    Scan.repeat1 P.term
    >> (fn raw_consts =>
          Toplevel.theory (generate_code (SOME raw_consts) #> snd))
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

val aliasP =
  OuterSyntax.command aliasK "declare an alias for a theory identifier" K.thy_decl (
    Scan.repeat1 (P.name -- P.name)
      >> (Toplevel.theory oo fold) add_alias
  );

val primclassP =
  OuterSyntax.command primclassK "define target-lanugage specific class" K.thy_decl (
    P.xname
    -- Scan.repeat1 (P.name -- P.text)
      >> (fn (raw_class, primdefs) =>
            (Toplevel.theory oo fold) (add_prim_class raw_class) primdefs)
  );

val primtycoP =
  OuterSyntax.command primtycoK "define target-lanugage specific type constructor" K.thy_decl (
    P.xname
    -- Scan.repeat1 (P.name -- P.text)
      >> (fn (raw_tyco, primdefs) =>
            (Toplevel.theory oo fold) (add_prim_tyco raw_tyco) primdefs)
  );

val primconstP =
  OuterSyntax.command primconstK "define target-lanugage specific constant" K.thy_decl (
    P.term
    -- Scan.repeat1 (P.name -- P.text)
      >> (fn (raw_const, primdefs) =>
            (Toplevel.theory oo fold) (add_prim_const raw_const) primdefs)
  );

val syntax_classP =
  OuterSyntax.command syntax_tycoK "define code syntax for class" K.thy_decl (
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

val _ = OuterSyntax.add_parsers [generateP, serializeP, aliasP,
  primclassP, primtycoP, primconstP, syntax_tycoP, syntax_constP];



(** theory setup **)

val _ = Context.add_setup (
  add_eqextr ("defs", eqextr_defs)
);

end; (* local *)

end; (* struct *)

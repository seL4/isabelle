(*  Title:      Pure/Tools/codegen_package.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Code generator from Isabelle theories to
intermediate language ("Thin-gol").
*)

signature CODEGEN_PACKAGE =
sig
  val codegen_term: term -> theory -> CodegenThingol.iexpr * theory;
  val is_dtcon: string -> bool;
  val consts_of_idfs: theory -> string list -> (string * typ) list;
  val idfs_of_consts: theory -> (string * typ) list -> string list;
  val get_root_module: theory -> CodegenThingol.module;
  val get_ml_fun_datatype: theory -> (string -> string)
    -> ((string * CodegenThingol.funn) list -> Pretty.T)
        * ((string * CodegenThingol.datatyp) list -> Pretty.T);

  val add_pretty_list: string -> string -> string * (int * string)
    -> theory -> theory;
  val add_alias: string * string -> theory -> theory;
  val set_get_all_datatype_cons : (theory -> (string * string) list)
    -> theory -> theory;
  val set_get_datatype: (theory -> string -> ((string * sort) list * (string * typ list) list) option)
    -> theory -> theory;
  val set_int_tyco: string -> theory -> theory;

  type appgen;
  val add_appconst: xstring * ((int * int) * appgen) -> theory -> theory;
  val add_appconst_i: string * ((int * int) * appgen) -> theory -> theory;
  val appgen_default: appgen;
  val appgen_let: (int -> term -> term list * term)
    -> appgen;
  val appgen_split: (int -> term -> term list * term)
    -> appgen;
  val appgen_number_of: (theory -> term -> IntInf.int) -> appgen;
  val appgen_char: (term -> int option) -> appgen;
  val appgen_wfrec: appgen;
  val add_case_const: string -> (string * int) list -> theory -> theory;

  val print_code: theory -> unit;
  val rename_inconsistent: theory -> theory;

  (*debugging purpose only*)
  structure InstNameMangler: NAME_MANGLER;
  structure ConstNameMangler: NAME_MANGLER;
  structure DatatypeconsNameMangler: NAME_MANGLER;
  structure CodegenData: THEORY_DATA;
  type auxtab;
  val mk_tabs: theory -> string list option -> auxtab;
  val alias_get: theory -> string -> string;
  val idf_of_name: theory -> string -> string -> string;
  val idf_of_const: theory -> auxtab -> string * typ -> string;
  val idf_of_co: theory -> auxtab -> string * string -> string option;
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

type deftab = (typ * thm) list Symtab.table;

fun is_overloaded thy c = case Theory.definitions_of thy c
 of [] => true   (* FIXME false (!?) *)
  | [{lhs = ty, ...}] => not (Sign.typ_equiv thy (ty, Sign.the_const_type thy c))
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
        case (find_first (fn {lhs, ...} => Sign.typ_equiv thy (ty, lhs))
            (Theory.definitions_of thy c))
         of SOME {module, ...} => NameSpace.append module nsp_overl
          | NONE => if c = "op ="
              then
                NameSpace.append
                  (((fn s => Codegen.thyname_of_type s thy) o fst o dest_Type o hd o fst o strip_type) ty)
                  nsp_overl
              else
                NameSpace.drop_base c';
      val c'' = NameSpace.append prefix (NameSpace.base c');
      fun mangle (Type (tyco, tys)) =
            (NameSpace.base o alias_get thy) tyco :: flat (map_filter mangle tys) |> SOME
        | mangle _ =
            NONE
    in
      Vartab.empty
      |> Type.raw_match (Sign.the_const_type thy c, ty)
      |> map (snd o snd) o Vartab.dest
      |> map_filter mangle
      |> flat
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

type auxtab = (bool * string list option * deftab)
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
            (nsp_dtcon, [nsp_module, nsp_class, nsp_tyco, nsp_dtcon])
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
   of { modl, gens, target_data, logic_data } =>
      let val (modl, gens, target_data, logic_data) =
        f (modl, gens, target_data, logic_data)
      in CodegenData.put { modl = modl, gens = gens,
           target_data = target_data, logic_data = logic_data } thy end;

val print_code = CodegenData.print;

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

fun idf_of_co thy (tabs as (_, (_, _, dtcontab))) (co, dtco) =
  case CodegenTheorems.get_datatypes thy dtco
   of SOME ((_, cos), _) => if AList.defined (op =) cos co
        then try (DatatypeconsNameMangler.get thy dtcontab) (co, dtco)
          |> the_default co
          |> idf_of_name thy nsp_dtcon
          |> SOME
        else NONE
    | NONE => NONE;

fun co_of_idf thy (tabs as (_, (_, _, dtcontab))) idf =
  case name_of_idf thy nsp_dtcon idf
   of SOME idf' => let
        val (c, dtco) = case try (DatatypeconsNameMangler.rev thy dtcontab) idf'
         of SOME c_dtco => c_dtco
          | NONE => case (snd o strip_type o Sign.the_const_type thy) idf'
                    of Type (dtco, _) => (idf', dtco)
                     | _ => (idf', "nat") (*a hack*)
      in SOME (c, dtco) end
    | NONE => NONE;

fun idf_of_const thy (tabs as (_, (_, (overltab1, overltab2), _)))
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
       of Type (tyco, _) => idf_of_co thy tabs (c, tyco)
        | _ => NONE;
  in case get_datatypecons (c, ty)
   of SOME idf => idf
    | NONE => case get_overloaded (c, ty)
   of SOME idf => idf
    | NONE => case ClassPackage.lookup_const_class thy c
   of SOME _ => idf_of_name thy nsp_mem c
    | NONE => idf_of_name thy nsp_const c
  end;

fun idf_of_const' thy (tabs as (_, (_, (overltab1, overltab2), _)))
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
  in case get_overloaded (c, ty)
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

fun const_of_idf thy (tabs as (_, (_, _, dtcontab))) idf =
  case recconst_of_idf thy tabs idf
   of SOME c_ty => SOME c_ty
    | NONE => case dest_nsp nsp_mem idf
       of SOME c => SOME (c, Sign.the_const_constraint thy c)
        | NONE => case co_of_idf thy tabs idf
           of SOME (c, dtco) =>
                let
                  val (vars, cos) = (fst o the o CodegenTheorems.get_datatypes thy) dtco
                in
                  SOME (c, (the o AList.lookup (op =) cos) c ---> Type (dtco, map TFree vars) |> Logic.varifyT)
                end
            | NONE => NONE;

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


(* definition and expression generators *)

fun check_strict thy f x ((false, _, _), _) =
      false
  | check_strict thy f x ((_, SOME targets, _), _) =
      exists (
        is_none o (fn tab => Symtab.lookup tab x) o f o the o (Symtab.lookup ((#target_data o CodegenData.get) thy))
      ) targets
  | check_strict thy f x ((true, _, _), _) =
      true;

fun no_strict ((_, targets, deftab), tabs') = ((false, targets, deftab), tabs');

fun ensure_def_class thy tabs cls trns =
  let
    fun defgen_class thy (tabs as (_, (insttab, _, _))) cls trns =
      case name_of_idf thy nsp_class cls
       of SOME cls =>
            let
              val (v, cs) = (ClassPackage.the_consts_sign thy) cls;
              val sortctxts = map (ClassPackage.sortcontext_of_typ thy o snd) cs;
              val idfs = map (idf_of_name thy nsp_mem o fst) cs;
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
            |> fail ("no class definition found for " ^ quote cls);
    val cls' = idf_of_name thy nsp_class cls;
  in
    trns
    |> debug_msg (fn _ => "generating class " ^ quote cls)
    |> ensure_def (defgen_class thy tabs) true ("generating class " ^ quote cls) cls'
    |> pair cls'
  end
and ensure_def_tyco thy tabs tyco trns =
  let
    val tyco' = idf_of_name thy nsp_tyco tyco;
    val strict = check_strict thy #syntax_tyco tyco' tabs;
    fun defgen_datatype thy (tabs as (_, (_, _, dtcontab))) dtco trns =
      case name_of_idf thy nsp_tyco dtco
       of SOME dtco =>
         (case CodegenTheorems.get_datatypes thy dtco
             of SOME ((vars, cos), _) =>
                  trns
                  |> debug_msg (fn _ => "trying defgen datatype for " ^ quote dtco)
                  |> fold_map (exprgen_tyvar_sort thy tabs) vars
                  ||>> fold_map (fn (c, tys) =>
                    fold_map (exprgen_type thy tabs) tys
                    #-> (fn tys' => pair ((the o idf_of_co thy tabs) (c, dtco), tys'))) cos
                  |-> (fn (vars, cos) => succeed (Datatype
                       (vars, cos)))
              | NONE =>
                  trns
                  |> fail ("no datatype found for " ^ quote dtco))
        | NONE =>
            trns
            |> fail ("not a type constructor: " ^ quote dtco)
  in
    trns
    |> debug_msg (fn _ => "generating type constructor " ^ quote tyco)
    |> ensure_def (defgen_datatype thy tabs) strict ("generating type constructor " ^ quote tyco) tyco'
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
and mk_fun thy tabs (c, ty) trns =
  case CodegenTheorems.get_funs thy (c, Logic.legacy_varifyT ty)  (* FIXME *)
   of eq_thms as eq_thm :: _ =>
        let
          val msg = cat_lines ("generating code for theorems " :: map string_of_thm eq_thms);
          val ty = (Logic.legacy_unvarifyT o CodegenTheorems.extr_typ thy) eq_thm
          val sortcontext = ClassPackage.sortcontext_of_typ thy ty;
          fun dest_eqthm eq_thm =
            let
              val ((t, args), rhs) =
                (apfst strip_comb o Logic.dest_equals o Logic.legacy_unvarify o prop_of) eq_thm;
            in case t
             of Const (c', _) => if c' = c then (args, rhs)
                 else error ("illegal function equation for " ^ quote c
                   ^ ", actually defining " ^ quote c')
              | _ => error ("illegal function equation for " ^ quote c)
            end;
          fun exprgen_eq (args, rhs) trns =
            trns
            |> fold_map (exprgen_term thy tabs) args
            ||>> exprgen_term thy tabs rhs;
        in
          trns
          |> message msg (fn trns => trns
          |> fold_map (exprgen_eq o dest_eqthm) eq_thms
          ||>> fold_map (exprgen_tyvar_sort thy tabs) sortcontext
          ||>> exprgen_type thy tabs ty
          |-> (fn ((eqs, sortctxt), ty) => (pair o SOME) ((eqs, (sortctxt, ty)), map snd sortcontext)))
        end
    | [] => (NONE, trns)
and ensure_def_inst thy (tabs as (_, (insttab, _, _))) (cls, tyco) trns =
  let
    fun defgen_inst thy (tabs as (_, (insttab, _, _))) inst trns =
      case Option.map (InstNameMangler.rev thy insttab) (name_of_idf thy nsp_inst inst)
       of SOME (_, (class, tyco)) =>
            let
              val (arity, memdefs) = ClassPackage.the_inst_sign thy (class, tyco);
              val arity_typ = Type (tyco, (map TFree arity));
              val operational_arity = map_filter (fn (v, sort) => case ClassPackage.operational_sort_of thy sort
               of [] => NONE
                | sort => SOME (v, sort)) arity;
              fun gen_suparity supclass trns =
                trns
                |> ensure_def_class thy tabs supclass
                ||>> fold_map (exprgen_classlookup thy tabs)
                      (ClassPackage.sortlookup thy ([supclass], arity_typ));
              fun gen_membr (m, ty) trns =
                trns
                |> mk_fun thy tabs (m, ty)
                |-> (fn NONE => error ("could not derive definition for member "
                          ^ quote m ^ " :: " ^ Sign.string_of_typ thy ty)
                      | SOME (funn, sorts) => fold_map (fn (sort, sort_ctxt) =>
                          fold_map (exprgen_classlookup thy tabs)
                            (ClassPackage.sortlookup thy (sort, TFree sort_ctxt)))
                            (sorts ~~ operational_arity)
                #-> (fn lss =>
                       pair (idf_of_name thy nsp_mem m, ((idf_of_name thy nsp_instmem m, funn), lss))));
            in
              trns
              |> debug_msg (fn _ => "trying defgen class instance for (" ^ quote cls
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
    |> debug_msg (fn _ => "generating instance " ^ quote cls ^ " / " ^ quote tyco)
    |> ensure_def (defgen_inst thy tabs) true
         ("generating instance " ^ quote cls ^ " / " ^ quote tyco) inst
    |> pair inst
  end
and ensure_def_const thy (tabs as (_, (_, overltab, dtcontab))) (c, ty) trns =
  let
    fun defgen_funs thy tabs c trns =
      case recconst_of_idf thy tabs c
       of SOME (c, ty) =>
            trns
            |> mk_fun thy tabs (c, ty)
            |-> (fn SOME (funn, _) => succeed (Fun funn)
                  | NONE => fail ("no defining equations found for " ^
                      (quote o Display.raw_string_of_term o Const) (c, ty)))
        | NONE =>
            trns
            |> fail ("not a constant: " ^ quote c);
    fun defgen_clsmem thy tabs m trns =
      case name_of_idf thy nsp_mem m
       of SOME m =>
            trns
            |> debug_msg (fn _ => "trying defgen class member for " ^ quote m)
            |> ensure_def_class thy tabs ((the o ClassPackage.lookup_const_class thy) m)
            |-> (fn cls => succeed Bot)
        | _ =>
            trns |> fail ("no class member found for " ^ quote m)
    fun defgen_datatypecons thy (tabs as (_, (_, _, dtcontab))) co trns =
      case co_of_idf thy tabs co
       of SOME (co, dtco) =>
            trns
            |> debug_msg (fn _ => "trying defgen datatype constructor for " ^ quote co)
            |> ensure_def_tyco thy tabs dtco
            |-> (fn dtco => succeed Bot)
        | _ =>
            trns
            |> fail ("not a datatype constructor: " ^ quote co);
    fun get_defgen tabs idf strict =
      if (is_some oo name_of_idf thy) nsp_const idf
        orelse (is_some oo name_of_idf thy) nsp_overl idf
      then defgen_funs thy tabs strict
      else if (is_some oo name_of_idf thy) nsp_mem idf
      then defgen_clsmem thy tabs strict
      else if (is_some oo name_of_idf thy) nsp_dtcon idf
      then defgen_datatypecons thy tabs strict
      else error ("illegal shallow name space for constant: " ^ quote idf);
    val idf = idf_of_const thy tabs (c, ty);
    val strict = check_strict thy #syntax_const idf tabs;
  in
    trns
    |> debug_msg (fn _ => "generating constant " ^ (quote o Display.raw_string_of_term o Const) (c, ty))
    |> ensure_def (get_defgen tabs idf) strict ("generating constant " ^ quote c) idf
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
and appgen_default thy tabs ((c, ty), ts) trns =
  trns
  |> ensure_def_const thy tabs (c, ty)
  ||>> exprgen_type thy tabs ty
  ||>> (fold_map o fold_map) (exprgen_classlookup thy tabs)
         (ClassPackage.sortlookups_const thy (c, ty))
  ||>> fold_map (exprgen_term thy tabs) ts
  |-> (fn (((c, ty), ls), es) =>
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
            |> fold_map (exprgen_type thy tabs) tys
            ||>> ag thy tabs ((f, ty), ts @ map2 (curry Free) vs tys)
            |-> (fn (tys, e) => pair (vs ~~ tys `|--> e))
          end
        else if length ts > imax then
          trns
          |> ag thy tabs ((f, ty), Library.take (imax, ts))
          ||>> fold_map (exprgen_term thy tabs) (Library.drop (imax, ts))
          |-> (fn (e, es) => pair (e `$$ es))
        else
          trns
          |> ag thy tabs ((f, ty), ts)
    | NONE =>
        trns
        |> appgen_default thy tabs ((f, ty), ts);


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

fun appgen_number_of int_of_bin thy tabs (app as (c as (_, ty), [bin])) trns =
  case try (int_of_bin thy) bin
   of SOME i => if i < 0 then error ("negative numeral: " ^ IntInf.toString i)
                (*preprocessor eliminates nat and negative numerals*)
      else
        trns
        |> pair (CodegenThingol.INum (i, IVar ""))
        (*|> exprgen_term thy (no_strict tabs) (Const c)
        ||>> exprgen_term thy (no_strict tabs) bin
        |-> (fn (e1, e2) => pair (CodegenThingol.INum (i, e1 `$ e2)))*)
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

fun appgen_wfrec thy tabs ((c, ty), [_, tf, tx]) trns =
  let
    val ty_def = (op ---> o apfst tl o strip_type o Logic.legacy_unvarifyT o Sign.the_const_type thy) c;
    val ty' = (op ---> o apfst tl o strip_type) ty;
    val idf = idf_of_const thy tabs (c, ty);
  in
    trns
    |> ensure_def ((K o fail) "no extraction of wfrec") false ("generating wfrec") idf
    |> exprgen_type thy tabs ty'
    ||>> (fold_map o fold_map) (exprgen_classlookup thy tabs)
           (ClassPackage.sortlookups_const thy (c, ty))
    ||>> exprgen_type thy tabs ty_def
    ||>> exprgen_term thy tabs tf
    ||>> exprgen_term thy tabs tx
    |-> (fn ((((_, ls), ty), tf), tx) => pair (IConst (idf, (ls, ty)) `$ tf `$ tx))
  end;

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

fun add_case_const c cos thy =
  let
    val n_eta = length cos + 1;
  in
    thy
    |> add_appconst_i (c, ((n_eta, n_eta), appgen_datatype_case cos))
  end;



(** theory interface **)

fun mk_tabs thy targets =
  let
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
              val deftab = Theory.definitions_of thy c
              val is_overl = (is_none o ClassPackage.lookup_const_class thy) c
               andalso case deftab   (* is_overloaded (!?) *)
               of [] => false
                | [{lhs = ty, ...}] => not (Sign.typ_equiv thy (ty, Sign.the_const_type thy c))
                | _ => true;
            in if is_overl then (fn (overltab1, overltab2) => (
              overltab1
              |> Symtab.update_new (c, map #lhs deftab),
              overltab2
              |> fold_map (fn {lhs = ty, ...} => ConstNameMangler.declare thy (c, ty)) deftab
              |-> (fn _ => I))) else I
            end) ((#2 o #constants o Consts.dest o #consts o Sign.rep_sg) thy)
      |> (fn (overltab1, overltab2) =>
            let
              val c = "op =";
              val ty = Sign.the_const_type thy c;
              fun inst tyco =
                let
                  val ty_inst =
                    tyco
                    |> Symtab.lookup ((snd o #types o Type.rep_tsig o Sign.tsig_of) thy)
                    |> (fn SOME (Type.LogicalType i, _) => i)
                    |> Term.invent_names [] "'a"
                    |> map (fn v => (TVar ((v, 0), Sign.defaultS thy)))
                    |> (fn tys => Type (tyco, tys))
                in map_atyps (fn _ => ty_inst) ty end;
              val tys =
                (Type.logical_types o Sign.tsig_of) thy
                |> filter (fn tyco => can (Sign.arity_sorts thy tyco) (Sign.defaultS thy))
                |> map inst
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
    val insttab = mk_insttab thy;
    val overltabs = mk_overltabs thy;
    val dtcontab = mk_dtcontab thy;
  in ((true, targets, Symtab.empty), (insttab, overltabs, dtcontab)) end;

fun get_serializer target =
  case Symtab.lookup (!serializers) target
   of SOME seri => seri
    | NONE => Scan.fail_with (fn _ => "unknown code target language: " ^ quote target) ();

fun map_module f =
  map_codegen_data (fn (modl, gens, target_data, logic_data) =>
    (f modl, gens, target_data, logic_data));

fun purge_defs NONE thy =
      map_module (K CodegenThingol.empty_module) thy
  | purge_defs (SOME cs) thy =
      let
        val tabs = mk_tabs thy NONE;
        val idfs = map (idf_of_const' thy tabs) cs;
        fun purge idfs modl =
          CodegenThingol.purge_module (filter (can (get_def modl)) idfs) modl
      in
        map_module (purge idfs) thy
      end;

fun expand_module targets init gen arg thy =
  thy
  |> CodegenTheorems.notify_dirty
  |> `(#modl o CodegenData.get)
  |> (fn (modl, thy) =>
        (start_transact init (gen thy (mk_tabs thy targets) arg) modl, thy))
  |-> (fn (x, modl) => map_module (K modl) #> pair x);

fun rename_inconsistent thy =
  let
    fun get_inconsistent thyname =
      let
        val thy = theory thyname;
        fun own_tables get =
          get thy
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
    val inconsistent = map get_inconsistent (ThyInfo.names ()) |> flat;
    fun add (src, dst) thy =
      if (is_some oo Symtab.lookup o fst o #alias o #logic_data o CodegenData.get) thy src
      then (warning ("code generator alias already defined for " ^ quote src ^ ", will not overwrite"); thy)
      else add_alias (src, dst) thy
  in fold add inconsistent thy end;

fun codegen_term t =
  expand_module NONE NONE exprgen_term t;

val is_dtcon = has_nsp nsp_dtcon;

fun consts_of_idfs thy =
  map (the o const_of_idf thy (mk_tabs thy NONE));

fun idfs_of_consts thy =
  map (idf_of_const thy (mk_tabs thy NONE));

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

(* syntax *)

fun read_typ thy =
  Sign.read_typ (thy, K NONE);

fun read_const thy raw_t =
  let
    val t = Sign.read_term thy raw_t
  in case try dest_Const t
   of SOME c => c
    | NONE => error ("not a constant: " ^ Sign.string_of_term thy t)
  end;

fun read_quote get reader gen raw thy =
  thy
  |> expand_module NONE ((SOME o get) thy)
       (fn thy => fn tabs => gen thy tabs o single o reader thy) raw
  |-> (fn [x] => pair x);

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
    (read_quote (fn thy => prep_tyco thy raw_tyco) read_typ 
      (fn thy => fn tabs => fold_map (exprgen_type thy tabs)))
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
      idf_of_const thy (mk_tabs thy NONE) (read_const thy raw_const);
    fun no_args_const thy raw_const =
      (length o fst o strip_type o snd o read_const thy) raw_const;
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
      (read_quote (fn thy => prep_const thy raw_const) Sign.read_term
      (fn thy => fn tabs => fold_map (exprgen_term thy tabs)))
    #-> (fn reader => pair (mk reader))
  end;

fun add_pretty_list raw_nil raw_cons (target, seri) thy =
  let
    val _ = get_serializer target;
    val tabs = mk_tabs thy NONE;
    fun mk_const raw_name =
      let
        val name = Sign.intern_const thy raw_name;
      in idf_of_const thy tabs (name, Sign.the_const_type thy name) end;
    val nil' = mk_const raw_nil;
    val cons' = mk_const raw_cons;
    val pr' = CodegenSerializer.pretty_list nil' cons' seri;
  in
    thy
    |> add_pretty_syntax_const cons' target pr'
  end;



(** code basis change notifications **)

val _ = Context.add_setup (CodegenTheorems.add_notify purge_defs);



(** toplevel interface **)

local

fun generate_code targets (SOME raw_consts) thy =
      let
        val consts = map (read_const thy) raw_consts;
        val _ = case targets of SOME targets => (map get_serializer targets; ()) | _ => ();
      in
        thy
        |> expand_module targets NONE (fold_map oo ensure_def_const) consts
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
        ) ([] (*TODO: add seri_defs here*), cs) module : unit; thy)
      end;
  in
    thy
    |> generate_code (SOME [target]) raw_consts
    |-> (fn cs => serialize cs)
  end;

fun purge_consts raw_ts thy =
  let
    val cs = map (read_const thy) raw_ts;
  in fold CodegenTheorems.purge_defs cs thy end;

structure P = OuterParse
and K = OuterKeyword

in

val (generateK, serializeK,
     syntax_classK, syntax_tycoK, syntax_constK,
     purgeK, aliasK) =
  ("code_generate", "code_serialize",
   "code_classapp", "code_typapp", "code_constapp",
   "code_purge", "code_alias");

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
  OuterSyntax.command purgeK "purge all defintions for constant" K.thy_decl (
    Scan.repeat1 P.term
    >> (Toplevel.theory o purge_consts)
  );

val aliasP =
  OuterSyntax.command aliasK "declare an alias for a theory identifier" K.thy_decl (
    Scan.repeat1 (P.name -- P.name)
      >> (Toplevel.theory oo fold) add_alias
  );

val _ = OuterSyntax.add_parsers [generateP, serializeP,
  syntax_classP, syntax_tycoP, syntax_constP,
  purgeP, aliasP];

end; (* local *)

end; (* struct *)

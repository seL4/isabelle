(*  Title:      Pure/Tools/codegen_package.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Code generator extraction kernel. Code generator Isar setup.
*)

signature CODEGEN_PACKAGE =
sig
  include BASIC_CODEGEN_THINGOL;
  val codegen_term: theory -> term -> thm * iterm;
  val eval_term: theory -> (string (*reference name!*) * 'a option ref) * term -> 'a;
  val const_of_idf: theory -> string -> string * typ;
  val get_root_module: theory -> CodegenThingol.code;

  type appgen;
  val add_appconst: string * appgen -> theory -> theory;
  val appgen_numeral: (theory -> term -> IntInf.int) -> appgen;
  val appgen_char: (term -> int option) -> appgen;
  val appgen_case: (theory -> term
    -> ((string * typ) list * ((term * typ) * (term * term) list)) option)
    -> appgen;
  val appgen_let: appgen;
end;

structure CodegenPackage : CODEGEN_PACKAGE =
struct

open BasicCodegenThingol;
val tracing = CodegenThingol.tracing;
val succeed = CodegenThingol.succeed;
val fail = CodegenThingol.fail;

(** code extraction **)

(* theory data *)

structure Code = CodeDataFun
(struct
  val name = "Pure/code";
  type T = CodegenThingol.code;
  val empty = CodegenThingol.empty_code;
  fun merge _ = CodegenThingol.merge_code;
  fun purge _ NONE _ = CodegenThingol.empty_code
    | purge NONE _ _ = CodegenThingol.empty_code
    | purge (SOME thy) (SOME cs) code =
        let
          val cs_exisiting =
            map_filter (CodegenNames.const_rev thy) (Graph.keys code);
        in
          Graph.del_nodes
            ((Graph.all_succs code
              o map (CodegenNames.const thy)
              o filter (member CodegenConsts.eq_const cs_exisiting)
              ) cs)
            code
        end;
end);

type appgen = theory -> ((sort -> sort) * Sorts.algebra) * Consts.T
  -> CodegenFuncgr.T
  -> bool * string list option
  -> (string * typ) * term list -> CodegenThingol.transact -> iterm * CodegenThingol.transact;

type appgens = (int * (appgen * stamp)) Symtab.table;
val merge_appgens : appgens * appgens -> appgens =
  Symtab.merge (fn ((bounds1, (_, stamp1)), (bounds2, (_, stamp2))) =>
    bounds1 = bounds2 andalso stamp1 = stamp2);

structure Consttab = CodegenConsts.Consttab;
type abstypes = typ Symtab.table * CodegenConsts.const Consttab.table;
fun merge_abstypes ((typs1, consts1) : abstypes, (typs2, consts2) : abstypes) =
  (Symtab.merge (Type.eq_type Vartab.empty) (typs1, typs2),
    Consttab.merge CodegenConsts.eq_const (consts1, consts2));

structure CodegenPackageData = TheoryDataFun
(struct
  val name = "Pure/codegen_package";
  type T = appgens * abstypes;
  val empty = (Symtab.empty, (Symtab.empty, Consttab.empty));
  val copy = I;
  val extend = I;
  fun merge _ ((appgens1, abstypes1), (appgens2, abstypes2)) =
    (merge_appgens (appgens1, appgens2), merge_abstypes (abstypes1, abstypes2));
  fun print _ _ = ();
end);

val _ = Context.add_setup (Code.init #> CodegenPackageData.init);


(* extraction kernel *)

fun check_strict (false, _) has_seri x =
      false
  | check_strict (_, SOME targets) has_seri x =
      not (has_seri targets x)
  | check_strict (true, _) has_seri x =
      true;

fun get_abstype thy (tyco, tys) = case Symtab.lookup ((fst o snd o CodegenPackageData.get) thy) tyco
 of SOME ty => SOME ((map_atyps (fn TFree (n, _) => nth tys (the (Int.fromString n)))) ty)
  | NONE => NONE;

fun ensure_def_class thy (algbr as ((proj_sort, _), _)) funcgr strct class trns =
  let
    val (v, cs) = (ClassPackage.the_consts_sign thy) class;
    val superclasses = (proj_sort o Sign.super_classes thy) class;
    val classops' = map (CodegenNames.const thy o CodegenConsts.norm_of_typ thy) cs;
    val class' = CodegenNames.class thy class;
    fun defgen_class trns =
      trns
      |> fold_map (ensure_def_class thy algbr funcgr strct) superclasses
      ||>> (fold_map (exprgen_type thy algbr funcgr strct) o map snd) cs
      |-> (fn (superclasses, classoptyps) => succeed
        (CodegenThingol.Class (superclasses,
          (unprefix "'" v, classops' ~~ classoptyps))))
  in
    trns
    |> tracing (fn _ => "generating class " ^ quote class)
    |> CodegenThingol.ensure_def defgen_class true
        ("generating class " ^ quote class) class'
    |> pair class'
  end
and ensure_def_tyco thy algbr funcgr strct tyco trns =
  let
    fun defgen_datatype trns =
      case CodegenData.get_datatype thy tyco
       of SOME (vs, cos) =>
            trns
            |> fold_map (exprgen_tyvar_sort thy algbr funcgr strct) vs
            ||>> fold_map (fn (c, tys) =>
              fold_map (exprgen_type thy algbr funcgr strct) tys
              #-> (fn tys' =>
                pair ((CodegenNames.const thy o CodegenConsts.norm_of_typ thy)
                  (c, tys ---> Type (tyco, map TFree vs)), tys'))) cos
            |-> (fn (vs, cos) => succeed (CodegenThingol.Datatype (vs, cos)))
        | NONE =>
            trns
            |> fail ("No such datatype: " ^ quote tyco)
    val tyco' = CodegenNames.tyco thy tyco;
    val strict = check_strict strct (CodegenSerializer.tyco_has_serialization thy) tyco';
  in
    trns
    |> tracing (fn _ => "generating type constructor " ^ quote tyco)
    |> CodegenThingol.ensure_def defgen_datatype strict
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
      case get_abstype thy (tyco, tys)
       of SOME ty =>
            trns
            |> exprgen_type thy algbr funcgr strct ty
        | NONE =>
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
and ensure_def_inst thy (algbr as ((proj_sort, _), _)) funcgr strct (class, tyco) trns =
  let
    val (vs, classop_defs) = ((apsnd o map) Const o ClassPackage.the_inst_sign thy)
      (class, tyco);
    val classops = (map (CodegenConsts.norm_of_typ thy) o snd
      o ClassPackage.the_consts_sign thy) class;
    val arity_typ = Type (tyco, (map TFree vs));
    val superclasses = (proj_sort o Sign.super_classes thy) class
    fun gen_superarity superclass trns =
      trns
      |> ensure_def_class thy algbr funcgr strct superclass
      ||>> exprgen_typinst thy algbr funcgr strct (arity_typ, [superclass])
      |-> (fn (superclass, [Instance (inst, iss)]) => pair (superclass, (inst, iss)));
    fun gen_classop_def (classop, t) trns =
      trns
      |> ensure_def_const thy algbr funcgr strct classop
      ||>> exprgen_term thy algbr funcgr strct t;
    fun defgen_inst trns =
      trns
      |> ensure_def_class thy algbr funcgr strct class
      ||>> ensure_def_tyco thy algbr funcgr strct tyco
      ||>> fold_map (exprgen_tyvar_sort thy algbr funcgr strct) vs
      ||>> fold_map gen_superarity superclasses
      ||>> fold_map gen_classop_def (classops ~~ classop_defs)
      |-> (fn ((((class, tyco), arity), superarities), classops) =>
             succeed (CodegenThingol.Classinst ((class, (tyco, arity)), (superarities, classops))));
    val inst = CodegenNames.instance thy (class, tyco);
  in
    trns
    |> tracing (fn _ => "generating instance " ^ quote class ^ " / " ^ quote tyco)
    |> CodegenThingol.ensure_def defgen_inst true
         ("generating instance " ^ quote class ^ " / " ^ quote tyco) inst
    |> pair inst
  end
and ensure_def_const thy (algbr as (_, consts)) funcgr strct (c, tys) trns =
  let
    val c' = CodegenNames.const thy (c, tys);
    fun defgen_datatypecons trns =
      trns
      |> ensure_def_tyco thy algbr funcgr strct
          ((the o CodegenData.get_datatype_of_constr thy) (c, tys))
      |-> (fn _ => succeed CodegenThingol.Bot);
    fun defgen_classop trns =
      trns
      |> ensure_def_class thy algbr funcgr strct ((the o AxClass.class_of_param thy) c)
      |-> (fn _ => succeed CodegenThingol.Bot);
    fun defgen_fun trns =
      case CodegenFuncgr.get_funcs funcgr
        (perhaps (Consttab.lookup ((snd o snd o CodegenPackageData.get) thy)) (c, tys))
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
              |> CodegenThingol.message msg (fn trns => trns
              |> fold_map (exprgen_eq o dest_eqthm) eq_thms
              ||>> fold_map (exprgen_tyvar_sort thy algbr funcgr strct) vs
              ||>> exprgen_type thy algbr funcgr strct ty
              |-> (fn ((eqs, vs), ty) => succeed (CodegenThingol.Fun (eqs, (vs, ty)))))
            end
        | [] =>
              trns
              |> fail ("No defining equations found for "
                   ^ (quote o CodegenConsts.string_of_const thy) (c, tys));
    val defgen =
      if CodegenNames.has_nsp CodegenNames.nsp_fun c'
      then defgen_fun
      else if CodegenNames.has_nsp CodegenNames.nsp_classop c'
      then defgen_classop
      else if CodegenNames.has_nsp CodegenNames.nsp_dtco c'
      then defgen_datatypecons
      else error ("Illegal shallow name space for constant: " ^ quote c');
    val strict = check_strict strct (CodegenSerializer.const_has_serialization thy) c';
  in
    trns
    |> tracing (fn _ => "generating constant "
        ^ (quote o CodegenConsts.string_of_const thy) (c, tys))
    |> CodegenThingol.ensure_def defgen strict ("generating constant "
         ^ CodegenConsts.string_of_const thy (c, tys)) c'
    |> pair c'
  end
and exprgen_term thy algbr funcgr strct (Const (c, ty)) trns =
      trns
      |> select_appgen thy algbr funcgr strct ((c, ty), [])
  | exprgen_term thy algbr funcgr strct (Var _) trns =
      error "Var encountered in term during code generation"
  | exprgen_term thy algbr funcgr strct (Free (v, ty)) trns =
      trns
      |> exprgen_type thy algbr funcgr strct ty
      |-> (fn _ => pair (IVar v))
  | exprgen_term thy algbr funcgr strct (Abs (raw_v, ty, raw_t)) trns =
      let
        val (v, t) = Syntax.variant_abs (CodegenNames.purify_var raw_v, ty, raw_t);
      in
        trns
        |> exprgen_type thy algbr funcgr strct ty
        ||>> exprgen_term thy algbr funcgr strct t
        |-> (fn (ty, t) => pair ((v, ty) `|-> t))
      end
  | exprgen_term thy algbr funcgr strct (t as _ $ _) trns =
      case strip_comb t
       of (Const (c, ty), ts) =>
            trns
            |> select_appgen thy algbr funcgr strct ((c, ty), ts)
            |-> (fn t => pair t)
        | (t', ts) =>
            trns
            |> exprgen_term thy algbr funcgr strct t'
            ||>> fold_map (exprgen_term thy algbr funcgr strct) ts
            |-> (fn (t, ts) => pair (t `$$ ts))
and appgen_default thy algbr funcgr strct ((c, ty), ts) trns =
  trns
  |> ensure_def_const thy algbr funcgr strct (CodegenConsts.norm_of_typ thy (c, ty))
  ||>> exprgen_type thy algbr funcgr strct ty
  ||>> exprgen_typinst_const thy algbr funcgr strct (c, ty)
  ||>> fold_map (exprgen_term thy algbr funcgr strct) ts
  |-> (fn (((c, ty), iss), ts) =>
         pair (IConst (c, (iss, ty)) `$$ ts))
and select_appgen thy algbr funcgr strct ((c, ty), ts) trns =
  case Symtab.lookup (fst (CodegenPackageData.get thy)) c
   of SOME (i, (appgen, _)) =>
        if length ts < i then
          let
            val tys = Library.take (i - length ts, ((fst o strip_type) ty));
            val vs = Name.names (Name.declare c Name.context) "a" tys;
          in
            trns
            |> fold_map (exprgen_type thy algbr funcgr strct) tys
            ||>> appgen thy algbr funcgr strct ((c, ty), ts @ map Free vs)
            |-> (fn (tys, t) => pair (map2 (fn (v, _) => pair v) vs tys `|--> t))
          end
        else if length ts > i then
          trns
          |> appgen thy algbr funcgr strct ((c, ty), Library.take (i, ts))
          ||>> fold_map (exprgen_term thy algbr funcgr strct) (Library.drop (i, ts))
          |-> (fn (t, ts) => pair (t `$$ ts))
        else
          trns
          |> appgen thy algbr funcgr strct ((c, ty), ts)
    | NONE =>
        trns
        |> appgen_default thy algbr funcgr strct ((c, ty), ts);


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
        |-> (fn t => pair (CodegenThingol.INum (i, t)))
    | NONE =>
        trns
        |> appgen_default thy algbr funcgr strct app;

fun appgen_char char_to_index thy algbr funcgr strct (app as ((_, ty), _)) trns =
  case (char_to_index o list_comb o apfst Const) app
   of SOME i =>
        trns
        |> exprgen_type thy algbr funcgr strct ty
        ||>> appgen_default thy algbr funcgr strct app
        |-> (fn (_, t0) => pair (IChar (chr i, t0)))
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
    val i = (length o fst o strip_type o Sign.the_const_type thy) c;
    val _ = Code.change thy (K CodegenThingol.empty_code);
  in
    (CodegenPackageData.map o apfst)
      (Symtab.update (c, (i, (appgen, stamp ())))) thy
  end;



(** abstype and constsubst interface **)

fun gen_abstyp prep_const prep_typ (raw_abstyp, raw_substtyp) raw_absconsts thy =
  let
    val abstyp = Type.no_tvars (prep_typ thy raw_abstyp);
    val substtyp = Type.no_tvars (prep_typ thy raw_substtyp);
    val absconsts = (map o pairself) (prep_const thy) raw_absconsts;
    val Type (abstyco, tys) = abstyp handle BIND => error ("bad type: " ^ Sign.string_of_typ thy abstyp);
    val typarms = map (fst o dest_TFree) tys handle MATCH => error ("bad type: " ^ Sign.string_of_typ thy abstyp);
    fun mk_index v = 
      let
        val k = find_index (fn w => v = w) typarms;
      in if k = ~1
        then error ("free type variable: " ^ quote v)
        else TFree (string_of_int k, [])
      end;
    val typpat = map_atyps (fn TFree (v, _) => mk_index v) substtyp;
    fun apply_typpat (Type (tyco, tys)) =
          let
            val tys' = map apply_typpat tys;
          in if tyco = abstyco then
            (map_atyps (fn TFree (n, _) => nth tys' (the (Int.fromString n)))) typpat
          else
            Type (tyco, tys')
          end
      | apply_typpat ty = ty;
    val string_of_typ = setmp show_sorts true (Sign.string_of_typ thy);
    fun add_consts (c1, c2) =
      let
        val _ = if CodegenNames.has_nsp CodegenNames.nsp_fun (CodegenNames.const thy c2)
          then ()
          else error ("not a function: " ^ CodegenConsts.string_of_const thy c2);
        val funcgr = CodegenFuncgr.mk_funcgr thy [c1, c2] [];
        val ty_map = CodegenFuncgr.get_func_typs funcgr;
        val ty1 = (apply_typpat o the o AList.lookup CodegenConsts.eq_const ty_map) c1;
        val ty2 = (the o AList.lookup CodegenConsts.eq_const ty_map) c2;
        val _ = if Sign.typ_equiv thy (ty1, ty2) then () else
          error ("Incompatiable type signatures of " ^ CodegenConsts.string_of_const thy c1
            ^ " and " ^ CodegenConsts.string_of_const thy c2 ^ ":\n"
            ^ string_of_typ ty1 ^ "\n" ^ string_of_typ ty2);
      in Consttab.update (c1, c2) end;
    val _ = Code.change thy (K CodegenThingol.empty_code);
  in
    thy
    |> (CodegenPackageData.map o apsnd) (fn (abstypes, abscs) =>
          (abstypes
          |> Symtab.update (abstyco, typpat),
          abscs
          |> fold add_consts absconsts)
       )
  end;

fun gen_constsubst prep_const raw_constsubsts thy =
  let
    val constsubsts = (map o pairself) (prep_const thy) raw_constsubsts;
    val string_of_typ = setmp show_sorts true (Sign.string_of_typ thy);
    fun add_consts (c1, c2) =
      let
        val _ = if CodegenNames.has_nsp CodegenNames.nsp_fun (CodegenNames.const thy c2)
          then ()
          else error ("not a function: " ^ CodegenConsts.string_of_const thy c2);
        val funcgr = CodegenFuncgr.mk_funcgr thy [c1, c2] [];
        val ty_map = CodegenFuncgr.get_func_typs funcgr;
        val ty1 = (the o AList.lookup CodegenConsts.eq_const ty_map) c1;
        val ty2 = (the o AList.lookup CodegenConsts.eq_const ty_map) c2;
        val _ = if Sign.typ_equiv thy (ty1, ty2) then () else
          error ("Incompatiable type signatures of " ^ CodegenConsts.string_of_const thy c1
            ^ " and " ^ CodegenConsts.string_of_const thy c2 ^ ":\n"
            ^ string_of_typ ty1 ^ "\n" ^ string_of_typ ty2);
      in Consttab.update (c1, c2) end;
    val _ = Code.change thy (K CodegenThingol.empty_code);
  in
    thy
    |> (CodegenPackageData.map o apsnd o apsnd) (fold add_consts constsubsts)
  end;

val abstyp = gen_abstyp CodegenConsts.norm Sign.certify_typ;
val abstyp_e = gen_abstyp CodegenConsts.read_const (fn thy => Sign.read_typ (thy, K NONE));

val constsubst = gen_constsubst CodegenConsts.norm;
val constsubst_e = gen_constsubst CodegenConsts.read_const;



(** code generation interfaces **)

fun generate thy (cs, rhss) targets init gen it =
  let
    val raw_funcgr = CodegenFuncgr.mk_funcgr thy cs rhss;
    val cs' = map_filter (Consttab.lookup ((snd o snd o CodegenPackageData.get) thy))
      (CodegenFuncgr.Constgraph.keys raw_funcgr);
    val funcgr = CodegenFuncgr.mk_funcgr thy cs' [];
    val qnaming = NameSpace.qualified_names NameSpace.default_naming;
    val algebr = ClassPackage.operational_algebra thy;
    val consttab = Consts.empty
      |> fold (fn (c, ty) => Consts.declare qnaming
           ((CodegenNames.const thy c, ty), true))
           (CodegenFuncgr.get_func_typs funcgr);
    val algbr = (algebr, consttab);
  in   
    Code.change_yield thy (CodegenThingol.start_transact init (gen thy algbr funcgr
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
    val seris' = map_filter (fn (target, args as _ :: _) =>
      SOME (CodegenSerializer.get_serializer thy (target, args)) | _ => NONE) seris;
    fun generate' thy = case cs
     of [] => []
      | _ =>
          generate thy (cs, []) targets NONE (fold_map oooo ensure_def_const') cs;
    fun serialize' [] code seri =
          seri NONE code 
      | serialize' cs code seri =
          seri (SOME cs) code;
    val cs = generate' thy;
    val code = Code.get thy;
  in
    (map (serialize' cs code) seris'; ())
  end;

val (codeK, code_abstypeK, code_constsubstK) =
  ("code_gen", "code_abstype", "code_constsubst");

in

val codeP =
  OuterSyntax.improper_command codeK "generate and serialize executable code for constants" K.diag (
    Scan.repeat P.term
    -- Scan.repeat (P.$$$ "(" |--
        P.name -- P.arguments
        --| P.$$$ ")")
    >> (fn (raw_cs, seris) => Toplevel.keep (code raw_cs seris o Toplevel.theory_of))
  );

val code_abstypeP =
  OuterSyntax.command code_abstypeK "axiomatic abstypes for code generation" K.thy_decl (
    (P.typ -- P.typ -- Scan.optional (P.$$$ "where" |-- Scan.repeat1
        (P.term --| (P.$$$ "\\<equiv>" || P.$$$ "==") -- P.term)) [])
    >> (Toplevel.theory o uncurry abstyp_e)
  );

val code_constsubstP =
  OuterSyntax.command code_constsubstK "axiomatic constant substitutions for code generation" K.thy_decl (
    Scan.repeat1 (P.term --| (P.$$$ "\\<equiv>" || P.$$$ "==") -- P.term)
    >> (Toplevel.theory o constsubst_e)
  );

val _ = OuterSyntax.add_parsers [codeP, code_abstypeP, code_constsubstP];

end; (* local *)

end; (* struct *)

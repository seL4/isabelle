(*  Title:      Pure/Tools/codegen_package.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Code generator extraction kernel. Code generator Isar setup.
*)

signature CODEGEN_PACKAGE =
sig
  include BASIC_CODEGEN_THINGOL;
  val codegen_term: theory -> term -> iterm;
  val eval_term: theory -> (string (*reference name!*) * 'a option ref) * term -> 'a;
  val codegen_command: theory -> string -> unit;

  type appgen;
  val add_appconst: string * appgen -> theory -> theory;
  val appgen_numeral: (term -> IntInf.int option) -> appgen;
  val appgen_char: (term -> int option) -> appgen;
  val appgen_case: (theory -> term
    -> ((string * typ) list * ((term * typ) * (term * term) list)) option)
    -> appgen;
  val appgen_let: appgen;

  val timing: bool ref;
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
          val dels = (Graph.all_preds code
              o map (CodegenNames.const thy)
              o filter (member CodegenConsts.eq_const cs_exisiting)
            ) cs;
        in Graph.del_nodes dels code end;
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
    val (v, cs) = AxClass.params_of_class thy class;
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
val timing = ref false;

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
    val ty_decl = Consts.the_declaration consts idf;
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
    val (vs, classop_defs) = ((apsnd o map) Const o CodegenConsts.instance_dict thy)
      (class, tyco);
    val classops = (map (CodegenConsts.norm_of_typ thy) o snd
      o AxClass.params_of_class thy) class;
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
and ensure_def_const thy (algbr as (_, consts)) funcgr strct (c_tys as (c, tys)) trns =
  let
    val c' = CodegenNames.const thy c_tys;
    fun defgen_datatypecons trns =
      trns
      |> ensure_def_tyco thy algbr funcgr strct
          ((the o CodegenData.get_datatype_of_constr thy) c_tys)
      |-> (fn _ => succeed CodegenThingol.Bot);
    fun defgen_classop trns =
      trns
      |> ensure_def_class thy algbr funcgr strct ((the o AxClass.class_of_param thy) c)
      |-> (fn _ => succeed CodegenThingol.Bot);
    fun defgen_fun trns =
      case CodegenFuncgr.funcs funcgr
        (perhaps (Consttab.lookup ((snd o snd o CodegenPackageData.get) thy)) c_tys)
       of eq_thms as eq_thm :: _ =>
            let
              val timeap = if !timing then Output.timeap_msg ("time for " ^ c')
                else I;
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
              |> timeap (fold_map (exprgen_eq o dest_eqthm) eq_thms)
              ||>> fold_map (exprgen_tyvar_sort thy algbr funcgr strct) vs
              ||>> exprgen_type thy algbr funcgr strct ty
              |-> (fn ((eqs, vs), ty) => succeed (CodegenThingol.Fun (eqs, (vs, ty)))))
            end
        | [] =>
              trns
              |> fail ("No defining equations found for "
                   ^ (quote o CodegenConsts.string_of_const thy) c_tys);
    val defgen = if (is_some o CodegenData.get_datatype_of_constr thy) c_tys
      then defgen_datatypecons
      else if (is_some o AxClass.class_of_param thy) c andalso
        case tys of [TFree _] => true | [TVar _] => true | _ => false
      then defgen_classop
      else defgen_fun
    val strict = check_strict strct (CodegenSerializer.const_has_serialization thy) c';
  in
    trns
    |> tracing (fn _ => "generating constant "
        ^ (quote o CodegenConsts.string_of_const thy) c_tys)
    |> CodegenThingol.ensure_def defgen strict ("generating constant "
         ^ CodegenConsts.string_of_const thy c_tys) c'
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
            val k = length ts;
            val tys = (curry Library.take (i - k) o curry Library.drop k o fst o strip_type) ty;
            val ctxt = (fold o fold_aterms)
              (fn Free (v, _) => Name.declare v | _ => I) ts Name.context;
            val vs = Name.names ctxt "a" tys;
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
  case int_of_numeral (list_comb (Const c, ts))
   of SOME i =>
        trns
        |> pair (CodegenThingol.INum i)
    | NONE =>
        trns
        |> appgen_default thy algbr funcgr strct app;

fun appgen_char char_to_index thy algbr funcgr strct (app as ((_, ty), _)) trns =
  case (char_to_index o list_comb o apfst Const) app
   of SOME i =>
        trns
        |> exprgen_type thy algbr funcgr strct ty
        |-> (fn _ => pair (IChar (chr i)))
    | NONE =>
        trns
        |> appgen_default thy algbr funcgr strct app;

val debug_term = ref (Bound 0);

fun appgen_case dest_case_expr thy algbr funcgr strct (app as (c_ty, ts)) trns =
  let
    val SOME ([], ((st, sty), ds)) = dest_case_expr thy (list_comb (Const c_ty, ts));
    fun fold_map_aterms f (t1 $ t2) s =
          s
          |> fold_map_aterms f t1
          ||>> fold_map_aterms f t2
          |-> (fn (t1, t2) => pair (t1 $ t2))
      | fold_map_aterms f (Abs (v, ty, t)) s =
          s
          |> fold_map_aterms f t
          |-> (fn t' => pair (Abs (v, ty, t')))
      | fold_map_aterms f a s = f a s;
    fun purify_term_frees (Free (v, ty)) (renaming, ctxt) = 
          let
            val ([v'], ctxt') = Name.variants [CodegenNames.purify_var v] ctxt;
            val renaming' = if v <> v' then Symtab.update (v, v') renaming else renaming;
          in (Free (v', ty), (renaming', ctxt')) end
      | purify_term_frees t ctxt = (t, ctxt);
    fun clausegen (raw_dt, raw_bt) trns =
      let
        val d_vs = map fst (Term.add_frees raw_dt []);
        val b_vs = map fst (Term.add_frees raw_bt []);
        val (dt, (renaming, ctxt)) =
          Name.context
          |> fold Name.declare (subtract (op =) d_vs b_vs)
          |> pair Symtab.empty
          |> fold_map_aterms purify_term_frees raw_dt;
        val bt = map_aterms (fn t as Free (v, ty) => Free (perhaps (Symtab.lookup renaming) v, ty)
                              | t => t) raw_bt;
      in
        trns
        |> exprgen_term thy algbr funcgr strct dt
        ||>> exprgen_term thy algbr funcgr strct bt
      end;
  in
    trns
    |> exprgen_term thy algbr funcgr strct st
    ||>> exprgen_type thy algbr funcgr strct sty
    ||>> fold_map clausegen ds
    |-> (fn ((se, sty), ds) => pair (ICase ((se, sty), ds)))
  end;

fun appgen_let thy algbr funcgr strct (app as (_, [st, ct])) trns =
  trns
  |> exprgen_term thy algbr funcgr strct ct
  ||>> exprgen_term thy algbr funcgr strct st
  |-> (fn ((v, ty) `|-> be, se) =>
            pair (ICase ((se, ty), case be
              of ICase ((IVar w, _), ds) => if v = w then ds else [(IVar v, be)]
               | _ => [(IVar v, be)]
            ))
        | _ => appgen_default thy algbr funcgr strct app);

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
        val funcgr = CodegenFuncgr.make thy [c1, c2];
        val ty1 = (apply_typpat o CodegenFuncgr.typ funcgr) c1;
        val ty2 = CodegenFuncgr.typ funcgr c2;
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
        val funcgr = CodegenFuncgr.make thy [c1, c2];
        val ty1 = CodegenFuncgr.typ funcgr c1;
        val ty2 = CodegenFuncgr.typ funcgr c2;
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

(* generic generation combinators *)

fun generate thy funcgr targets init gen it =
  let
    val cs = map_filter (Consttab.lookup ((snd o snd o CodegenPackageData.get) thy))
      (CodegenFuncgr.all funcgr);
    val funcgr' = CodegenFuncgr.make thy cs;
    val qnaming = NameSpace.qualified_names NameSpace.default_naming;
    val algebr = Sorts.project_algebra (Sign.pp thy)
      (the_default false o Option.map #operational o try (AxClass.get_definition thy)) (Sign.classes_of thy);
    val consttab = Consts.empty
      |> fold (fn c => Consts.declare qnaming
           ((CodegenNames.const thy c, CodegenFuncgr.typ funcgr' c), true))
           (CodegenFuncgr.all funcgr');
    val algbr = (algebr, consttab);
  in   
    Code.change_yield thy (CodegenThingol.start_transact init (gen thy algbr funcgr'
        (true, targets) it))
    |> fst
  end;

fun codegen_term thy t =
  let
    val ct = Thm.cterm_of thy t;
    val (ct', funcgr) = CodegenFuncgr.make_term thy (K K) ct;
    val t' = Thm.term_of ct';
  in generate thy funcgr (SOME []) NONE exprgen_term' t' end;

fun eval_term thy (ref_spec, t) =
  let
    val _ = (Term.fold_types o Term.fold_atyps) (fn _ =>
      error ("Term" ^ Sign.string_of_term thy t ^ "is polymorhpic"))
      t;
    val t' = codegen_term thy t;
  in CodegenSerializer.eval_term thy (ref_spec, t') (Code.get thy) end;


(* constant specifications with wildcards *)

fun consts_of thy thyname =
  let
    val this_thy = Option.map theory thyname |> the_default thy;
    val defs = (#defs o rep_theory) this_thy;
    val cs_names = (Symtab.keys o snd o #constants o Consts.dest o #consts o Sign.rep_sg) this_thy;
    val consts = maps (fn c => (map (fn tys => CodegenConsts.norm thy (c, tys))
      o map #lhs o filter #is_def o map snd o Defs.specifications_of defs) c) cs_names;
    fun is_const thyname (c, _) =
      (*this is an approximation*)
      not (exists (fn thy => Sign.declared_const thy c) (Theory.parents_of this_thy))
  in case thyname
   of NONE => consts
    | SOME thyname => filter (is_const thyname) consts
  end;

fun filter_generatable thy consts =
  let
    fun generatable const =
      case try (CodegenFuncgr.make thy) [const]
       of SOME funcgr => can
            (generate thy funcgr NONE NONE (fold_map oooo ensure_def_const')) [const]
        | NONE => false;
  in filter generatable consts end;

fun read_constspec thy "*" = filter_generatable thy (consts_of thy NONE)
  | read_constspec thy s = if String.isSuffix ".*" s
      then filter_generatable thy (consts_of thy (SOME (unsuffix ".*" s)))
      else [CodegenConsts.read_const thy s];


(** toplevel interface and setup **)

local

structure P = OuterParse
and K = OuterKeyword

fun code raw_cs seris thy =
  let
    val cs = maps (read_constspec thy) raw_cs;
    (*FIXME: assert serializer*)
    val seris' = map (fn (target, args as _ :: _) =>
          (target, SOME (CodegenSerializer.get_serializer thy target args))
      | (target, []) => (CodegenSerializer.assert_serializer thy target, NONE)) seris;
    fun generate' thy = case cs
     of [] => []
      | _ =>
          generate thy (CodegenFuncgr.make thy cs) (case map fst seris' of [] => NONE | xs => SOME xs)
            NONE (fold_map oooo ensure_def_const') cs;
    fun serialize' [] code seri =
          seri NONE code 
      | serialize' cs code seri =
          seri (SOME cs) code;
    val cs = generate' thy;
    val code = Code.get thy;
  in
    (map (serialize' cs code) (map_filter snd seris'); ())
  end;

val (codeK, code_abstypeK, code_axiomsK) =
  ("code_gen", "code_abstype", "code_axioms");

in

val code_bareP = (
    P.!!! (Scan.repeat P.term
    -- Scan.repeat (P.$$$ "(" |--
        P.name -- P.arguments
        --| P.$$$ ")"))
    >> (fn (raw_cs, seris) => code raw_cs seris)
  );

val codeP =
  OuterSyntax.improper_command codeK "generate and serialize executable code for constants"
    K.diag (code_bareP >> (fn f => Toplevel.keep (f o Toplevel.theory_of)));

fun codegen_command thy cmd =
  case Scan.read OuterLex.stopper code_bareP ((filter OuterLex.is_proper o OuterSyntax.scan) cmd)
   of SOME f => f thy
    | NONE => error ("bad directive " ^ quote cmd);

val code_abstypeP =
  OuterSyntax.command code_abstypeK "axiomatic abstypes for code generation" K.thy_decl (
    (P.typ -- P.typ -- Scan.optional (P.$$$ "where" |-- Scan.repeat1
        (P.term --| (P.$$$ "\\<equiv>" || P.$$$ "==") -- P.term)) [])
    >> (Toplevel.theory o uncurry abstyp_e)
  );

val code_axiomsP =
  OuterSyntax.command code_axiomsK "axiomatic constant equalities for code generation" K.thy_decl (
    Scan.repeat1 (P.term --| (P.$$$ "\\<equiv>" || P.$$$ "==") -- P.term)
    >> (Toplevel.theory o constsubst_e)
  );

val _ = OuterSyntax.add_parsers [codeP, code_abstypeP, code_axiomsP];

end; (* local *)

end; (* struct *)

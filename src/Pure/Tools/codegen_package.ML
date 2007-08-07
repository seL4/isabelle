(*  Title:      Pure/Tools/codegen_package.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Code generator translation kernel.  Code generator Isar setup.
*)

signature CODEGEN_PACKAGE =
sig
  (* interfaces *)
  val eval_conv: theory
    -> (CodegenThingol.code -> CodegenThingol.iterm -> cterm -> thm) -> cterm -> thm;
  val codegen_command: theory -> string -> unit;

  (* primitive interfaces *)
  val eval_term: theory -> (string (*reference name!*) * 'a option ref) * term -> 'a;
  val satisfies_ref: bool option ref;
  val satisfies: theory -> term -> string list -> bool;

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

structure CodegenPackage : CODEGEN_PACKAGE =
struct

open BasicCodegenThingol;
val tracing = CodegenThingol.tracing;
val succeed = CodegenThingol.succeed;
val fail = CodegenThingol.fail;

(** code translation **)

(* theory data *)

type appgen = theory -> ((sort -> sort) * Sorts.algebra) * Consts.T
  -> CodegenFuncgr.T
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

structure Translation = TheoryDataFun
(
  type T = appgens * abstypes;
  val empty = (Symtab.empty, (Symtab.empty, Consttab.empty));
  val copy = I;
  val extend = I;
  fun merge _ ((appgens1, abstypes1), (appgens2, abstypes2)) =
    (merge_appgens (appgens1, appgens2), merge_abstypes (abstypes1, abstypes2));
);

structure Funcgr = CodegenFuncgrRetrieval (fun rewrites thy = []);

fun code_depgr thy [] = Funcgr.make thy []
  | code_depgr thy consts =
      let
        val gr = Funcgr.make thy consts;
        val select = CodegenFuncgr.Constgraph.all_succs gr consts;
      in
        CodegenFuncgr.Constgraph.subgraph
          (member CodegenConsts.eq_const select) gr
      end;

fun code_thms thy =
  Pretty.writeln o CodegenFuncgr.pretty thy o code_depgr thy;

fun code_deps thy consts =
  let
    val gr = code_depgr thy consts;
    fun mk_entry (const, (_, (_, parents))) =
      let
        val name = CodegenConsts.string_of_const thy const;
        val nameparents = map (CodegenConsts.string_of_const thy) parents;
      in { name = name, ID = name, dir = "", unfold = true,
        path = "", parents = nameparents }
      end;
    val prgr = CodegenFuncgr.Constgraph.fold ((fn x => fn xs => xs @ [x]) o mk_entry) gr [];
  in Present.display_graph prgr end;

structure Code = CodeDataFun
(
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
);


(* translation kernel *)

fun get_abstype thy (tyco, tys) = case Symtab.lookup ((fst o snd o Translation.get) thy) tyco
 of SOME ty => SOME ((map_atyps (fn TFree (n, _) => nth tys (the (Int.fromString n)))) ty)
  | NONE => NONE;

fun ensure_def thy = CodegenThingol.ensure_def (CodegenNames.labelled_name thy);

fun ensure_def_class thy (algbr as ((_, algebra), _)) funcgr class =
  let
    val superclasses = (Sorts.certify_sort algebra o Sorts.super_classes algebra) class;
    val (v, cs) = AxClass.params_of_class thy class;
    val class' = CodegenNames.class thy class;
    val classrels' = map (curry (CodegenNames.classrel thy) class) superclasses;
    val classops' = map (CodegenNames.const thy o CodegenConsts.const_of_cexpr thy) cs;
    val defgen_class =
      fold_map (ensure_def_class thy algbr funcgr) superclasses
      ##>> (fold_map (exprgen_typ thy algbr funcgr) o map snd) cs
      #-> (fn (superclasses, classoptyps) => succeed
        (CodegenThingol.Class (superclasses ~~ classrels', (unprefix "'" v, classops' ~~ classoptyps))))
  in
    tracing (fn _ => "generating class " ^ quote class)
    #> ensure_def thy defgen_class ("generating class " ^ quote class) class'
    #> pair class'
  end
and ensure_def_classrel thy algbr funcgr (subclass, superclass) =
  ensure_def_class thy algbr funcgr subclass
  #>> (fn _ => CodegenNames.classrel thy (subclass, superclass))
and ensure_def_tyco thy algbr funcgr "fun" trns =
      trns
      |> pair "fun"
  | ensure_def_tyco thy algbr funcgr tyco trns =
      let
        fun defgen_datatype trns =
          let
            val (vs, cos) = CodegenData.get_datatype thy tyco;
          in
            trns
            |> fold_map (exprgen_tyvar_sort thy algbr funcgr) vs
            ||>> fold_map (fn (c, tys) =>
              fold_map (exprgen_typ thy algbr funcgr) tys
              #-> (fn tys' =>
                pair ((CodegenNames.const thy o CodegenConsts.const_of_cexpr thy)
                  (c, tys ---> Type (tyco, map TFree vs)), tys'))) cos
            |-> (fn (vs, cos) => succeed (CodegenThingol.Datatype (vs, cos)))
          end;
        val tyco' = CodegenNames.tyco thy tyco;
      in
        trns
        |> tracing (fn _ => "generating type constructor " ^ quote tyco)
        |> ensure_def thy defgen_datatype ("generating type constructor " ^ quote tyco) tyco'
        |> pair tyco'
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
      case get_abstype thy (tyco, tys)
       of SOME ty =>
            trns
            |> exprgen_typ thy algbr funcgr ty
        | NONE =>
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
    val c' = CodegenConsts.const_of_cexpr thy (c, ty_ctxt)
    val idf = CodegenNames.const thy c';
    val ty_decl = Consts.the_declaration consts idf;
    val (tys, tys_decl) = pairself (curry (Consts.typargs consts) idf) (ty_ctxt, ty_decl);
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
    fun gen_classop_def (classop as (c, ty)) trns =
      trns
      |> ensure_def_const thy algbr funcgr (CodegenConsts.const_of_cexpr thy classop)
      ||>> exprgen_term thy algbr funcgr (Const (c, map_type_tfree (K arity_typ) ty));
    fun defgen_inst trns =
      trns
      |> ensure_def_class thy algbr funcgr class
      ||>> ensure_def_tyco thy algbr funcgr tyco
      ||>> fold_map (exprgen_tyvar_sort thy algbr funcgr) vs
      ||>> fold_map gen_superarity superclasses
      ||>> fold_map gen_classop_def classops
      |-> (fn ((((class, tyco), arity), superarities), classops) =>
             succeed (CodegenThingol.Classinst ((class, (tyco, arity)), (superarities, classops))));
    val inst = CodegenNames.instance thy (class, tyco);
  in
    trns
    |> tracing (fn _ => "generating instance " ^ quote class ^ " / " ^ quote tyco)
    |> ensure_def thy defgen_inst ("generating instance " ^ quote class ^ " / " ^ quote tyco) inst
    |> pair inst
  end
and ensure_def_const thy (algbr as (_, consts)) funcgr (const as (c, opt_tyco)) trns =
  let
    val c' = CodegenNames.const thy const;
    fun defgen_datatypecons trns =
      trns
      |> ensure_def_tyco thy algbr funcgr
          ((the o CodegenData.get_datatype_of_constr thy) const)
      |-> (fn _ => succeed CodegenThingol.Bot);
    fun defgen_classop trns =
      trns
      |> ensure_def_class thy algbr funcgr ((the o AxClass.class_of_param thy) c)
      |-> (fn _ => succeed CodegenThingol.Bot);
    fun defgen_fun trns =
      let
        val const' = perhaps (Consttab.lookup ((snd o snd o Translation.get) thy)) const;
        val raw_thms = CodegenFuncgr.funcs funcgr const';
        val ty = (Logic.unvarifyT o CodegenFuncgr.typ funcgr) const';
        val thms = if (null o Term.typ_tfrees) ty orelse (null o fst o strip_type) ty
          then raw_thms
          else map (CodegenFunc.expand_eta 1) raw_thms;
        val timeap = if !timing then Output.timeap_msg ("time for " ^ c')
          else I;
        val msg = cat_lines ("generating code for theorems " :: map string_of_thm thms);
        val vs = (map dest_TFree o Consts.typargs consts) (c', ty);
        val dest_eqthm =
          apfst (snd o strip_comb) o Logic.dest_equals o Logic.unvarify o prop_of;
        fun exprgen_eq (args, rhs) trns =
          trns
          |> fold_map (exprgen_term thy algbr funcgr) args
          ||>> exprgen_term thy algbr funcgr rhs;
      in
        trns
        |> CodegenThingol.message msg (fn trns => trns
        |> timeap (fold_map (exprgen_eq o dest_eqthm) thms)
        ||>> fold_map (exprgen_tyvar_sort thy algbr funcgr) vs
        ||>> exprgen_typ thy algbr funcgr ty
        |-> (fn ((eqs, vs), ty) => succeed (CodegenThingol.Fun (eqs, (vs, ty)))))
      end;
    val defgen = if (is_some o CodegenData.get_datatype_of_constr thy) const
      then defgen_datatypecons
      else if is_some opt_tyco
        orelse (not o is_some o AxClass.class_of_param thy) c
      then defgen_fun
      else defgen_classop
  in
    trns
    |> tracing (fn _ => "generating constant "
        ^ (quote o CodegenConsts.string_of_const thy) const)
    |> ensure_def thy defgen ("generating constant " ^ CodegenConsts.string_of_const thy const) c'
    |> pair c'
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
  |> ensure_def_const thy algbr funcgr (CodegenConsts.const_of_cexpr thy (c, ty))
  ||>> fold_map (exprgen_typ thy algbr funcgr) ((fst o Term.strip_type) ty)
  ||>> exprgen_typ thy algbr funcgr ((snd o Term.strip_type) ty)
  ||>> exprgen_dict_parms thy algbr funcgr (c, ty)
  ||>> fold_map (exprgen_term thy algbr funcgr) ts
  |>> (fn ((((c, tys), ty), iss), ts) => IConst (c, (iss, tys)) `$$ ts)
and select_appgen thy algbr funcgr ((c, ty), ts) trns =
  case Symtab.lookup (fst (Translation.get thy)) c
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
    ^ CodegenConsts.string_of_typ thy ty
    ^ "\noccurs with type\n"
    ^ CodegenConsts.string_of_typ thy ty_decl);

fun perhaps_def_const thy algbr funcgr c trns =
  case try (ensure_def_const thy algbr funcgr c) trns
   of SOME (c, trns) => (SOME c, trns)
    | NONE => (NONE, trns);

fun exprgen_term' thy algbr funcgr t trns =
  exprgen_term thy algbr funcgr t trns
  handle CONSTRAIN ((c, ty), ty_decl) => error ("In term " ^ (quote o Sign.string_of_term thy) t
    ^ ",\nconstant " ^ c ^ " with most general type\n"
    ^ CodegenConsts.string_of_typ thy ty
    ^ "\noccurs with type\n"
    ^ CodegenConsts.string_of_typ thy ty_decl);


(* parametrized application generators, for instantiation in object logic *)
(* (axiomatic extensions of translation kernel) *)

fun appgen_case dest_case_expr thy algbr funcgr (app as (c_ty, ts)) =
  let
    val SOME ([], ((st, sty), ds)) = dest_case_expr thy (list_comb (Const c_ty, ts));
    fun clause_gen (dt, bt) =
      exprgen_term thy algbr funcgr dt
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
            ICase (CodegenThingol.collapse_let (((v, ty), se), be), t0)
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
    val _ = Code.change thy (K CodegenThingol.empty_code);
  in
    (Translation.map o apfst)
      (Symtab.update (c, (i, (appgen, stamp ())))) thy
  end;



(** abstype and constsubst interface **)

local

fun add_consts thy f (c1, c2 as (c, opt_tyco)) =
  let
    val _ = if
        is_some (AxClass.class_of_param thy c) andalso is_none opt_tyco
        orelse is_some (CodegenData.get_datatype_of_constr thy c2)
      then error ("Not a function: " ^ CodegenConsts.string_of_const thy c2)
      else ();
    val funcgr = Funcgr.make thy [c1, c2];
    val ty1 = (f o CodegenFuncgr.typ funcgr) c1;
    val ty2 = CodegenFuncgr.typ funcgr c2;
    val _ = if Sign.typ_equiv thy (ty1, ty2) then () else
      error ("Incompatiable type signatures of " ^ CodegenConsts.string_of_const thy c1
        ^ " and " ^ CodegenConsts.string_of_const thy c2 ^ ":\n"
        ^ CodegenConsts.string_of_typ thy ty1 ^ "\n" ^ CodegenConsts.string_of_typ thy ty2);
  in Consttab.update (c1, c2) end;

fun gen_abstyp prep_const prep_typ (raw_abstyp, raw_substtyp) raw_absconsts thy =
  let
    val abstyp = Type.no_tvars (prep_typ thy raw_abstyp);
    val substtyp = Type.no_tvars (prep_typ thy raw_substtyp);
    val absconsts = (map o pairself) (prep_const thy) raw_absconsts;
    val Type (abstyco, tys) = abstyp handle BIND => error ("Bad type: " ^ Sign.string_of_typ thy abstyp);
    val typarms = map (fst o dest_TFree) tys handle MATCH => error ("Bad type: " ^ Sign.string_of_typ thy abstyp);
    fun mk_index v = 
      let
        val k = find_index (fn w => v = w) typarms;
      in if k = ~1
        then error ("Free type variable: " ^ quote v)
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
    val _ = Code.change thy (K CodegenThingol.empty_code);
  in
    thy
    |> (Translation.map o apsnd) (fn (abstypes, abscs) =>
          (abstypes
          |> Symtab.update (abstyco, typpat),
          abscs
          |> fold (add_consts thy apply_typpat) absconsts)
       )
  end;

fun gen_constsubst prep_const raw_constsubsts thy =
  let
    val constsubsts = (map o pairself) (prep_const thy) raw_constsubsts;
    val _ = Code.change thy (K CodegenThingol.empty_code);
  in
    thy
    |> (Translation.map o apsnd o apsnd) (fold (add_consts thy I) constsubsts)
  end;

in

val abstyp = gen_abstyp (K I) Sign.certify_typ;
val abstyp_e = gen_abstyp CodegenConsts.read_const Sign.read_typ;

val constsubst = gen_constsubst (K I);
val constsubst_e = gen_constsubst CodegenConsts.read_const;

end; (*local*)


(** code generation interfaces **)

(* generic generation combinators *)

fun generate thy funcgr gen it =
  let
    (*FIXME*)
    val _ = Funcgr.intervene thy funcgr;
    val cs = map_filter (Consttab.lookup ((snd o snd o Translation.get) thy))
      (CodegenFuncgr.all funcgr);
    val funcgr' = Funcgr.make thy cs;
    val naming = NameSpace.qualified_names NameSpace.default_naming;
    val consttab = Consts.empty
      |> fold (fn c => Consts.declare naming
           ((CodegenNames.const thy c, CodegenFuncgr.typ funcgr' c), true))
           (CodegenFuncgr.all funcgr');
    val algbr = (CodegenData.operational_algebra thy, consttab);
  in   
    Code.change_yield thy
      (CodegenThingol.start_transact (gen thy algbr funcgr' it))
    |> fst
  end;

fun eval_conv thy conv =
  let
    fun conv' funcgr ct =
      let
        val t = generate thy funcgr exprgen_term' (Thm.term_of ct);
        val consts = CodegenThingol.fold_constnames (insert (op =)) t [];
        val code = Code.get thy
          |> CodegenThingol.project_code true [] (SOME consts)
      in conv code t ct end;
  in Funcgr.eval_conv thy conv' end;

fun codegen_term thy t =
  let
    val ct = Thm.cterm_of thy t;
    val (ct', funcgr) = Funcgr.make_term thy (K (K K)) ct;
    val t' = Thm.term_of ct';
  in generate thy funcgr exprgen_term' t' end;

fun raw_eval_term thy (ref_spec, t) args =
  let
    val _ = (Term.map_types o Term.map_atyps) (fn _ =>
      error ("Term " ^ Sign.string_of_term thy t ^ " contains polymorphic type"))
      t;
    val t' = codegen_term thy t;
  in
    CodegenSerializer.eval_term thy CodegenNames.labelled_name
      (Code.get thy) (ref_spec, t') args
  end;

val satisfies_ref : bool option ref = ref NONE;

fun eval_term thy t = raw_eval_term thy t [];
fun satisfies thy t witnesses = raw_eval_term thy
  (("CodegenPackage.satisfies_ref", satisfies_ref), t) witnesses;

fun filter_generatable thy consts =
  let
    val (consts', funcgr) = Funcgr.make_consts thy consts;
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
    val (perm1, cs) = CodegenConsts.read_const_exprs thy
      (filter_generatable thy) raw_cs;
    val (perm2, cs') = case generate thy (Funcgr.make thy cs) (fold_map ooo ensure_def_const') cs
     of [] => (true, NONE)
      | cs => (false, SOME cs);
    val code = Code.get thy;
    val seris' = map (fn (((target, module), file), args) =>
      CodegenSerializer.get_serializer thy target (perm1 orelse perm2) module file args
        CodegenNames.labelled_name cs') seris;
  in
    (map (fn f => f code) seris' : unit list; ())
  end;

fun code_thms_cmd thy =
  code_thms thy o snd o CodegenConsts.read_const_exprs thy (fst o Funcgr.make_consts thy);

fun code_deps_cmd thy =
  code_deps thy o snd o CodegenConsts.read_const_exprs thy (fst o Funcgr.make_consts thy);

val (inK, toK, fileK) = ("in", "to", "file");

val code_exprP =
  (Scan.repeat P.term
  -- Scan.repeat (P.$$$ inK |-- P.name
     -- Scan.option (P.$$$ toK |-- P.name)
     -- Scan.option (P.$$$ fileK |-- P.name)
     -- Scan.optional (P.$$$ "(" |-- P.arguments --| P.$$$ ")") []
  ) >> (fn (raw_cs, seris) => code raw_cs seris));

val _ = OuterSyntax.add_keywords [inK, toK, fileK];

val (codeK, code_abstypeK, code_axiomsK, code_thmsK, code_depsK) =
  ("code_gen", "code_abstype", "code_axioms", "code_thms", "code_deps");

in

val codeP =
  OuterSyntax.improper_command codeK "generate executable code for constants"
    K.diag (P.!!! code_exprP >> (fn f => Toplevel.keep (f o Toplevel.theory_of)));

fun codegen_command thy cmd =
  case Scan.read OuterLex.stopper (P.!!! code_exprP) ((filter OuterLex.is_proper o OuterSyntax.scan) cmd)
   of SOME f => (writeln "Now generating code..."; f thy)
    | NONE => error ("Bad directive " ^ quote cmd);

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

val _ = OuterSyntax.add_parsers [codeP, code_abstypeP, code_axiomsP, code_thmsP, code_depsP];

end; (* local *)

end; (* struct *)

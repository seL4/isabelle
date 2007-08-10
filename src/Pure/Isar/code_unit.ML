(*  Title:      Pure/Isar/code_unit.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Basic units of code generation:  Identifying (possibly overloaded) constants
by name plus optional type constructor.  Convenient data structures for constants.
Defining equations ("func"s).  Auxiliary.
*)

signature CODE_UNIT =
sig
  type const = string * string option (*constant name, possibly instance*)
  val const_ord: const * const -> order
  val eq_const: const * const -> bool
  structure Consttab: TABLE
  val const_of_cexpr: theory -> string * typ -> const
  val string_of_typ: theory -> typ -> string
  val string_of_const: theory -> const -> string
  val read_bare_const: theory -> string -> string * typ
  val read_const: theory -> string -> const
  val read_const_exprs: theory -> (const list -> const list)
    -> string list -> bool * const list

  val co_of_const: theory -> const
    -> string * ((string * sort) list * (string * typ list))
  val co_of_const': theory -> const
    -> (string * ((string * sort) list * (string * typ list))) option
  val cos_of_consts: theory -> const list
    -> string * ((string * sort) list * (string * typ list) list)
  val const_of_co: theory -> string -> (string * sort) list
    -> string * typ list -> const
  val consts_of_cos: theory -> string -> (string * sort) list
    -> (string * typ list) list -> const list
  val no_args: theory -> const -> int

  val typargs: theory -> string * typ -> typ list
  val typ_sort_inst: Sorts.algebra -> typ * sort
    -> sort Vartab.table -> sort Vartab.table

  val assert_rew: thm -> thm
  val mk_rew: thm -> thm
  val mk_func: thm -> thm
  val head_func: thm -> const * typ
  val bad_thm: string -> 'a
  val error_thm: (thm -> thm) -> thm -> thm
  val warning_thm: (thm -> thm) -> thm -> thm option

  val inst_thm: sort Vartab.table -> thm -> thm
  val expand_eta: int -> thm -> thm
  val rewrite_func: thm list -> thm -> thm
  val norm_args: thm list -> thm list 
  val norm_varnames: (string -> string) -> (string -> string) -> thm list -> thm list 
end;

structure CodeUnit: CODE_UNIT =
struct


(* auxiliary *)

exception BAD_THM of string;
fun bad_thm msg = raise BAD_THM msg;
fun error_thm f thm = f thm handle BAD_THM msg => error msg;
fun warning_thm f thm = SOME (f thm) handle BAD_THM msg
  => (warning ("code generator: " ^ msg); NONE);


(* basic data structures *)

type const = string * string option;
val const_ord = prod_ord fast_string_ord (option_ord string_ord);
val eq_const = is_equal o const_ord;

structure Consttab =
  TableFun(
    type key = const;
    val ord = const_ord;
  );

fun string_of_typ thy = setmp show_sorts true (Sign.string_of_typ thy);


(* conversion between constant expressions and constants *)

fun const_of_cexpr thy (c_ty as (c, _)) =
  case AxClass.class_of_param thy c
   of SOME class => (case Sign.const_typargs thy c_ty
       of [Type (tyco, _)] => if can (Sorts.mg_domain (Sign.classes_of thy) tyco) [class]
              then (c, SOME tyco)
              else (c, NONE)
        | [_] => (c, NONE))
    | NONE => (c, NONE);

fun string_of_const thy (c, NONE) = Sign.extern_const thy c
  | string_of_const thy (c, SOME tyco) = Sign.extern_const thy c
      ^ " " ^ enclose "[" "]" (Sign.extern_type thy tyco);


(* reading constants as terms and wildcards pattern *)

fun read_bare_const thy raw_t =
  let
    val t = Sign.read_term thy raw_t;
  in case try dest_Const t
   of SOME c_ty => c_ty
    | NONE => error ("Not a constant: " ^ Sign.string_of_term thy t)
  end;

fun read_const thy = const_of_cexpr thy o read_bare_const thy;

local

fun consts_of thy some_thyname =
  let
    val this_thy = Option.map theory some_thyname |> the_default thy;
    val cs = Symtab.fold (fn (c, (_, NONE)) => cons c | _ => I)
      ((snd o #constants o Consts.dest o #consts o Sign.rep_sg) this_thy) [];
    fun classop c = case AxClass.class_of_param thy c
     of NONE => [(c, NONE)]
      | SOME class => Symtab.fold
          (fn (tyco, classes) => if AList.defined (op =) classes class
            then cons (c, SOME tyco) else I)
          ((#arities o Sorts.rep_algebra o Sign.classes_of) this_thy)
          [(c, NONE)];
    val consts = maps classop cs;
    fun test_instance thy (class, tyco) =
      can (Sorts.mg_domain (Sign.classes_of thy) tyco) [class]
    fun belongs_here thyname (c, NONE) =
          not (exists (fn thy' => Sign.declared_const thy' c) (Theory.parents_of this_thy))
      | belongs_here thyname (c, SOME tyco) =
          let
            val SOME class = AxClass.class_of_param thy c
          in not (exists (fn thy' => test_instance thy' (class, tyco))
            (Theory.parents_of this_thy))
          end;
  in case some_thyname
   of NONE => consts
    | SOME thyname => filter (belongs_here thyname) consts
  end;

fun read_const_expr thy "*" = ([], consts_of thy NONE)
  | read_const_expr thy s = if String.isSuffix ".*" s
      then ([], consts_of thy (SOME (unsuffix ".*" s)))
      else ([read_const thy s], []);

in

fun read_const_exprs thy select exprs =
  case (pairself flat o split_list o map (read_const_expr thy)) exprs
   of (consts, []) => (false, consts)
    | (consts, consts') => (true, consts @ select consts');

end; (*local*)

(* conversion between constants, constant expressions and datatype constructors *)

fun const_of_co thy tyco vs (co, tys) =
  const_of_cexpr thy (co, tys ---> Type (tyco, map TFree vs));

fun consts_of_cos thy tyco vs cos =
  let
    val dty = Type (tyco, map TFree vs);
    fun mk_co (co, tys) = const_of_cexpr thy (co, tys ---> dty);
  in map mk_co cos end;

local

exception BAD of string;

fun mg_typ_of_const thy (c, NONE) = Sign.the_const_type thy c
  | mg_typ_of_const thy (c, SOME tyco) =
      let
        val SOME class = AxClass.class_of_param thy c;
        val ty = Sign.the_const_type thy c;
          (*an approximation*)
        val sorts = Sorts.mg_domain (Sign.classes_of thy) tyco [class]
          handle CLASS_ERROR => raise BAD ("No such instance: " ^ tyco ^ " :: " ^ class
            ^ ",\nrequired for overloaded constant " ^ c);
        val vs = Name.invents Name.context "'a" (length sorts);
      in map_atyps (K (Type (tyco, map (fn v => TVar ((v, 0), [])) vs))) ty end;

fun gen_co_of_const thy const =
  let
    val (c, _) = const;
    val ty = (Logic.unvarifyT o mg_typ_of_const thy) const;
    fun err () = raise BAD
      ("Illegal type for datatype constructor: " ^ string_of_typ thy ty);
    val (tys, ty') = strip_type ty;
    val (tyco, vs) = ((apsnd o map) dest_TFree o dest_Type) ty'
      handle TYPE _ => err ();
    val sorts = if has_duplicates (eq_fst op =) vs then err ()
      else map snd vs;
    val vs_names = Name.invent_list [] "'a" (length vs);
    val vs_map = map fst vs ~~ vs_names;
    val vs' = vs_names ~~ sorts;
    val tys' = (map o map_type_tfree) (fn (v, sort) =>
      (TFree ((the o AList.lookup (op =) vs_map) v, sort))) tys
      handle Option => err ();
  in (tyco, (vs', (c, tys'))) end;

in

fun co_of_const thy const = gen_co_of_const thy const handle BAD msg => error msg;
fun co_of_const' thy const = SOME (gen_co_of_const thy const) handle BAD msg => NONE;

fun no_args thy = length o fst o strip_type o mg_typ_of_const thy;

end;

fun cos_of_consts thy consts =
  let
    val raw_cos  = map (co_of_const thy) consts;
    val (tyco, (vs_names, sorts_cos)) = if (length o distinct (eq_fst op =)) raw_cos = 1
      then ((fst o hd) raw_cos, ((map fst o fst o snd o hd) raw_cos,
        map ((apfst o map) snd o snd) raw_cos))
      else error ("Term constructors not referring to the same type: "
        ^ commas (map (string_of_const thy) consts));
    val sorts = foldr1 ((uncurry o map2 o curry o Sorts.inter_sort) (Sign.classes_of thy))
      (map fst sorts_cos);
    val cos = map snd sorts_cos;
    val vs = vs_names ~~ sorts;
  in (tyco, (vs, cos)) end;


(* dictionary values *)

fun typargs thy (c_ty as (c, ty)) =
  let
    val opt_class = AxClass.class_of_param thy c;
    val tys = Sign.const_typargs thy (c, ty);
  in case (opt_class, tys)
   of (SOME class, ty as [Type (tyco, tys')]) =>
        if can (Sorts.mg_domain (Sign.classes_of thy) tyco) [class]
        then tys' else ty
    | _ => tys
  end;

fun typ_sort_inst algebra =
  let
    val inters = Sorts.inter_sort algebra;
    fun match _ [] = I
      | match (TVar (v, S)) S' = Vartab.map_default (v, []) (fn S'' => inters (S, inters (S', S'')))
      | match (Type (a, Ts)) S =
          fold2 match Ts (Sorts.mg_domain algebra a S)
  in uncurry match end;


(* making rewrite theorems *)

fun assert_rew thm =
  let
    val (lhs, rhs) = (Logic.dest_equals o Thm.plain_prop_of) thm
      handle TERM _ => bad_thm ("Not an equation: " ^ Display.string_of_thm thm)
          | THM _ => bad_thm ("Not an equation: " ^ Display.string_of_thm thm);
    fun vars_of t = fold_aterms
     (fn Var (v, _) => insert (op =) v
       | Free _ => bad_thm ("Illegal free variable in rewrite theorem\n"
           ^ Display.string_of_thm thm)
       | _ => I) t [];
    fun tvars_of t = fold_term_types
     (fn _ => fold_atyps (fn TVar (v, _) => insert (op =) v
                          | TFree _ => bad_thm 
      ("Illegal free type variable in rewrite theorem\n" ^ Display.string_of_thm thm))) t [];
    val lhs_vs = vars_of lhs;
    val rhs_vs = vars_of rhs;
    val lhs_tvs = tvars_of lhs;
    val rhs_tvs = tvars_of lhs;
    val _ = if null (subtract (op =) lhs_vs rhs_vs)
      then ()
      else bad_thm ("Free variables on right hand side of rewrite theorem\n"
        ^ Display.string_of_thm thm);
    val _ = if null (subtract (op =) lhs_tvs rhs_tvs)
      then ()
      else bad_thm ("Free type variables on right hand side of rewrite theorem\n"
        ^ Display.string_of_thm thm)
  in thm end;

fun mk_rew thm =
  let
    val thy = Thm.theory_of_thm thm;
    val ctxt = ProofContext.init thy;
  in
    thm
    |> LocalDefs.meta_rewrite_rule ctxt
    |> assert_rew
  end;


(* making defining equations *)

fun assert_func thm =
  let
    val thy = Thm.theory_of_thm thm;
    val (head, args) = (strip_comb o fst o Logic.dest_equals
      o ObjectLogic.drop_judgment thy o Thm.plain_prop_of) thm;
    val _ = case head of Const _ => () | _ =>
      bad_thm ("Equation not headed by constant\n" ^ Display.string_of_thm thm);
    val _ =
      if has_duplicates (op =)
        ((fold o fold_aterms) (fn Var (v, _) => cons v
          | _ => I
        ) args [])
      then bad_thm ("Duplicated variables on left hand side of equation\n"
        ^ Display.string_of_thm thm)
      else ()
    fun check _ (Abs _) = bad_thm
          ("Abstraction on left hand side of equation\n"
            ^ Display.string_of_thm thm)
      | check 0 (Var _) = ()
      | check _ (Var _) = bad_thm
          ("Variable with application on left hand side of defining equation\n"
            ^ Display.string_of_thm thm)
      | check n (t1 $ t2) = (check (n+1) t1; check 0 t2)
      | check n (Const (_, ty)) = if n <> (length o fst o strip_type) ty
          then bad_thm
            ("Partially applied constant on left hand side of equation\n"
               ^ Display.string_of_thm thm)
          else ();
    val _ = map (check 0) args;
  in thm end;

val mk_func = assert_func o mk_rew;

fun head_func thm =
  let
    val thy = Thm.theory_of_thm thm;
    val (Const (c_ty as (_, ty))) = (fst o strip_comb o fst o Logic.dest_equals
      o ObjectLogic.drop_judgment thy o Thm.plain_prop_of) thm;
    val const = const_of_cexpr thy c_ty;
  in (const, ty) end;


(* utilities *)

fun inst_thm tvars' thm =
  let
    val thy = Thm.theory_of_thm thm;
    val tvars = (Term.add_tvars o Thm.prop_of) thm [];
    fun mk_inst (tvar as (v, _)) = case Vartab.lookup tvars' v
     of SOME sort => SOME (pairself (Thm.ctyp_of thy o TVar) (tvar, (v, sort)))
      | NONE => NONE;
    val insts = map_filter mk_inst tvars;
  in Thm.instantiate (insts, []) thm end;

fun expand_eta k thm =
  let
    val thy = Thm.theory_of_thm thm;
    val (lhs, rhs) = (Logic.dest_equals o Thm.plain_prop_of) thm;
    val (head, args) = strip_comb lhs;
    val l = if k = ~1
      then (length o fst o strip_abs) rhs
      else Int.max (0, k - length args);
    val used = Name.make_context (map (fst o fst) (Term.add_vars lhs []));
    fun get_name _ 0 used = ([], used)
      | get_name (Abs (v, ty, t)) k used =
          used
          |> Name.variants [v]
          ||>> get_name t (k - 1)
          |>> (fn ([v'], vs') => (v', ty) :: vs')
      | get_name t k used = 
          let
            val (tys, _) = (strip_type o fastype_of) t
          in case tys
           of [] => raise TERM ("expand_eta", [t])
            | ty :: _ =>
                used
                |> Name.variants [""]
                |-> (fn [v] => get_name (t $ Var ((v, 0), ty)) (k - 1)
                #>> (fn vs' => (v, ty) :: vs'))
          end;
    val (vs, _) = get_name rhs l used;
    val vs_refl = map (fn (v, ty) => Thm.reflexive (Thm.cterm_of thy (Var ((v, 0), ty)))) vs;
  in
    thm
    |> fold (fn refl => fn thm => Thm.combination thm refl) vs_refl
    |> Conv.fconv_rule Drule.beta_eta_conversion
  end;

fun rewrite_func rewrites thm =
  let
    val rewrite = MetaSimplifier.rewrite false rewrites;
    val (ct_eq, [ct_lhs, ct_rhs]) = (Drule.strip_comb o Thm.cprop_of) thm;
    val Const ("==", _) = Thm.term_of ct_eq;
    val (ct_f, ct_args) = Drule.strip_comb ct_lhs;
    val rhs' = rewrite ct_rhs;
    val args' = map rewrite ct_args;
    val lhs' = Thm.symmetric (fold (fn th1 => fn th2 => Thm.combination th2 th1)
      args' (Thm.reflexive ct_f));
  in Thm.transitive (Thm.transitive lhs' thm) rhs' end;

fun norm_args thms =
  let
    val num_args_of = length o snd o strip_comb o fst o Logic.dest_equals;
    val k = fold (curry Int.max o num_args_of o Thm.plain_prop_of) thms 0;
  in
    thms
    |> map (expand_eta k)
    |> map (Conv.fconv_rule Drule.beta_eta_conversion)
  end;

fun canonical_tvars purify_tvar thm =
  let
    val ctyp = Thm.ctyp_of (Thm.theory_of_thm thm);
    fun tvars_subst_for thm = (fold_types o fold_atyps)
      (fn TVar (v_i as (v, _), sort) => let
            val v' = purify_tvar v
          in if v = v' then I
          else insert (op =) (v_i, (v', sort)) end
        | _ => I) (prop_of thm) [];
    fun mk_inst (v_i, (v', sort)) (maxidx, acc) =
      let
        val ty = TVar (v_i, sort)
      in
        (maxidx + 1, (ctyp ty, ctyp (TVar ((v', maxidx), sort))) :: acc)
      end;
    val maxidx = Thm.maxidx_of thm + 1;
    val (_, inst) = fold mk_inst (tvars_subst_for thm) (maxidx + 1, []);
  in Thm.instantiate (inst, []) thm end;

fun canonical_vars purify_var thm =
  let
    val cterm = Thm.cterm_of (Thm.theory_of_thm thm);
    fun vars_subst_for thm = fold_aterms
      (fn Var (v_i as (v, _), ty) => let
            val v' = purify_var v
          in if v = v' then I
          else insert (op =) (v_i, (v', ty)) end
        | _ => I) (prop_of thm) [];
    fun mk_inst (v_i as (v, i), (v', ty)) (maxidx, acc) =
      let
        val t = Var (v_i, ty)
      in
        (maxidx + 1, (cterm t, cterm (Var ((v', maxidx), ty))) :: acc)
      end;
    val maxidx = Thm.maxidx_of thm + 1;
    val (_, inst) = fold mk_inst (vars_subst_for thm) (maxidx + 1, []);
  in Thm.instantiate ([], inst) thm end;

fun canonical_absvars purify_var thm =
  let
    val t = Thm.plain_prop_of thm;
    val t' = Term.map_abs_vars purify_var t;
  in Thm.rename_boundvars t t' thm end;

fun norm_varnames purify_tvar purify_var thms =
  let
    fun burrow_thms f [] = []
      | burrow_thms f thms =
          thms
          |> Conjunction.intr_balanced
          |> f
          |> Conjunction.elim_balanced (length thms)
  in
    thms
    |> burrow_thms (canonical_tvars purify_tvar)
    |> map (canonical_vars purify_var)
    |> map (canonical_absvars purify_var)
    |> map Drule.zero_var_indexes
  end;

end;

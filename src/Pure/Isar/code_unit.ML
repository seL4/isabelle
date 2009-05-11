(*  Title:      Pure/Isar/code_unit.ML
    Author:     Florian Haftmann, TU Muenchen

Basic notions of code generation.  Auxiliary.
*)

signature CODE_UNIT =
sig
  (*generic non-sense*)
  val bad_thm: string -> 'a
  val error_thm: ('a -> 'b) -> 'a -> 'b
  val warning_thm: ('a -> 'b) -> 'a -> 'b option
  val try_thm: ('a -> 'b) -> 'a -> 'b option

  (*typ instantiations*)
  val typscheme: theory -> string * typ -> (string * sort) list * typ
  val inst_thm: theory -> sort Vartab.table -> thm -> thm
  val constrain_thm: theory -> sort -> thm -> thm

  (*constant aliasses*)
  val add_const_alias: thm -> theory -> theory
  val triv_classes: theory -> class list
  val resubst_alias: theory -> string -> string

  (*constants*)
  val string_of_typ: theory -> typ -> string
  val string_of_const: theory -> string -> string
  val no_args: theory -> string -> int
  val check_const: theory -> term -> string
  val read_bare_const: theory -> string -> string * typ
  val read_const: theory -> string -> string

  (*constructor sets*)
  val constrset_of_consts: theory -> (string * typ) list
    -> string * ((string * sort) list * (string * typ list) list)

  (*code equations*)
  val assert_eqn: theory -> thm -> thm
  val mk_eqn: theory -> thm -> thm * bool
  val assert_linear: (string -> bool) -> thm * bool -> thm * bool
  val const_eqn: theory -> thm -> string
  val const_typ_eqn: thm -> string * typ
  val typscheme_eqn: theory -> thm -> (string * sort) list * typ
  val expand_eta: theory -> int -> thm -> thm
  val rewrite_eqn: simpset -> thm -> thm
  val rewrite_head: thm list -> thm -> thm
  val norm_args: theory -> thm list -> thm list 
  val norm_varnames: theory -> thm list -> thm list

  (*case certificates*)
  val case_cert: thm -> string * (int * string list)
end;

structure Code_Unit: CODE_UNIT =
struct


(* auxiliary *)

exception BAD_THM of string;
fun bad_thm msg = raise BAD_THM msg;
fun error_thm f thm = f thm handle BAD_THM msg => error msg;
fun warning_thm f thm = SOME (f thm) handle BAD_THM msg
  => (warning ("code generator: " ^ msg); NONE);
fun try_thm f thm = SOME (f thm) handle BAD_THM _ => NONE;

fun string_of_typ thy = setmp show_sorts true (Syntax.string_of_typ_global thy);
fun string_of_const thy c = case AxClass.inst_of_param thy c
 of SOME (c, tyco) => Sign.extern_const thy c ^ " " ^ enclose "[" "]" (Sign.extern_type thy tyco)
  | NONE => Sign.extern_const thy c;

fun no_args thy = length o fst o strip_type o Sign.the_const_type thy;


(* utilities *)

fun typscheme thy (c, ty) =
  let
    val ty' = Logic.unvarifyT ty;
    fun dest (TFree (v, sort)) = (v, sort)
      | dest ty = error ("Illegal type parameter in type scheme: " ^ Syntax.string_of_typ_global thy ty);
    val vs = map dest (Sign.const_typargs thy (c, ty'));
  in (vs, Type.strip_sorts ty') end;

fun inst_thm thy tvars' thm =
  let
    val tvars = (Term.add_tvars o Thm.prop_of) thm [];
    val inter_sort = Sorts.inter_sort (Sign.classes_of thy);
    fun mk_inst (tvar as (v, sort)) = case Vartab.lookup tvars' v
     of SOME sort' => SOME (pairself (Thm.ctyp_of thy o TVar)
          (tvar, (v, inter_sort (sort, sort'))))
      | NONE => NONE;
    val insts = map_filter mk_inst tvars;
  in Thm.instantiate (insts, []) thm end;

fun constrain_thm thy sort thm =
  let
    val constrain = curry (Sorts.inter_sort (Sign.classes_of thy)) sort
    val tvars = (Term.add_tvars o Thm.prop_of) thm [];
    fun mk_inst (tvar as (v, sort)) = pairself (Thm.ctyp_of thy o TVar o pair v)
      (sort, constrain sort)
    val insts = map mk_inst tvars;
  in Thm.instantiate (insts, []) thm end;

fun expand_eta thy k thm =
  let
    val (lhs, rhs) = (Logic.dest_equals o Thm.plain_prop_of) thm;
    val (head, args) = strip_comb lhs;
    val l = if k = ~1
      then (length o fst o strip_abs) rhs
      else Int.max (0, k - length args);
    val used = Name.make_context (map (fst o fst) (Term.add_vars lhs []));
    fun get_name _ 0 = pair []
      | get_name (Abs (v, ty, t)) k =
          Name.variants [v]
          ##>> get_name t (k - 1)
          #>> (fn ([v'], vs') => (v', ty) :: vs')
      | get_name t k = 
          let
            val (tys, _) = (strip_type o fastype_of) t
          in case tys
           of [] => raise TERM ("expand_eta", [t])
            | ty :: _ =>
                Name.variants [""]
                #-> (fn [v] => get_name (t $ Var ((v, 0), ty)) (k - 1)
                #>> (fn vs' => (v, ty) :: vs'))
          end;
    val (vs, _) = get_name rhs l used;
    fun expand (v, ty) thm = Drule.fun_cong_rule thm
      (Thm.cterm_of thy (Var ((v, 0), ty)));
  in
    thm
    |> fold expand vs
    |> Conv.fconv_rule Drule.beta_eta_conversion
  end;

fun eqn_conv conv =
  let
    fun lhs_conv ct = if can Thm.dest_comb ct
      then (Conv.combination_conv lhs_conv conv) ct
      else Conv.all_conv ct;
  in Conv.combination_conv (Conv.arg_conv lhs_conv) conv end;

fun head_conv conv =
  let
    fun lhs_conv ct = if can Thm.dest_comb ct
      then (Conv.fun_conv lhs_conv) ct
      else conv ct;
  in Conv.fun_conv (Conv.arg_conv lhs_conv) end;

val rewrite_eqn = Conv.fconv_rule o eqn_conv o Simplifier.rewrite;
val rewrite_head = Conv.fconv_rule o head_conv o MetaSimplifier.rewrite false;

fun norm_args thy thms =
  let
    val num_args_of = length o snd o strip_comb o fst o Logic.dest_equals;
    val k = fold (curry Int.max o num_args_of o Thm.prop_of) thms 0;
  in
    thms
    |> map (expand_eta thy k)
    |> map (Conv.fconv_rule Drule.beta_eta_conversion)
  end;

fun canonical_tvars thy thm =
  let
    val ctyp = Thm.ctyp_of thy;
    val purify_tvar = unprefix "'" #> Name.desymbolize false #> prefix "'";
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

fun canonical_vars thy thm =
  let
    val cterm = Thm.cterm_of thy;
    val purify_var = Name.desymbolize false;
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

fun canonical_absvars thm =
  let
    val t = Thm.plain_prop_of thm;
    val purify_var = Name.desymbolize false;
    val t' = Term.map_abs_vars purify_var t;
  in Thm.rename_boundvars t t' thm end;

fun norm_varnames thy thms =
  let
    fun burrow_thms f [] = []
      | burrow_thms f thms =
          thms
          |> Conjunction.intr_balanced
          |> f
          |> Conjunction.elim_balanced (length thms)
  in
    thms
    |> map (canonical_vars thy)
    |> map canonical_absvars
    |> map Drule.zero_var_indexes
    |> burrow_thms (canonical_tvars thy)
    |> Drule.zero_var_indexes_list
  end;


(* const aliasses *)

structure ConstAlias = TheoryDataFun
(
  type T = ((string * string) * thm) list * class list;
  val empty = ([], []);
  val copy = I;
  val extend = I;
  fun merge _ ((alias1, classes1), (alias2, classes2)) : T =
    (Library.merge (eq_snd Thm.eq_thm_prop) (alias1, alias2),
      Library.merge (op =) (classes1, classes2));
);

fun add_const_alias thm thy =
  let
    val lhs_rhs = case try Logic.dest_equals (Thm.prop_of thm)
     of SOME lhs_rhs => lhs_rhs
      | _ => error ("Not an equation: " ^ Display.string_of_thm thm);
    val c_c' = case try (pairself (AxClass.unoverload_const thy o dest_Const)) lhs_rhs
     of SOME c_c' => c_c'
      | _ => error ("Not an equation with two constants: " ^ Display.string_of_thm thm);
    val some_class = the_list (AxClass.class_of_param thy (snd c_c'));
  in thy |>
    ConstAlias.map (fn (alias, classes) =>
      ((c_c', thm) :: alias, fold (insert (op =)) some_class classes))
  end;

fun resubst_alias thy =
  let
    val alias = fst (ConstAlias.get thy);
    val subst_inst_param = Option.map fst o AxClass.inst_of_param thy;
    fun subst_alias c =
      get_first (fn ((c', c''), _) => if c = c'' then SOME c' else NONE) alias;
  in
    perhaps subst_inst_param
    #> perhaps subst_alias
  end;

val triv_classes = snd o ConstAlias.get;


(* reading constants as terms *)

fun check_bare_const thy t = case try dest_Const t
 of SOME c_ty => c_ty
  | NONE => error ("Not a constant: " ^ Syntax.string_of_term_global thy t);

fun check_const thy = AxClass.unoverload_const thy o check_bare_const thy;

fun read_bare_const thy = check_bare_const thy o Syntax.read_term_global thy;

fun read_const thy = AxClass.unoverload_const thy o read_bare_const thy;


(* constructor sets *)

fun constrset_of_consts thy cs =
  let
    val _ = map (fn (c, _) => if (is_some o AxClass.class_of_param thy) c
      then error ("Is a class parameter: " ^ string_of_const thy c) else ()) cs;
    fun no_constr (c, ty) = error ("Not a datatype constructor: " ^ string_of_const thy c
      ^ " :: " ^ string_of_typ thy ty);
    fun last_typ c_ty ty =
      let
        val frees = OldTerm.typ_tfrees ty;
        val (tyco, vs) = ((apsnd o map) (dest_TFree) o dest_Type o snd o strip_type) ty
          handle TYPE _ => no_constr c_ty
        val _ = if has_duplicates (eq_fst (op =)) vs then no_constr c_ty else ();
        val _ = if length frees <> length vs then no_constr c_ty else ();
      in (tyco, vs) end;
    fun ty_sorts (c, ty) =
      let
        val ty_decl = (Logic.unvarifyT o Sign.the_const_type thy) c;
        val (tyco, _) = last_typ (c, ty) ty_decl;
        val (_, vs) = last_typ (c, ty) ty;
      in ((tyco, map snd vs), (c, (map fst vs, ty))) end;
    fun add ((tyco', sorts'), c) ((tyco, sorts), cs) =
      let
        val _ = if tyco' <> tyco
          then error "Different type constructors in constructor set"
          else ();
        val sorts'' = map2 (curry (Sorts.inter_sort (Sign.classes_of thy))) sorts' sorts
      in ((tyco, sorts), c :: cs) end;
    fun inst vs' (c, (vs, ty)) =
      let
        val the_v = the o AList.lookup (op =) (vs ~~ vs');
        val ty' = map_atyps (fn TFree (v, _) => TFree (the_v v)) ty;
      in (c, (fst o strip_type) ty') end;
    val c' :: cs' = map ty_sorts cs;
    val ((tyco, sorts), cs'') = fold add cs' (apsnd single c');
    val vs = Name.names Name.context Name.aT sorts;
    val cs''' = map (inst vs) cs'';
  in (tyco, (vs, rev cs''')) end;


(* code equations *)

fun assert_eqn thy thm =
  let
    val (lhs, rhs) = (Logic.dest_equals o Thm.plain_prop_of) thm
      handle TERM _ => bad_thm ("Not an equation: " ^ Display.string_of_thm thm)
          | THM _ => bad_thm ("Not an equation: " ^ Display.string_of_thm thm);
    fun vars_of t = fold_aterms (fn Var (v, _) => insert (op =) v
      | Free _ => bad_thm ("Illegal free variable in rewrite theorem\n"
          ^ Display.string_of_thm thm)
      | _ => I) t [];
    fun tvars_of t = fold_term_types (fn _ =>
      fold_atyps (fn TVar (v, _) => insert (op =) v
        | TFree _ => bad_thm 
      ("Illegal free type variable in rewrite theorem\n" ^ Display.string_of_thm thm))) t [];
    val lhs_vs = vars_of lhs;
    val rhs_vs = vars_of rhs;
    val lhs_tvs = tvars_of lhs;
    val rhs_tvs = tvars_of rhs;
    val _ = if null (subtract (op =) lhs_vs rhs_vs)
      then ()
      else bad_thm ("Free variables on right hand side of rewrite theorem\n"
        ^ Display.string_of_thm thm);
    val _ = if null (subtract (op =) lhs_tvs rhs_tvs)
      then ()
      else bad_thm ("Free type variables on right hand side of rewrite theorem\n"
        ^ Display.string_of_thm thm)    val (head, args) = (strip_comb o fst o Logic.dest_equals o Thm.plain_prop_of) thm;
    val (c, ty) = case head of Const c_ty => c_ty | _ =>
      bad_thm ("Equation not headed by constant\n" ^ Display.string_of_thm thm);
    fun check _ (Abs _) = bad_thm
          ("Abstraction on left hand side of equation\n"
            ^ Display.string_of_thm thm)
      | check 0 (Var _) = ()
      | check _ (Var _) = bad_thm
          ("Variable with application on left hand side of code equation\n"
            ^ Display.string_of_thm thm)
      | check n (t1 $ t2) = (check (n+1) t1; check 0 t2)
      | check n (Const (_, ty)) = if n <> (length o fst o strip_type) ty
          then bad_thm
            ("Partially applied constant on left hand side of equation\n"
               ^ Display.string_of_thm thm)
          else ();
    val _ = map (check 0) args;
    val ty_decl = Sign.the_const_type thy c;
    val _ = if Sign.typ_equiv thy (Type.strip_sorts ty_decl, Type.strip_sorts ty)
      then () else bad_thm ("Type\n" ^ string_of_typ thy ty
           ^ "\nof code equation\n"
           ^ Display.string_of_thm thm
           ^ "\nis incompatible with declared function type\n"
           ^ string_of_typ thy ty_decl)
  in thm end;

fun add_linear thm =
  let
    val (_, args) = (strip_comb o fst o Logic.dest_equals o Thm.plain_prop_of) thm;
    val linear = not (has_duplicates (op =)
      ((fold o fold_aterms) (fn Var (v, _) => cons v | _ => I) args []))
  in (thm, linear) end;

fun assert_pat is_cons thm =
  let
    val args = (snd o strip_comb o fst o Logic.dest_equals o Thm.plain_prop_of) thm;
    val _ = (map o map_aterms) (fn t as Const (c, _) => if is_cons c then t
          else bad_thm ("Not a constructor on left hand side of equation: "
            ^ quote c ^ ",\n in equation\n" ^ Display.string_of_thm thm)
      | t => t) args;
  in thm end;

fun assert_linear is_cons (thm, false) = (thm, false)
  | assert_linear is_cons (thm, true) = if snd (add_linear (assert_pat is_cons thm))
      then (thm, true)
      else bad_thm
        ("Duplicate variables on left hand side of code equation:\n"
          ^ Display.string_of_thm thm);

val const_typ_eqn = dest_Const o fst o strip_comb o fst o Logic.dest_equals o Thm.plain_prop_of;

fun typscheme_eqn thy = typscheme thy o const_typ_eqn;

(*permissive wrt. to overloaded constants!*)
fun mk_eqn thy = add_linear o assert_eqn thy o LocalDefs.meta_rewrite_rule (ProofContext.init thy);
fun const_eqn thy = AxClass.unoverload_const thy o const_typ_eqn;


(* case cerificates *)

fun case_certificate thm =
  let
    val ((head, raw_case_expr), cases) = (apfst Logic.dest_equals
      o apsnd Logic.dest_conjunctions o Logic.dest_implies o Thm.prop_of) thm;
    val _ = case head of Free _ => true
      | Var _ => true
      | _ => raise TERM ("case_cert", []);
    val ([(case_var, _)], case_expr) = Term.strip_abs_eta 1 raw_case_expr;
    val (Const (case_const, _), raw_params) = strip_comb case_expr;
    val n = find_index (fn Free (v, _) => v = case_var | _ => false) raw_params;
    val _ = if n = ~1 then raise TERM ("case_cert", []) else ();
    val params = map (fst o dest_Var) (nth_drop n raw_params);
    fun dest_case t =
      let
        val (head' $ t_co, rhs) = Logic.dest_equals t;
        val _ = if head' = head then () else raise TERM ("case_cert", []);
        val (Const (co, _), args) = strip_comb t_co;
        val (Var (param, _), args') = strip_comb rhs;
        val _ = if args' = args then () else raise TERM ("case_cert", []);
      in (param, co) end;
    fun analyze_cases cases =
      let
        val co_list = fold (AList.update (op =) o dest_case) cases [];
      in map (the o AList.lookup (op =) co_list) params end;
    fun analyze_let t =
      let
        val (head' $ arg, Var (param', _) $ arg') = Logic.dest_equals t;
        val _ = if head' = head then () else raise TERM ("case_cert", []);
        val _ = if arg' = arg then () else raise TERM ("case_cert", []);
        val _ = if [param'] = params then () else raise TERM ("case_cert", []);
      in [] end;
    fun analyze (cases as [let_case]) =
          (analyze_cases cases handle Bind => analyze_let let_case)
      | analyze cases = analyze_cases cases;
  in (case_const, (n, analyze cases)) end;

fun case_cert thm = case_certificate thm
  handle Bind => error "bad case certificate"
       | TERM _ => error "bad case certificate";

end;

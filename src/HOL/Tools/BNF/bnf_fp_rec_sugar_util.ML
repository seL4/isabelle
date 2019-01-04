(*  Title:      HOL/Tools/BNF/bnf_fp_rec_sugar_util.ML
    Author:     Lorenz Panny, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2013

Library for recursor and corecursor sugar.
*)

signature BNF_FP_REC_SUGAR_UTIL =
sig
  val error_at: Proof.context -> term list -> string -> 'a
  val warning_at: Proof.context -> term list -> string -> unit

  val excess_equations: Proof.context -> term list -> 'a
  val extra_variable_in_rhs: Proof.context -> term list -> term -> 'a
  val ill_formed_corec_call: Proof.context -> term -> 'a
  val ill_formed_equation_head: Proof.context -> term list -> 'a
  val ill_formed_equation_lhs_rhs: Proof.context -> term list -> 'a
  val ill_formed_equation: Proof.context -> term -> 'a
  val ill_formed_formula: Proof.context -> term -> 'a
  val ill_formed_rec_call: Proof.context -> term -> 'a
  val inconstant_pattern_pos_for_fun: Proof.context -> term list -> string -> 'a
  val invalid_map: Proof.context -> term list -> term -> 'a
  val missing_args_to_fun_on_lhs: Proof.context -> term list -> 'a
  val missing_equations_for_const: string -> 'a
  val missing_equations_for_fun: string -> 'a
  val missing_pattern: Proof.context -> term list -> 'a
  val more_than_one_nonvar_in_lhs: Proof.context -> term list -> 'a
  val multiple_equations_for_ctr: Proof.context -> term list -> 'a
  val nonprimitive_corec: Proof.context -> term list -> 'a
  val nonprimitive_pattern_in_lhs: Proof.context -> term list -> 'a
  val not_codatatype: Proof.context -> typ -> 'a
  val not_datatype: Proof.context -> typ -> 'a
  val not_constructor_in_pattern: Proof.context -> term list -> term -> 'a
  val not_constructor_in_rhs: Proof.context -> term list -> term -> 'a
  val rec_call_not_apply_to_ctr_arg: Proof.context -> term list -> term -> 'a
  val partially_applied_ctr_in_pattern: Proof.context -> term list -> 'a
  val partially_applied_ctr_in_rhs: Proof.context -> term list -> 'a
  val too_few_args_in_rec_call: Proof.context -> term list -> term -> 'a
  val unexpected_rec_call_in: Proof.context -> term list -> term -> 'a
  val unexpected_corec_call_in: Proof.context -> term list -> term -> 'a
  val unsupported_case_around_corec_call: Proof.context -> term list -> term -> 'a

  val no_equation_for_ctr_warning: Proof.context -> term list -> term -> unit

  val check_all_fun_arg_frees: Proof.context -> term list -> term list -> unit
  val check_duplicate_const_names: binding list -> unit
  val check_duplicate_variables_in_lhs: Proof.context -> term list -> term list -> unit
  val check_top_sort: Proof.context -> binding -> typ -> unit

  datatype fp_kind = Least_FP | Greatest_FP

  val case_fp: fp_kind -> 'a -> 'a -> 'a

  type fp_rec_sugar =
    {transfers: bool list,
     fun_names: string list,
     funs: term list,
     fun_defs: thm list,
     fpTs: typ list}

  val morph_fp_rec_sugar: morphism -> fp_rec_sugar -> fp_rec_sugar
  val transfer_fp_rec_sugar: theory -> fp_rec_sugar -> fp_rec_sugar

  val flat_rec_arg_args: 'a list list -> 'a list

  val indexed: 'a list -> int -> int list * int
  val indexedd: 'a list list -> int -> int list list * int
  val indexeddd: 'a list list list -> int -> int list list list * int
  val indexedddd: 'a list list list list -> int -> int list list list list * int
  val find_index_eq: ''a list -> ''a -> int
  val finds: ('a * 'b -> bool) -> 'a list -> 'b list -> ('a * 'b list) list * 'b list
  val find_indices: ('b * 'a -> bool) -> 'a list -> 'b list -> int list

  val order_strong_conn: ('a * 'a -> bool) -> ((('a * unit) * 'a list) list -> 'b) ->
    ('b -> 'a list) -> ('a * 'a list) list -> 'a list list -> 'a list list

  val mk_common_name: string list -> string

  val num_binder_types: typ -> int
  val exists_subtype_in: typ list -> typ -> bool
  val exists_strict_subtype_in: typ list -> typ -> bool
  val tvar_subst: theory -> typ list -> typ list -> ((string * int) * typ) list

  val retype_const_or_free: typ -> term -> term
  val drop_all: term -> term
  val permute_args: int -> term -> term

  val mk_partial_compN: int -> typ -> term -> term
  val mk_compN: int -> typ list -> term * term -> term
  val mk_comp: typ list -> term * term -> term

  val mk_co_rec: theory -> fp_kind -> typ list -> typ -> term -> term

  val mk_conjunctN: int -> int -> thm
  val conj_dests: int -> thm -> thm list

  val print_def_consts: bool -> (term * (string * thm)) list -> Proof.context -> unit
end;

structure BNF_FP_Rec_Sugar_Util : BNF_FP_REC_SUGAR_UTIL =
struct

fun error_at ctxt ats str =
  error (str ^ (if null ats then ""
    else " at\n" ^ cat_lines (map (prefix "  " o Syntax.string_of_term ctxt) ats)));
fun warning_at ctxt ats str =
  warning (str ^ (if null ats then ""
    else " at\n" ^ cat_lines (map (prefix "  " o Syntax.string_of_term ctxt) ats)));

fun excess_equations ctxt ats =
  error ("Excess equation(s):\n" ^
    cat_lines (map (prefix "  " o Syntax.string_of_term ctxt) ats));
fun extra_variable_in_rhs ctxt ats var =
  error_at ctxt ats ("Extra variable " ^ quote (Syntax.string_of_term ctxt var) ^
    " in right-hand side");
fun ill_formed_corec_call ctxt t =
  error ("Ill-formed corecursive call " ^ quote (Syntax.string_of_term ctxt t));
fun ill_formed_equation_head ctxt ats =
  error_at ctxt ats "Ill-formed function equation (expected function name on left-hand side)";
fun ill_formed_equation_lhs_rhs ctxt ats =
  error_at ctxt ats "Ill-formed equation (expected \"lhs = rhs\")";
fun ill_formed_equation ctxt t =
  error_at ctxt [] ("Ill-formed equation:\n  " ^ Syntax.string_of_term ctxt t);
fun ill_formed_formula ctxt t =
  error_at ctxt [] ("Ill-formed formula:\n  " ^ Syntax.string_of_term ctxt t);
fun ill_formed_rec_call ctxt t =
  error ("Ill-formed recursive call: " ^ quote (Syntax.string_of_term ctxt t));
fun inconstant_pattern_pos_for_fun ctxt ats fun_name =
  error_at ctxt ats ("Inconstant constructor pattern position for function " ^ quote fun_name);
fun invalid_map ctxt ats t =
  error_at ctxt ats ("Invalid map function in " ^ quote (Syntax.string_of_term ctxt t));
fun missing_args_to_fun_on_lhs ctxt ats =
  error_at ctxt ats "Expected more arguments to function on left-hand side";
fun missing_equations_for_const fun_name =
  error ("Missing equations for constant " ^ quote fun_name);
fun missing_equations_for_fun fun_name =
  error ("Missing equations for function " ^ quote fun_name);
fun missing_pattern ctxt ats =
  error_at ctxt ats "Constructor pattern missing in left-hand side";
fun more_than_one_nonvar_in_lhs ctxt ats =
  error_at ctxt ats "More than one non-variable argument in left-hand side";
fun multiple_equations_for_ctr ctxt ats =
  error ("Multiple equations for constructor:\n" ^
    cat_lines (map (prefix "  " o Syntax.string_of_term ctxt) ats));
fun nonprimitive_corec ctxt ats =
  error_at ctxt ats "Nonprimitive corecursive specification";
fun nonprimitive_pattern_in_lhs ctxt ats =
  error_at ctxt ats "Nonprimitive pattern in left-hand side";
fun not_codatatype ctxt T =
  error ("Not a codatatype: " ^ Syntax.string_of_typ ctxt T);
fun not_datatype ctxt T =
  error ("Not a datatype: " ^ Syntax.string_of_typ ctxt T);
fun not_constructor_in_pattern ctxt ats t =
  error_at ctxt ats ("Not a constructor " ^ quote (Syntax.string_of_term ctxt t) ^
    " in pattern");
fun not_constructor_in_rhs ctxt ats t =
  error_at ctxt ats ("Not a constructor " ^ quote (Syntax.string_of_term ctxt t) ^
    " in right-hand side");
fun rec_call_not_apply_to_ctr_arg ctxt ats t =
  error_at ctxt ats ("Recursive call not directly applied to constructor argument in " ^
    quote (Syntax.string_of_term ctxt t));
fun partially_applied_ctr_in_pattern ctxt ats =
  error_at ctxt ats "Partially applied constructor in pattern";
fun partially_applied_ctr_in_rhs ctxt ats =
  error_at ctxt ats "Partially applied constructor in right-hand side";
fun too_few_args_in_rec_call ctxt ats t =
  error_at ctxt ats ("Too few arguments in recursive call " ^ quote (Syntax.string_of_term ctxt t));
fun unexpected_rec_call_in ctxt ats t =
  error_at ctxt ats ("Unexpected recursive call in " ^ quote (Syntax.string_of_term ctxt t));
fun unexpected_corec_call_in ctxt ats t =
  error_at ctxt ats ("Unexpected corecursive call in " ^ quote (Syntax.string_of_term ctxt t));
fun unsupported_case_around_corec_call ctxt ats t =
  error_at ctxt ats ("Unsupported corecursive call under case expression " ^
    quote (Syntax.string_of_term ctxt t) ^
    "\n(Define datatype with discriminators and selectors to circumvent this limitation)");

fun no_equation_for_ctr_warning ctxt ats ctr =
  warning_at ctxt ats ("No equation for constructor " ^ quote (Syntax.string_of_term ctxt ctr));

fun check_all_fun_arg_frees ctxt ats fun_args =
  (case find_first (not o is_Free) fun_args of
    SOME t => error_at ctxt ats ("Non-variable function argument on left-hand side " ^
      quote (Syntax.string_of_term ctxt t))
  | NONE =>
    (case find_first (Variable.is_fixed ctxt o fst o dest_Free) fun_args of
      SOME t => error_at ctxt ats ("Function argument " ^
        quote (Syntax.string_of_term ctxt t) ^ " is fixed in context")
    | NONE => ()));

fun check_duplicate_const_names bs =
  let val dups = duplicates (op =) (map Binding.name_of bs) in
    ignore (null dups orelse error ("Duplicate constant name " ^ quote (hd dups)))
  end;

fun check_duplicate_variables_in_lhs ctxt ats vars =
  let val dups = duplicates (op aconv) vars in
    ignore (null dups orelse
      error_at ctxt ats ("Duplicable variable " ^ quote (Syntax.string_of_term ctxt (hd dups)) ^
        " in left-hand side"))
  end;

fun check_top_sort ctxt b T =
  ignore (Sign.of_sort (Proof_Context.theory_of ctxt) (T, \<^sort>\<open>type\<close>) orelse
    error ("Type of " ^ Binding.print b ^ " contains top sort"));

datatype fp_kind = Least_FP | Greatest_FP;

fun case_fp Least_FP l _ = l
  | case_fp Greatest_FP _ g = g;

type fp_rec_sugar =
  {transfers: bool list,
   fun_names: string list,
   funs: term list,
   fun_defs: thm list,
   fpTs: typ list};

fun morph_fp_rec_sugar phi ({transfers, fun_names, funs, fun_defs, fpTs} : fp_rec_sugar) =
  {transfers = transfers,
   fun_names = fun_names,
   funs = map (Morphism.term phi) funs,
   fun_defs = map (Morphism.thm phi) fun_defs,
   fpTs = map (Morphism.typ phi) fpTs};

val transfer_fp_rec_sugar = morph_fp_rec_sugar o Morphism.transfer_morphism;

fun flat_rec_arg_args xss =
  (* FIXME (once the old datatype package is completely phased out): The first line below gives the
     preferred order. The second line is for compatibility with the old datatype package. *)
  (* flat xss *)
  map hd xss @ maps tl xss;

fun indexe _ h = (h, h + 1);
fun indexed xs = fold_map indexe xs;
fun indexedd xss = fold_map indexed xss;
fun indexeddd xsss = fold_map indexedd xsss;
fun indexedddd xssss = fold_map indexeddd xssss;

fun find_index_eq hs h = find_index (curry (op =) h) hs;

fun finds eq = fold_map (fn x => List.partition (curry eq x) #>> pair x);

fun find_indices eq xs ys =
  map_filter I (map_index (fn (i, y) => if member eq xs y then SOME i else NONE) ys);

fun order_strong_conn eq make_graph topological_order deps sccs =
  let
    val normals = maps (fn x :: xs => map (fn y => (y, x)) xs) sccs;
    fun normal s = AList.lookup eq normals s |> the_default s;

    val normal_deps = deps
      |> map (fn (x, xs) => let val x' = normal x in
          (x', fold (insert eq o normal) xs [] |> remove eq x')
        end)
      |> AList.group eq
      |> map (apsnd (fn xss => fold (union eq) xss []));

    val normal_G = make_graph (map (apfst (rpair ())) normal_deps);
    val ordered_normals = rev (topological_order normal_G);
  in
    map (fn x => the (find_first (fn (y :: _) => eq (y, x)) sccs)) ordered_normals
  end;

val mk_common_name = space_implode "_";

fun num_binder_types (Type (\<^type_name>\<open>fun\<close>, [_, T])) = 1 + num_binder_types T
  | num_binder_types _ = 0;

val exists_subtype_in = Term.exists_subtype o member (op =);
fun exists_strict_subtype_in Ts T = exists_subtype_in (remove (op =) T Ts) T;

fun tvar_subst thy Ts Us =
  Vartab.fold (cons o apsnd snd) (fold (Sign.typ_match thy) (Ts ~~ Us) Vartab.empty) [];

fun retype_const_or_free T (Const (s, _)) = Const (s, T)
  | retype_const_or_free T (Free (s, _)) = Free (s, T)
  | retype_const_or_free _ t = raise TERM ("retype_const_or_free", [t]);

fun drop_all t =
  subst_bounds (strip_qnt_vars \<^const_name>\<open>Pure.all\<close> t |> map Free |> rev,
    strip_qnt_body \<^const_name>\<open>Pure.all\<close> t);

fun permute_args n t =
  list_comb (t, map Bound (0 :: (n downto 1))) |> fold (K (Term.abs (Name.uu, dummyT))) (0 upto n);

fun mk_partial_comp fT g = fst (Term.dest_comb (HOLogic.mk_comp (g, Free (Name.uu, fT))));

fun mk_partial_compN 0 _ g = g
  | mk_partial_compN n fT g = mk_partial_comp fT (mk_partial_compN (n - 1) (range_type fT) g);

fun mk_compN n bound_Ts (g, f) =
  let val typof = curry fastype_of1 bound_Ts in
    mk_partial_compN n (typof f) g $ f
  end;

val mk_comp = mk_compN 1;

fun mk_co_rec thy fp Cs fpT t =
  let
    val ((f_Cs, prebody), body) = strip_type (fastype_of t) |>> split_last;
    val fpT0 = case_fp fp prebody body;
    val Cs0 = distinct (op =) (map (case_fp fp body_type domain_type) f_Cs);
    val rho = tvar_subst thy (fpT0 :: Cs0) (fpT :: Cs);
  in
    Term.subst_TVars rho t
  end;

fun mk_conjunctN 1 1 = @{thm TrueE[OF TrueI]}
  | mk_conjunctN _ 1 = conjunct1
  | mk_conjunctN 2 2 = conjunct2
  | mk_conjunctN n m = conjunct2 RS (mk_conjunctN (n - 1) (m - 1));

fun conj_dests n thm = map (fn k => thm RS mk_conjunctN n k) (1 upto n);

fun print_def_consts int defs ctxt =
  Proof_Display.print_consts int (Position.thread_data ()) ctxt (K false)
    (map_filter (try (dest_Free o fst)) defs);

end;

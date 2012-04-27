(*  Title:      ZF/Tools/primrec_package.ML
    Author:     Norbert Voelker, FernUni Hagen
    Author:     Stefan Berghofer, TU Muenchen
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Package for defining functions on datatypes by primitive recursion.
*)

signature PRIMREC_PACKAGE =
sig
  val add_primrec: ((binding * string) * Attrib.src list) list -> theory -> theory * thm list
  val add_primrec_i: ((binding * term) * attribute list) list -> theory -> theory * thm list
end;

structure PrimrecPackage : PRIMREC_PACKAGE =
struct

exception RecError of string;

(*Remove outer Trueprop and equality sign*)
val dest_eqn = FOLogic.dest_eq o FOLogic.dest_Trueprop;

fun primrec_err s = error ("Primrec definition error:\n" ^ s);

fun primrec_eq_err sign s eq =
  primrec_err (s ^ "\nin equation\n" ^ Syntax.string_of_term_global sign eq);


(* preprocessing of equations *)

(*rec_fn_opt records equations already noted for this function*)
fun process_eqn thy (eq, rec_fn_opt) =
  let
    val (lhs, rhs) =
        if null (Term.add_vars eq []) then
            dest_eqn eq handle TERM _ => raise RecError "not a proper equation"
        else raise RecError "illegal schematic variable(s)";

    val (recfun, args) = strip_comb lhs;
    val (fname, ftype) = dest_Const recfun handle TERM _ =>
      raise RecError "function is not declared as constant in theory";

    val (ls_frees, rest)  = take_prefix is_Free args;
    val (middle, rs_frees) = take_suffix is_Free rest;

    val (constr, cargs_frees) =
      if null middle then raise RecError "constructor missing"
      else strip_comb (hd middle);
    val (cname, _) = dest_Const constr
      handle TERM _ => raise RecError "ill-formed constructor";
    val con_info = the (Symtab.lookup (ConstructorsData.get thy) cname)
      handle Option =>
      raise RecError "cannot determine datatype associated with function"

    val (ls, cargs, rs) = (map dest_Free ls_frees,
                           map dest_Free cargs_frees,
                           map dest_Free rs_frees)
      handle TERM _ => raise RecError "illegal argument in pattern";
    val lfrees = ls @ rs @ cargs;

    (*Constructor, frees to left of pattern, pattern variables,
      frees to right of pattern, rhs of equation, full original equation. *)
    val new_eqn = (cname, (rhs, cargs, eq))

  in
    if has_duplicates (op =) lfrees then
      raise RecError "repeated variable name in pattern"
    else if not (subset (op =) (Term.add_frees rhs [], lfrees)) then
      raise RecError "extra variables on rhs"
    else if length middle > 1 then
      raise RecError "more than one non-variable in pattern"
    else case rec_fn_opt of
        NONE => SOME (fname, ftype, ls, rs, con_info, [new_eqn])
      | SOME (fname', _, ls', rs', con_info': constructor_info, eqns) =>
          if AList.defined (op =) eqns cname then
            raise RecError "constructor already occurred as pattern"
          else if (ls <> ls') orelse (rs <> rs') then
            raise RecError "non-recursive arguments are inconsistent"
          else if #big_rec_name con_info <> #big_rec_name con_info' then
             raise RecError ("Mixed datatypes for function " ^ fname)
          else if fname <> fname' then
             raise RecError ("inconsistent functions for datatype " ^
                             #big_rec_name con_info)
          else SOME (fname, ftype, ls, rs, con_info, new_eqn::eqns)
  end
  handle RecError s => primrec_eq_err thy s eq;


(*Instantiates a recursor equation with constructor arguments*)
fun inst_recursor ((_ $ constr, rhs), cargs') =
    subst_atomic (#2 (strip_comb constr) ~~ map Free cargs') rhs;


(*Convert a list of recursion equations into a recursor call*)
fun process_fun thy (fname, ftype, ls, rs, con_info: constructor_info, eqns) =
  let
    val fconst = Const(fname, ftype)
    val fabs = list_comb (fconst, map Free ls @ [Bound 0] @ map Free rs)
    and {big_rec_name, constructors, rec_rewrites, ...} = con_info

    (*Replace X_rec(args,t) by fname(ls,t,rs) *)
    fun use_fabs (_ $ t) = subst_bound (t, fabs)
      | use_fabs t       = t

    val cnames         = map (#1 o dest_Const) constructors
    and recursor_pairs = map (dest_eqn o concl_of) rec_rewrites

    fun absterm (Free x, body) = absfree x body
      | absterm (t, body) = Abs("rec", Ind_Syntax.iT, abstract_over (t, body))

    (*Translate rec equations into function arguments suitable for recursor.
      Missing cases are replaced by 0 and all cases are put into order.*)
    fun add_case ((cname, recursor_pair), cases) =
      let val (rhs, recursor_rhs, eq) =
            case AList.lookup (op =) eqns cname of
                NONE => (warning ("no equation for constructor " ^ cname ^
                                  "\nin definition of function " ^ fname);
                         (Const (@{const_name zero}, Ind_Syntax.iT),
                          #2 recursor_pair, Const (@{const_name zero}, Ind_Syntax.iT)))
              | SOME (rhs, cargs', eq) =>
                    (rhs, inst_recursor (recursor_pair, cargs'), eq)
          val allowed_terms = map use_fabs (#2 (strip_comb recursor_rhs))
          val abs = List.foldr absterm rhs allowed_terms
      in
          if !Ind_Syntax.trace then
              writeln ("recursor_rhs = " ^
                       Syntax.string_of_term_global thy recursor_rhs ^
                       "\nabs = " ^ Syntax.string_of_term_global thy abs)
          else();
          if Logic.occs (fconst, abs) then
              primrec_eq_err thy
                   ("illegal recursive occurrences of " ^ fname)
                   eq
          else abs :: cases
      end

    val recursor = head_of (#1 (hd recursor_pairs))

    (** make definition **)

    (*the recursive argument*)
    val rec_arg =
      Free (singleton (Name.variant_list (map #1 (ls@rs))) (Long_Name.base_name big_rec_name),
        Ind_Syntax.iT)

    val def_tm = Logic.mk_equals
                    (subst_bound (rec_arg, fabs),
                     list_comb (recursor,
                                List.foldr add_case [] (cnames ~~ recursor_pairs))
                     $ rec_arg)

  in
      if !Ind_Syntax.trace then
            writeln ("primrec def:\n" ^
                     Syntax.string_of_term_global thy def_tm)
      else();
      (Long_Name.base_name fname ^ "_" ^ Long_Name.base_name big_rec_name ^ "_def",
       def_tm)
  end;


(* prepare functions needed for definitions *)

fun add_primrec_i args thy =
  let
    val ((eqn_names, eqn_terms), eqn_atts) = apfst split_list (split_list args);
    val SOME (fname, ftype, ls, rs, con_info, eqns) =
      List.foldr (process_eqn thy) NONE eqn_terms;
    val def = process_fun thy (fname, ftype, ls, rs, con_info, eqns);

    val ([def_thm], thy1) = thy
      |> Sign.add_path (Long_Name.base_name fname)
      |> Global_Theory.add_defs false [Thm.no_attributes (apfst Binding.name def)];

    val rewrites = def_thm :: map mk_meta_eq (#rec_rewrites con_info)
    val eqn_thms =
      eqn_terms |> map (fn t =>
        Goal.prove_global thy1 [] [] (Ind_Syntax.traceIt "next primrec equation = " thy1 t)
          (fn _ => EVERY [rewrite_goals_tac rewrites, rtac @{thm refl} 1]));

    val (eqn_thms', thy2) =
      thy1
      |> Global_Theory.add_thms ((eqn_names ~~ eqn_thms) ~~ eqn_atts);
    val (_, thy3) =
      thy2
      |> Global_Theory.add_thmss [((Binding.name "simps", eqn_thms'), [Simplifier.simp_add])]
      ||> Sign.parent_path;
  in (thy3, eqn_thms') end;

fun add_primrec args thy =
  add_primrec_i (map (fn ((name, s), srcs) =>
    ((name, Syntax.read_prop_global thy s), map (Attrib.attribute_cmd_global thy) srcs))
    args) thy;


(* outer syntax *)

val _ =
  Outer_Syntax.command @{command_spec "primrec"} "define primitive recursive functions on datatypes"
    (Scan.repeat1 (Parse_Spec.opt_thm_name ":" -- Parse.prop)
      >> (Toplevel.theory o (#1 oo (add_primrec o map Parse.triple_swap))));

end;


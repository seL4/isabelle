(*  Title:      ZF/Tools/primrec_package.ML
    ID:         $Id$
    Author:     Stefan Berghofer and Norbert Voelker
    Copyright   1998  TU Muenchen
    ZF version by Lawrence C Paulson (Cambridge)

Package for defining functions on datatypes by primitive recursion
*)

signature PRIMREC_PACKAGE =
sig
  val add_primrec_i : (string * term) list -> theory -> theory * thm list
  val add_primrec   : (string * string) list -> theory -> theory * thm list
end;

structure PrimrecPackage : PRIMREC_PACKAGE =
struct

exception RecError of string;

(*Remove outer Trueprop and equality sign*)
val dest_eqn = FOLogic.dest_eq o FOLogic.dest_Trueprop;

fun primrec_err s = error ("Primrec definition error:\n" ^ s);

fun primrec_eq_err sign s eq =
  primrec_err (s ^ "\nin equation\n" ^ Sign.string_of_term sign eq);

(* preprocessing of equations *)

(*rec_fn_opt records equations already noted for this function*)
fun process_eqn thy (eq, rec_fn_opt) = 
  let
    val (lhs, rhs) = 
	if null (term_vars eq) then
	    dest_eqn eq handle _ => raise RecError "not a proper equation"
	else raise RecError "illegal schematic variable(s)";

    val (recfun, args) = strip_comb lhs;
    val (fname, ftype) = dest_Const recfun handle _ => 
      raise RecError "function is not declared as constant in theory";

    val (ls_frees, rest)  = take_prefix is_Free args;
    val (middle, rs_frees) = take_suffix is_Free rest;

    val (constr, cargs_frees) = 
      if null middle then raise RecError "constructor missing"
      else strip_comb (hd middle);
    val (cname, _) = dest_Const constr
      handle _ => raise RecError "ill-formed constructor";
    val con_info = the (Symtab.lookup (ConstructorsData.get thy, cname))
      handle _ =>
      raise RecError "cannot determine datatype associated with function"

    val (ls, cargs, rs) = (map dest_Free ls_frees, 
			   map dest_Free cargs_frees, 
			   map dest_Free rs_frees)
      handle _ => raise RecError "illegal argument in pattern";
    val lfrees = ls @ rs @ cargs;

    (*Constructor, frees to left of pattern, pattern variables,
      frees to right of pattern, rhs of equation, full original equation. *)
    val new_eqn = (cname, (rhs, cargs, eq))

  in
    if not (null (duplicates lfrees)) then 
      raise RecError "repeated variable name in pattern" 
    else if not ((map dest_Free (term_frees rhs)) subset lfrees) then
      raise RecError "extra variables on rhs"
    else if length middle > 1 then 
      raise RecError "more than one non-variable in pattern"
    else case rec_fn_opt of
        None => Some (fname, ftype, ls, rs, con_info, [new_eqn])
      | Some (fname', _, ls', rs', con_info': constructor_info, eqns) => 
	  if is_some (assoc (eqns, cname)) then
	    raise RecError "constructor already occurred as pattern"
	  else if (ls <> ls') orelse (rs <> rs') then
	    raise RecError "non-recursive arguments are inconsistent"
	  else if #big_rec_name con_info <> #big_rec_name con_info' then
	     raise RecError ("Mixed datatypes for function " ^ fname)
	  else if fname <> fname' then
	     raise RecError ("inconsistent functions for datatype " ^ 
			     #big_rec_name con_info)
	  else Some (fname, ftype, ls, rs, con_info, new_eqn::eqns)
  end
  handle RecError s => primrec_eq_err (sign_of thy) s eq;


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

    fun absterm (Free(a,T), body) = absfree (a,T,body)
      | absterm (t,body) = Abs("rec", Ind_Syntax.iT, abstract_over (t, body))

    (*Translate rec equations into function arguments suitable for recursor.
      Missing cases are replaced by 0 and all cases are put into order.*)
    fun add_case ((cname, recursor_pair), cases) =
      let val (rhs, recursor_rhs, eq) = 
	    case assoc (eqns, cname) of
		None => (warning ("no equation for constructor " ^ cname ^
				  "\nin definition of function " ^ fname);
			 (Const ("0", Ind_Syntax.iT), 
			  #2 recursor_pair, Const ("0", Ind_Syntax.iT)))
	      | Some (rhs, cargs', eq) =>
		    (rhs, inst_recursor (recursor_pair, cargs'), eq)
	  val allowed_terms = map use_fabs (#2 (strip_comb recursor_rhs))
	  val abs = foldr absterm (allowed_terms, rhs)
      in 
          if !Ind_Syntax.trace then
	      writeln ("recursor_rhs = " ^ 
		       Sign.string_of_term (sign_of thy) recursor_rhs ^
		       "\nabs = " ^ Sign.string_of_term (sign_of thy) abs)
          else();
	  if Logic.occs (fconst, abs) then 
	      primrec_eq_err (sign_of thy) 
	           ("illegal recursive occurrences of " ^ fname)
		   eq
	  else abs :: cases
      end

    val recursor = head_of (#1 (hd recursor_pairs))

    (** make definition **)

    (*the recursive argument*)
    val rec_arg = Free (variant (map #1 (ls@rs)) (Sign.base_name big_rec_name),
			Ind_Syntax.iT)

    val def_tm = Logic.mk_equals
	            (subst_bound (rec_arg, fabs),
		     list_comb (recursor,
				foldr add_case (cnames ~~ recursor_pairs, []))
		     $ rec_arg)

  in
      if !Ind_Syntax.trace then
	    writeln ("primrec def:\n" ^ 
		     Sign.string_of_term (sign_of thy) def_tm)
      else();
      (Sign.base_name fname ^ "_" ^ Sign.base_name big_rec_name ^ "_def",
       def_tm)
  end;



(* prepare functions needed for definitions *)

(*Each equation is paired with an optional name, which is "_" (ML wildcard)
  if omitted.*)
fun add_primrec_i recursion_eqns thy =
  let
    val Some (fname, ftype, ls, rs, con_info, eqns) = 
	foldr (process_eqn thy) (map snd recursion_eqns, None);
    val def = process_fun thy (fname, ftype, ls, rs, con_info, eqns) 
    val (thy', [def_thm]) = thy |> Theory.add_path (Sign.base_name (#1 def))
                   |> (PureThy.add_defs_i false o map Thm.no_attributes) [def]
    val rewrites = def_thm :: map mk_meta_eq (#rec_rewrites con_info)
    val char_thms = 
	(if !Ind_Syntax.trace then	(* FIXME message / quiet_mode (!?) *)
	     writeln ("Proving equations for primrec function " ^ fname)
	 else ();
	 map (fn (_,t) =>
	      prove_goalw_cterm rewrites
		(Ind_Syntax.traceIt "next primrec equation = "
		 (cterm_of (sign_of thy') t))
	      (fn _ => [rtac refl 1]))
	 recursion_eqns);
    val simps = char_thms;
    val thy'' = thy' 
      |> (#1 o PureThy.add_thmss [(("simps", simps), [Simplifier.simp_add_global])])
      |> (#1 o PureThy.add_thms (map (rpair [])
         (filter_out (equal "_" o fst) (map fst recursion_eqns ~~ simps))))
      |> Theory.parent_path;
  in
    (thy'', char_thms)
  end;

fun add_primrec eqns thy =
  add_primrec_i (map (apsnd (Sign.simple_read_term (sign_of thy) propT)) eqns) thy;

end;

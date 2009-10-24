(* Author: Lukas Bulwahn, TU Muenchen

Auxilary functions for predicate compiler
*)

structure Predicate_Compile_Aux =
struct

(* syntactic functions *)
 
fun is_equationlike_term (Const ("==", _) $ _ $ _) = true
  | is_equationlike_term (Const ("Trueprop", _) $ (Const ("op =", _) $ _ $ _)) = true
  | is_equationlike_term _ = false
  
val is_equationlike = is_equationlike_term o prop_of 

fun is_pred_equation_term (Const ("==", _) $ u $ v) =
  (fastype_of u = @{typ bool}) andalso (fastype_of v = @{typ bool})
  | is_pred_equation_term _ = false
  
val is_pred_equation = is_pred_equation_term o prop_of 

fun is_intro_term constname t =
  case fst (strip_comb (HOLogic.dest_Trueprop (Logic.strip_imp_concl t))) of
    Const (c, _) => c = constname
  | _ => false
  
fun is_intro constname t = is_intro_term constname (prop_of t)

fun is_pred thy constname =
  let
    val T = (Sign.the_const_type thy constname)
  in body_type T = @{typ "bool"} end;
  

fun is_predT (T as Type("fun", [_, _])) = (snd (strip_type T) = HOLogic.boolT)
  | is_predT _ = false

  
(*** check if a term contains only constructor functions ***)
fun is_constrt thy =
  let
    val cnstrs = flat (maps
      (map (fn (_, (Tname, _, cs)) => map (apsnd (rpair Tname o length)) cs) o #descr o snd)
      (Symtab.dest (Datatype.get_all thy)));
    fun check t = (case strip_comb t of
        (Free _, []) => true
      | (Const (s, T), ts) => (case (AList.lookup (op =) cnstrs s, body_type T) of
            (SOME (i, Tname), Type (Tname', _)) => length ts = i andalso Tname = Tname' andalso forall check ts
          | _ => false)
      | _ => false)
  in check end;  
  
fun strip_ex (Const ("Ex", _) $ Abs (x, T, t)) =
  let
    val (xTs, t') = strip_ex t
  in
    ((x, T) :: xTs, t')
  end
  | strip_ex t = ([], t)

fun focus_ex t nctxt =
  let
    val ((xs, Ts), t') = apfst split_list (strip_ex t) 
    val (xs', nctxt') = Name.variants xs nctxt;
    val ps' = xs' ~~ Ts;
    val vs = map Free ps';
    val t'' = Term.subst_bounds (rev vs, t');
  in ((ps', t''), nctxt') end;


(* introduction rule combinators *)

(* combinators to apply a function to all literals of an introduction rules *)

(*
fun map_atoms f intro = 
*)

fun fold_atoms f intro s =
  let
    val (literals, head) = Logic.strip_horn intro
    fun appl t s = (case t of
      (@{term "Not"} $ t') => f t' s
      | _ => f t s)
  in fold appl (map HOLogic.dest_Trueprop literals) s end

fun fold_map_atoms f intro s =
  let
    val (literals, head) = Logic.strip_horn intro
    fun appl t s = (case t of
      (@{term "Not"} $ t') =>
        let
          val (t'', s') = f t' s
        in (@{term "Not"} $ t'', s') end
      | _ => f t s)
    val (literals', s') = fold_map appl (map HOLogic.dest_Trueprop literals) s
  in
    (Logic.list_implies (map HOLogic.mk_Trueprop literals', head), s')
  end;
  
(*
fun equals_conv lhs_cv rhs_cv ct =
  case Thm.term_of ct of
    Const ("==", _) $ _ $ _ => Conv.arg_conv cv ct  
  | _ => error "equals_conv"  
*)

(* Different options for compiler *)

datatype options = Options of {  
  (*check_modes : (string * int list list) list,*)
  show_steps : bool,
  show_mode_inference : bool,
  show_proof_trace : bool,
  show_intermediate_results : bool,
  (*
  inductify_functions : bool,
  *)
  inductify : bool,
  rpred : bool
};

fun show_steps (Options opt) = #show_steps opt
fun show_intermediate_results (Options opt) = #show_intermediate_results opt
fun show_proof_trace (Options opt) = #show_proof_trace opt

fun is_inductify (Options opt) = #inductify opt
fun is_rpred (Options opt) = #rpred opt


val default_options = Options {
  show_steps = false,
  show_intermediate_results = false,
  show_proof_trace = false,
  show_mode_inference = false,
  inductify = false,
  rpred = false
}


fun print_step options s =
  if show_steps options then tracing s else ()
  

(* tuple processing *)

fun expand_tuples thy intro =
  let
    fun rewrite_args [] (pats, intro_t, ctxt) = (pats, intro_t, ctxt)
      | rewrite_args (arg::args) (pats, intro_t, ctxt) = 
      (case HOLogic.strip_tupleT (fastype_of arg) of
        (Ts as _ :: _ :: _) =>
        let
          fun rewrite_arg' (Const ("Pair", _) $ _ $ t2, Type ("*", [_, T2]))
            (args, (pats, intro_t, ctxt)) = rewrite_arg' (t2, T2) (args, (pats, intro_t, ctxt))
            | rewrite_arg' (t, Type ("*", [T1, T2])) (args, (pats, intro_t, ctxt)) =
              let
                val ([x, y], ctxt') = Variable.variant_fixes ["x", "y"] ctxt
                val pat = (t, HOLogic.mk_prod (Free (x, T1), Free (y, T2)))
                val intro_t' = Pattern.rewrite_term thy [pat] [] intro_t
                val args' = map (Pattern.rewrite_term thy [pat] []) args
              in
                rewrite_arg' (Free (y, T2), T2) (args', (pat::pats, intro_t', ctxt'))
              end
            | rewrite_arg' _ (args, (pats, intro_t, ctxt)) = (args, (pats, intro_t, ctxt))
          val (args', (pats, intro_t', ctxt')) = rewrite_arg' (arg, fastype_of arg)
            (args, (pats, intro_t, ctxt))
        in
          rewrite_args args' (pats, intro_t', ctxt')
        end
      | _ => rewrite_args args (pats, intro_t, ctxt))
    fun rewrite_prem atom =
      let
        val (_, args) = strip_comb atom
      in rewrite_args args end
    val ctxt = ProofContext.init thy
    val (((T_insts, t_insts), [intro']), ctxt1) = Variable.import false [intro] ctxt
    val intro_t = prop_of intro'
    val concl = Logic.strip_imp_concl intro_t
    val (p, args) = strip_comb (HOLogic.dest_Trueprop concl)
    val (pats', intro_t', ctxt2) = rewrite_args args ([], intro_t, ctxt1)
    val (pats', intro_t', ctxt3) = 
      fold_atoms rewrite_prem intro_t' (pats', intro_t', ctxt2)
    fun rewrite_pat (ct1, ct2) =
      (ct1, cterm_of thy (Pattern.rewrite_term thy pats' [] (term_of ct2)))
    val t_insts' = map rewrite_pat t_insts
    val intro'' = Thm.instantiate (T_insts, t_insts') intro
    val [intro'''] = Variable.export ctxt3 ctxt [intro'']
    val intro'''' = Simplifier.full_simplify
      (HOL_basic_ss addsimps [@{thm fst_conv}, @{thm snd_conv}, @{thm Pair_eq}])
      intro'''
  in
    intro''''
  end



end;

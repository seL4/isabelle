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


end;

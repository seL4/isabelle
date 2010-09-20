(*  Title:      HOL/Tools/Predicate_Compile/predicate_compile_aux.ML
    Author:     Lukas Bulwahn, TU Muenchen

Auxilary functions for predicate compiler.
*)

signature PREDICATE_COMPILE_AUX =
sig
  (* general functions *)
  val apfst3 : ('a -> 'd) -> 'a * 'b * 'c -> 'd * 'b * 'c
  val apsnd3 : ('b -> 'd) -> 'a * 'b * 'c -> 'a * 'd * 'c
  val aptrd3 : ('c -> 'd) -> 'a * 'b * 'c -> 'a * 'b * 'd
  val find_indices : ('a -> bool) -> 'a list -> int list
  val assert : bool -> unit
  (* mode *)
  datatype mode = Bool | Input | Output | Pair of mode * mode | Fun of mode * mode
  val eq_mode : mode * mode -> bool
  val mode_ord: mode * mode -> order
  val list_fun_mode : mode list -> mode
  val strip_fun_mode : mode -> mode list
  val dest_fun_mode : mode -> mode list
  val dest_tuple_mode : mode -> mode list
  val all_modes_of_typ : typ -> mode list
  val all_smodes_of_typ : typ -> mode list
  val fold_map_aterms_prodT : ('a -> 'a -> 'a) -> (typ -> 'b -> 'a * 'b) -> typ -> 'b -> 'a * 'b
  val map_filter_prod : (term -> term option) -> term -> term option
  val replace_ho_args : mode -> term list -> term list -> term list
  val ho_arg_modes_of : mode -> mode list
  val ho_argsT_of : mode -> typ list -> typ list
  val ho_args_of : mode -> term list -> term list
  val ho_args_of_typ : typ -> term list -> term list
  val ho_argsT_of_typ : typ list -> typ list
  val split_map_mode : (mode -> term -> term option * term option)
    -> mode -> term list -> term list * term list
  val split_map_modeT : (mode -> typ -> typ option * typ option)
    -> mode -> typ list -> typ list * typ list
  val split_mode : mode -> term list -> term list * term list
  val split_modeT' : mode -> typ list -> typ list * typ list
  val string_of_mode : mode -> string
  val ascii_string_of_mode : mode -> string
  (* premises *)
  datatype indprem = Prem of term | Negprem of term | Sidecond of term
    | Generator of (string * typ)
  val dest_indprem : indprem -> term
  val map_indprem : (term -> term) -> indprem -> indprem
  (* general syntactic functions *)
  val conjuncts : term -> term list
  val is_equationlike : thm -> bool
  val is_pred_equation : thm -> bool
  val is_intro : string -> thm -> bool
  val is_predT : typ -> bool
  val is_constrt : theory -> term -> bool
  val is_constr : Proof.context -> string -> bool
  val focus_ex : term -> Name.context -> ((string * typ) list * term) * Name.context
  val strip_all : term -> (string * typ) list * term
  (* introduction rule combinators *)
  val map_atoms : (term -> term) -> term -> term
  val fold_atoms : (term -> 'a -> 'a) -> term -> 'a -> 'a
  val fold_map_atoms : (term -> 'a -> term * 'a) -> term -> 'a -> term * 'a
  val maps_premises : (term -> term list) -> term -> term
  val map_concl : (term -> term) -> term -> term
  val map_term : theory -> (term -> term) -> thm -> thm
  (* split theorems of case expressions *)
  val prepare_split_thm : Proof.context -> thm -> thm
  val find_split_thm : theory -> term -> thm option
  (* datastructures and setup for generic compilation *)
  datatype compilation_funs = CompilationFuns of {
    mk_predT : typ -> typ,
    dest_predT : typ -> typ,
    mk_bot : typ -> term,
    mk_single : term -> term,
    mk_bind : term * term -> term,
    mk_sup : term * term -> term,
    mk_if : term -> term,
    mk_iterate_upto : typ -> term * term * term -> term,
    mk_not : term -> term,
    mk_map : typ -> typ -> term -> term -> term
  };
  val mk_predT : compilation_funs -> typ -> typ
  val dest_predT : compilation_funs -> typ -> typ
  val mk_bot : compilation_funs -> typ -> term
  val mk_single : compilation_funs -> term -> term
  val mk_bind : compilation_funs -> term * term -> term
  val mk_sup : compilation_funs -> term * term -> term
  val mk_if : compilation_funs -> term -> term
  val mk_iterate_upto : compilation_funs -> typ -> term * term * term -> term
  val mk_not : compilation_funs -> term -> term
  val mk_map : compilation_funs -> typ -> typ -> term -> term -> term
  val funT_of : compilation_funs -> mode -> typ -> typ
  (* Different compilations *)
  datatype compilation = Pred | Depth_Limited | Random | Depth_Limited_Random | DSeq | Annotated
    | Pos_Random_DSeq | Neg_Random_DSeq | New_Pos_Random_DSeq | New_Neg_Random_DSeq
  val negative_compilation_of : compilation -> compilation
  val compilation_for_polarity : bool -> compilation -> compilation
  val string_of_compilation : compilation -> string
  val compilation_names : (string * compilation) list
  val non_random_compilations : compilation list
  val random_compilations : compilation list
  (* Different options for compiler *)
  datatype options = Options of {  
    expected_modes : (string * mode list) option,
    proposed_modes : (string * mode list) list,
    proposed_names : ((string * mode) * string) list,
    show_steps : bool,
    show_proof_trace : bool,
    show_intermediate_results : bool,
    show_mode_inference : bool,
    show_modes : bool,
    show_compilation : bool,
    show_caught_failures : bool,
    show_invalid_clauses : bool,
    skip_proof : bool,
    no_topmost_reordering : bool,
    function_flattening : bool,
    fail_safe_function_flattening : bool,
    specialise : bool,
    no_higher_order_predicate : string list,
    inductify : bool,
    detect_switches : bool,
    compilation : compilation
  };
  val expected_modes : options -> (string * mode list) option
  val proposed_modes : options -> string -> mode list option
  val proposed_names : options -> string -> mode -> string option
  val show_steps : options -> bool
  val show_proof_trace : options -> bool
  val show_intermediate_results : options -> bool
  val show_mode_inference : options -> bool
  val show_modes : options -> bool
  val show_compilation : options -> bool
  val show_caught_failures : options -> bool
  val show_invalid_clauses : options -> bool
  val skip_proof : options -> bool
  val no_topmost_reordering : options -> bool
  val function_flattening : options -> bool
  val fail_safe_function_flattening : options -> bool
  val specialise : options -> bool
  val no_higher_order_predicate : options -> string list
  val is_inductify : options -> bool
  val detect_switches : options -> bool
  val compilation : options -> compilation
  val default_options : options
  val bool_options : string list
  val print_step : options -> string -> unit
  (* simple transformations *)
  val expand_tuples : theory -> thm -> thm
  val eta_contract_ho_arguments : theory -> thm -> thm
  val remove_equalities : theory -> thm -> thm
  val remove_pointless_clauses : thm -> thm list
  val peephole_optimisation : theory -> thm -> thm option
  val define_quickcheck_predicate :
    term -> theory -> (((string * typ) * (string * typ) list) * thm) * theory 
end;

structure Predicate_Compile_Aux : PREDICATE_COMPILE_AUX =
struct

(* general functions *)

fun apfst3 f (x, y, z) = (f x, y, z)
fun apsnd3 f (x, y, z) = (x, f y, z)
fun aptrd3 f (x, y, z) = (x, y, f z)

fun comb_option f (SOME x1, SOME x2) = SOME (f (x1, x2))
  | comb_option f (NONE, SOME x2) = SOME x2
  | comb_option f (SOME x1, NONE) = SOME x1
  | comb_option f (NONE, NONE) = NONE

fun map2_optional f (x :: xs) (y :: ys) = f x (SOME y) :: (map2_optional f xs ys)
  | map2_optional f (x :: xs) [] = (f x NONE) :: (map2_optional f xs [])
  | map2_optional f [] [] = []

fun find_indices f xs =
  map_filter (fn (i, true) => SOME i | (i, false) => NONE) (map_index (apsnd f) xs)

fun assert check = if check then () else raise Fail "Assertion failed!"

(* mode *)

datatype mode = Bool | Input | Output | Pair of mode * mode | Fun of mode * mode

(* equality of instantiatedness with respect to equivalences:
  Pair Input Input == Input and Pair Output Output == Output *)
fun eq_mode (Fun (m1, m2), Fun (m3, m4)) = eq_mode (m1, m3) andalso eq_mode (m2, m4)
  | eq_mode (Pair (m1, m2), Pair (m3, m4)) = eq_mode (m1, m3) andalso eq_mode (m2, m4)
  | eq_mode (Pair (m1, m2), Input) = eq_mode (m1, Input) andalso eq_mode (m2, Input)
  | eq_mode (Pair (m1, m2), Output) = eq_mode (m1, Output) andalso eq_mode (m2, Output)
  | eq_mode (Input, Pair (m1, m2)) = eq_mode (Input, m1) andalso eq_mode (Input, m2)
  | eq_mode (Output, Pair (m1, m2)) = eq_mode (Output, m1) andalso eq_mode (Output, m2)
  | eq_mode (Input, Input) = true
  | eq_mode (Output, Output) = true
  | eq_mode (Bool, Bool) = true
  | eq_mode _ = false

fun mode_ord (Input, Output) = LESS
  | mode_ord (Output, Input) = GREATER
  | mode_ord (Input, Input) = EQUAL
  | mode_ord (Output, Output) = EQUAL
  | mode_ord (Bool, Bool) = EQUAL
  | mode_ord (Pair (m1, m2), Pair (m3, m4)) = prod_ord mode_ord mode_ord ((m1, m2), (m3, m4))
  | mode_ord (Fun (m1, m2), Fun (m3, m4)) = prod_ord mode_ord mode_ord ((m1, m2), (m3, m4))
 
fun list_fun_mode [] = Bool
  | list_fun_mode (m :: ms) = Fun (m, list_fun_mode ms)

(* name: binder_modes? *)
fun strip_fun_mode (Fun (mode, mode')) = mode :: strip_fun_mode mode'
  | strip_fun_mode Bool = []
  | strip_fun_mode _ = raise Fail "Bad mode for strip_fun_mode"

(* name: strip_fun_mode? *)
fun dest_fun_mode (Fun (mode, mode')) = mode :: dest_fun_mode mode'
  | dest_fun_mode mode = [mode]

fun dest_tuple_mode (Pair (mode, mode')) = mode :: dest_tuple_mode mode'
  | dest_tuple_mode _ = []

fun all_modes_of_typ' (T as Type ("fun", _)) = 
  let
    val (S, U) = strip_type T
  in
    if U = HOLogic.boolT then
      fold_rev (fn m1 => fn m2 => map_product (curry Fun) m1 m2)
        (map all_modes_of_typ' S) [Bool]
    else
      [Input, Output]
  end
  | all_modes_of_typ' (Type (@{type_name Product_Type.prod}, [T1, T2])) = 
    map_product (curry Pair) (all_modes_of_typ' T1) (all_modes_of_typ' T2)
  | all_modes_of_typ' _ = [Input, Output]

fun all_modes_of_typ (T as Type ("fun", _)) =
    let
      val (S, U) = strip_type T
    in
      if U = @{typ bool} then
        fold_rev (fn m1 => fn m2 => map_product (curry Fun) m1 m2)
          (map all_modes_of_typ' S) [Bool]
      else
        raise Fail "Invocation of all_modes_of_typ with a non-predicate type"
    end
  | all_modes_of_typ @{typ bool} = [Bool]
  | all_modes_of_typ T =
    raise Fail "Invocation of all_modes_of_typ with a non-predicate type"

fun all_smodes_of_typ (T as Type ("fun", _)) =
  let
    val (S, U) = strip_type T
    fun all_smodes (Type (@{type_name Product_Type.prod}, [T1, T2])) = 
      map_product (curry Pair) (all_smodes T1) (all_smodes T2)
      | all_smodes _ = [Input, Output]
  in
    if U = HOLogic.boolT then
      fold_rev (fn m1 => fn m2 => map_product (curry Fun) m1 m2) (map all_smodes S) [Bool]
    else
      raise Fail "invalid type for predicate"
  end

fun ho_arg_modes_of mode =
  let
    fun ho_arg_mode (m as Fun _) =  [m]
      | ho_arg_mode (Pair (m1, m2)) = ho_arg_mode m1 @ ho_arg_mode m2
      | ho_arg_mode _ = []
  in
    maps ho_arg_mode (strip_fun_mode mode)
  end

fun ho_args_of mode ts =
  let
    fun ho_arg (Fun _) (SOME t) = [t]
      | ho_arg (Fun _) NONE = raise Fail "mode and term do not match"
      | ho_arg (Pair (m1, m2)) (SOME (Const (@{const_name Pair}, _) $ t1 $ t2)) =
          ho_arg m1 (SOME t1) @ ho_arg m2 (SOME t2)
      | ho_arg (Pair (m1, m2)) NONE = ho_arg m1 NONE @ ho_arg m2 NONE
      | ho_arg _ _ = []
  in
    flat (map2_optional ho_arg (strip_fun_mode mode) ts)
  end

fun ho_args_of_typ T ts =
  let
    fun ho_arg (T as Type("fun", [_,_])) (SOME t) = if body_type T = @{typ bool} then [t] else []
      | ho_arg (Type("fun", [_,_])) NONE = raise Fail "mode and term do not match"
      | ho_arg (Type(@{type_name "Product_Type.prod"}, [T1, T2]))
         (SOME (Const (@{const_name Pair}, _) $ t1 $ t2)) =
          ho_arg T1 (SOME t1) @ ho_arg T2 (SOME t2)
      | ho_arg (Type(@{type_name "Product_Type.prod"}, [T1, T2])) NONE =
          ho_arg T1 NONE @ ho_arg T2 NONE
      | ho_arg _ _ = []
  in
    flat (map2_optional ho_arg (binder_types T) ts)
  end

fun ho_argsT_of_typ Ts =
  let
    fun ho_arg (T as Type("fun", [_,_])) = if body_type T = @{typ bool} then [T] else []
      | ho_arg (Type(@{type_name "Product_Type.prod"}, [T1, T2])) =
          ho_arg T1 @ ho_arg T2
      | ho_arg _ = []
  in
    maps ho_arg Ts
  end
  

(* temporary function should be replaced by unsplit_input or so? *)
fun replace_ho_args mode hoargs ts =
  let
    fun replace (Fun _, _) (arg' :: hoargs') = (arg', hoargs')
      | replace (Pair (m1, m2), Const (@{const_name Pair}, T) $ t1 $ t2) hoargs =
        let
          val (t1', hoargs') = replace (m1, t1) hoargs
          val (t2', hoargs'') = replace (m2, t2) hoargs'
        in
          (Const (@{const_name Pair}, T) $ t1' $ t2', hoargs'')
        end
      | replace (_, t) hoargs = (t, hoargs)
  in
    fst (fold_map replace (strip_fun_mode mode ~~ ts) hoargs)
  end

fun ho_argsT_of mode Ts =
  let
    fun ho_arg (Fun _) T = [T]
      | ho_arg (Pair (m1, m2)) (Type (@{type_name Product_Type.prod}, [T1, T2])) = ho_arg m1 T1 @ ho_arg m2 T2
      | ho_arg _ _ = []
  in
    flat (map2 ho_arg (strip_fun_mode mode) Ts)
  end

(* splits mode and maps function to higher-order argument types *)
fun split_map_mode f mode ts =
  let
    fun split_arg_mode' (m as Fun _) t = f m t
      | split_arg_mode' (Pair (m1, m2)) (Const (@{const_name Pair}, _) $ t1 $ t2) =
        let
          val (i1, o1) = split_arg_mode' m1 t1
          val (i2, o2) = split_arg_mode' m2 t2
        in
          (comb_option HOLogic.mk_prod (i1, i2), comb_option HOLogic.mk_prod (o1, o2))
        end
      | split_arg_mode' m t =
        if eq_mode (m, Input) then (SOME t, NONE)
        else if eq_mode (m, Output) then (NONE,  SOME t)
        else raise Fail "split_map_mode: mode and term do not match"
  in
    (pairself (map_filter I) o split_list) (map2 split_arg_mode' (strip_fun_mode mode) ts)
  end

(* splits mode and maps function to higher-order argument types *)
fun split_map_modeT f mode Ts =
  let
    fun split_arg_mode' (m as Fun _) T = f m T
      | split_arg_mode' (Pair (m1, m2)) (Type (@{type_name Product_Type.prod}, [T1, T2])) =
        let
          val (i1, o1) = split_arg_mode' m1 T1
          val (i2, o2) = split_arg_mode' m2 T2
        in
          (comb_option HOLogic.mk_prodT (i1, i2), comb_option HOLogic.mk_prodT (o1, o2))
        end
      | split_arg_mode' Input T = (SOME T, NONE)
      | split_arg_mode' Output T = (NONE,  SOME T)
      | split_arg_mode' _ _ = raise Fail "split_modeT': mode and type do not match"
  in
    (pairself (map_filter I) o split_list) (map2 split_arg_mode' (strip_fun_mode mode) Ts)
  end

fun split_mode mode ts = split_map_mode (fn _ => fn _ => (NONE, NONE)) mode ts

fun fold_map_aterms_prodT comb f (Type (@{type_name Product_Type.prod}, [T1, T2])) s =
  let
    val (x1, s') = fold_map_aterms_prodT comb f T1 s
    val (x2, s'') = fold_map_aterms_prodT comb f T2 s'
  in
    (comb x1 x2, s'')
  end
  | fold_map_aterms_prodT comb f T s = f T s

fun map_filter_prod f (Const (@{const_name Pair}, _) $ t1 $ t2) =
  comb_option HOLogic.mk_prod (map_filter_prod f t1, map_filter_prod f t2)
  | map_filter_prod f t = f t

(* obviously, split_mode' and split_modeT' do not match? where does that cause problems? *)
  
fun split_modeT' mode Ts =
  let
    fun split_arg_mode' (Fun _) T = ([], [])
      | split_arg_mode' (Pair (m1, m2)) (Type (@{type_name Product_Type.prod}, [T1, T2])) =
        let
          val (i1, o1) = split_arg_mode' m1 T1
          val (i2, o2) = split_arg_mode' m2 T2
        in
          (i1 @ i2, o1 @ o2)
        end
      | split_arg_mode' Input T = ([T], [])
      | split_arg_mode' Output T = ([], [T])
      | split_arg_mode' _ _ = raise Fail "split_modeT': mode and type do not match"
  in
    (pairself flat o split_list) (map2 split_arg_mode' (strip_fun_mode mode) Ts)
  end

fun string_of_mode mode =
  let
    fun string_of_mode1 Input = "i"
      | string_of_mode1 Output = "o"
      | string_of_mode1 Bool = "bool"
      | string_of_mode1 mode = "(" ^ (string_of_mode3 mode) ^ ")"
    and string_of_mode2 (Pair (m1, m2)) = string_of_mode3 m1 ^ " * " ^  string_of_mode2 m2
      | string_of_mode2 mode = string_of_mode1 mode
    and string_of_mode3 (Fun (m1, m2)) = string_of_mode2 m1 ^ " => " ^ string_of_mode3 m2
      | string_of_mode3 mode = string_of_mode2 mode
  in string_of_mode3 mode end

fun ascii_string_of_mode mode' =
  let
    fun ascii_string_of_mode' Input = "i"
      | ascii_string_of_mode' Output = "o"
      | ascii_string_of_mode' Bool = "b"
      | ascii_string_of_mode' (Pair (m1, m2)) =
          "P" ^ ascii_string_of_mode' m1 ^ ascii_string_of_mode'_Pair m2
      | ascii_string_of_mode' (Fun (m1, m2)) = 
          "F" ^ ascii_string_of_mode' m1 ^ ascii_string_of_mode'_Fun m2 ^ "B"
    and ascii_string_of_mode'_Fun (Fun (m1, m2)) =
          ascii_string_of_mode' m1 ^ (if m2 = Bool then "" else "_" ^ ascii_string_of_mode'_Fun m2)
      | ascii_string_of_mode'_Fun Bool = "B"
      | ascii_string_of_mode'_Fun m = ascii_string_of_mode' m
    and ascii_string_of_mode'_Pair (Pair (m1, m2)) =
          ascii_string_of_mode' m1 ^ ascii_string_of_mode'_Pair m2
      | ascii_string_of_mode'_Pair m = ascii_string_of_mode' m
  in ascii_string_of_mode'_Fun mode' end

(* premises *)

datatype indprem = Prem of term | Negprem of term | Sidecond of term
  | Generator of (string * typ);

fun dest_indprem (Prem t) = t
  | dest_indprem (Negprem t) = t
  | dest_indprem (Sidecond t) = t
  | dest_indprem (Generator _) = raise Fail "cannot destruct generator"

fun map_indprem f (Prem t) = Prem (f t)
  | map_indprem f (Negprem t) = Negprem (f t)
  | map_indprem f (Sidecond t) = Sidecond (f t)
  | map_indprem f (Generator (v, T)) = Generator (dest_Free (f (Free (v, T))))

(* general syntactic functions *)

(*Like dest_conj, but flattens conjunctions however nested*)
fun conjuncts_aux (Const (@{const_name HOL.conj}, _) $ t $ t') conjs = conjuncts_aux t (conjuncts_aux t' conjs)
  | conjuncts_aux t conjs = t::conjs;

fun conjuncts t = conjuncts_aux t [];

fun is_equationlike_term (Const ("==", _) $ _ $ _) = true
  | is_equationlike_term (Const (@{const_name Trueprop}, _) $ (Const (@{const_name HOL.eq}, _) $ _ $ _)) = true
  | is_equationlike_term _ = false
  
val is_equationlike = is_equationlike_term o prop_of 

fun is_pred_equation_term (Const ("==", _) $ u $ v) =
  (fastype_of u = @{typ bool}) andalso (fastype_of v = @{typ bool})
  | is_pred_equation_term _ = false
  
val is_pred_equation = is_pred_equation_term o prop_of 

fun is_intro_term constname t =
  the_default false (try (fn t => case fst (strip_comb (HOLogic.dest_Trueprop (Logic.strip_imp_concl t))) of
    Const (c, _) => c = constname
  | _ => false) t)
  
fun is_intro constname t = is_intro_term constname (prop_of t)

fun is_pred thy constname = (body_type (Sign.the_const_type thy constname) = HOLogic.boolT);

fun is_predT (T as Type("fun", [_, _])) = (snd (strip_type T) = @{typ bool})
  | is_predT _ = false

(*** check if a term contains only constructor functions ***)
(* TODO: another copy in the core! *)
(* FIXME: constructor terms are supposed to be seen in the way the code generator
  sees constructors.*)
fun is_constrt thy =
  let
    val cnstrs = flat (maps
      (map (fn (_, (Tname, _, cs)) => map (apsnd (rpair Tname o length)) cs) o #descr o snd)
      (Symtab.dest (Datatype.get_all thy)));
    fun check t = (case strip_comb t of
        (Var _, []) => true
      | (Free _, []) => true
      | (Const (s, T), ts) => (case (AList.lookup (op =) cnstrs s, body_type T) of
            (SOME (i, Tname), Type (Tname', _)) => length ts = i andalso Tname = Tname' andalso forall check ts
          | _ => false)
      | _ => false)
  in check end;

fun is_funtype (Type ("fun", [_, _])) = true
  | is_funtype _ = false;

fun is_Type (Type _) = true
  | is_Type _ = false

(* returns true if t is an application of an datatype constructor *)
(* which then consequently would be splitted *)
(* else false *)
(*
fun is_constructor thy t =
  if (is_Type (fastype_of t)) then
    (case DatatypePackage.get_datatype thy ((fst o dest_Type o fastype_of) t) of
      NONE => false
    | SOME info => (let
      val constr_consts = maps (fn (_, (_, _, constrs)) => map fst constrs) (#descr info)
      val (c, _) = strip_comb t
      in (case c of
        Const (name, _) => name mem_string constr_consts
        | _ => false) end))
  else false
*)

val is_constr = Code.is_constr o ProofContext.theory_of;

fun strip_all t = (Term.strip_all_vars t, Term.strip_all_body t)

fun strip_ex (Const (@{const_name Ex}, _) $ Abs (x, T, t)) =
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

fun map_atoms f intro = 
  let
    val (literals, head) = Logic.strip_horn intro
    fun appl t = (case t of
        (@{term Not} $ t') => HOLogic.mk_not (f t')
      | _ => f t)
  in
    Logic.list_implies
      (map (HOLogic.mk_Trueprop o appl o HOLogic.dest_Trueprop) literals, head)
  end

fun fold_atoms f intro s =
  let
    val (literals, head) = Logic.strip_horn intro
    fun appl t s = (case t of
      (@{term Not} $ t') => f t' s
      | _ => f t s)
  in fold appl (map HOLogic.dest_Trueprop literals) s end

fun fold_map_atoms f intro s =
  let
    val (literals, head) = Logic.strip_horn intro
    fun appl t s = (case t of
      (@{term Not} $ t') => apfst HOLogic.mk_not (f t' s)
      | _ => f t s)
    val (literals', s') = fold_map appl (map HOLogic.dest_Trueprop literals) s
  in
    (Logic.list_implies (map HOLogic.mk_Trueprop literals', head), s')
  end;

fun map_premises f intro =
  let
    val (premises, head) = Logic.strip_horn intro
  in
    Logic.list_implies (map f premises, head)
  end

fun map_filter_premises f intro =
  let
    val (premises, head) = Logic.strip_horn intro
  in
    Logic.list_implies (map_filter f premises, head)
  end

fun maps_premises f intro =
  let
    val (premises, head) = Logic.strip_horn intro
  in
    Logic.list_implies (maps f premises, head)
  end

fun map_concl f intro =
  let
    val (premises, head) = Logic.strip_horn intro
  in
    Logic.list_implies (premises, f head)
  end

(* combinators to apply a function to all basic parts of nested products *)

fun map_products f (Const (@{const_name Pair}, T) $ t1 $ t2) =
  Const (@{const_name Pair}, T) $ map_products f t1 $ map_products f t2
  | map_products f t = f t

(* split theorems of case expressions *)

fun prepare_split_thm ctxt split_thm =
    (split_thm RS @{thm iffD2})
    |> Local_Defs.unfold ctxt [@{thm atomize_conjL[symmetric]},
      @{thm atomize_all[symmetric]}, @{thm atomize_imp[symmetric]}]

fun find_split_thm thy (Const (name, T)) = Option.map #split (Datatype_Data.info_of_case thy name)
  | find_split_thm thy _ = NONE

(* lifting term operations to theorems *)

fun map_term thy f th =
  Skip_Proof.make_thm thy (f (prop_of th))

(*
fun equals_conv lhs_cv rhs_cv ct =
  case Thm.term_of ct of
    Const ("==", _) $ _ $ _ => Conv.arg_conv cv ct  
  | _ => error "equals_conv"  
*)

(* Different compilations *)

datatype compilation = Pred | Depth_Limited | Random | Depth_Limited_Random | DSeq | Annotated
  | Pos_Random_DSeq | Neg_Random_DSeq | New_Pos_Random_DSeq | New_Neg_Random_DSeq

fun negative_compilation_of Pos_Random_DSeq = Neg_Random_DSeq
  | negative_compilation_of Neg_Random_DSeq = Pos_Random_DSeq
  | negative_compilation_of New_Pos_Random_DSeq = New_Neg_Random_DSeq
  | negative_compilation_of New_Neg_Random_DSeq = New_Pos_Random_DSeq
  | negative_compilation_of c = c
  
fun compilation_for_polarity false Pos_Random_DSeq = Neg_Random_DSeq
  | compilation_for_polarity false New_Pos_Random_DSeq = New_Neg_Random_DSeq
  | compilation_for_polarity _ c = c

fun string_of_compilation c =
  case c of
    Pred => ""
  | Random => "random"
  | Depth_Limited => "depth limited"
  | Depth_Limited_Random => "depth limited random"
  | DSeq => "dseq"
  | Annotated => "annotated"
  | Pos_Random_DSeq => "pos_random dseq"
  | Neg_Random_DSeq => "neg_random_dseq"
  | New_Pos_Random_DSeq => "new_pos_random dseq"
  | New_Neg_Random_DSeq => "new_neg_random_dseq"

val compilation_names = [("pred", Pred),
  ("random", Random),
  ("depth_limited", Depth_Limited),
  ("depth_limited_random", Depth_Limited_Random),
  (*("annotated", Annotated),*)
  ("dseq", DSeq), ("random_dseq", Pos_Random_DSeq),
  ("new_random_dseq", New_Pos_Random_DSeq)]

val non_random_compilations = [Pred, Depth_Limited, DSeq, Annotated]


val random_compilations = [Random, Depth_Limited_Random,
  Pos_Random_DSeq, Neg_Random_DSeq, New_Pos_Random_DSeq, New_Neg_Random_DSeq]

(* datastructures and setup for generic compilation *)

datatype compilation_funs = CompilationFuns of {
  mk_predT : typ -> typ,
  dest_predT : typ -> typ,
  mk_bot : typ -> term,
  mk_single : term -> term,
  mk_bind : term * term -> term,
  mk_sup : term * term -> term,
  mk_if : term -> term,
  mk_iterate_upto : typ -> term * term * term -> term,
  mk_not : term -> term,
  mk_map : typ -> typ -> term -> term -> term
};

fun mk_predT (CompilationFuns funs) = #mk_predT funs
fun dest_predT (CompilationFuns funs) = #dest_predT funs
fun mk_bot (CompilationFuns funs) = #mk_bot funs
fun mk_single (CompilationFuns funs) = #mk_single funs
fun mk_bind (CompilationFuns funs) = #mk_bind funs
fun mk_sup (CompilationFuns funs) = #mk_sup funs
fun mk_if (CompilationFuns funs) = #mk_if funs
fun mk_iterate_upto (CompilationFuns funs) = #mk_iterate_upto funs
fun mk_not (CompilationFuns funs) = #mk_not funs
fun mk_map (CompilationFuns funs) = #mk_map funs

(** function types and names of different compilations **)

fun funT_of compfuns mode T =
  let
    val Ts = binder_types T
    val (inTs, outTs) = split_map_modeT (fn m => fn T => (SOME (funT_of compfuns m T), NONE)) mode Ts
  in
    inTs ---> (mk_predT compfuns (HOLogic.mk_tupleT outTs))
  end;

(* Different options for compiler *)

datatype options = Options of {  
  expected_modes : (string * mode list) option,
  proposed_modes : (string * mode list) list,
  proposed_names : ((string * mode) * string) list,
  show_steps : bool,
  show_proof_trace : bool,
  show_intermediate_results : bool,
  show_mode_inference : bool,
  show_modes : bool,
  show_compilation : bool,
  show_caught_failures : bool,
  show_invalid_clauses : bool,
  skip_proof : bool,
  no_topmost_reordering : bool,
  function_flattening : bool,
  specialise : bool,
  fail_safe_function_flattening : bool,
  no_higher_order_predicate : string list,
  inductify : bool,
  detect_switches : bool,
  compilation : compilation
};

fun expected_modes (Options opt) = #expected_modes opt
fun proposed_modes (Options opt) = AList.lookup (op =) (#proposed_modes opt)
fun proposed_names (Options opt) name mode = AList.lookup (eq_pair (op =) eq_mode)
  (#proposed_names opt) (name, mode)

fun show_steps (Options opt) = #show_steps opt
fun show_intermediate_results (Options opt) = #show_intermediate_results opt
fun show_proof_trace (Options opt) = #show_proof_trace opt
fun show_modes (Options opt) = #show_modes opt
fun show_mode_inference (Options opt) = #show_mode_inference opt
fun show_compilation (Options opt) = #show_compilation opt
fun show_caught_failures (Options opt) = #show_caught_failures opt
fun show_invalid_clauses (Options opt) = #show_invalid_clauses opt
fun skip_proof (Options opt) = #skip_proof opt

fun function_flattening (Options opt) = #function_flattening opt
fun fail_safe_function_flattening (Options opt) = #fail_safe_function_flattening opt
fun specialise (Options opt) = #specialise opt
fun no_topmost_reordering (Options opt) = #no_topmost_reordering opt
fun no_higher_order_predicate (Options opt) = #no_higher_order_predicate opt

fun is_inductify (Options opt) = #inductify opt

fun compilation (Options opt) = #compilation opt

fun detect_switches (Options opt) = #detect_switches opt

val default_options = Options {
  expected_modes = NONE,
  proposed_modes = [],
  proposed_names = [],
  show_steps = false,
  show_intermediate_results = false,
  show_proof_trace = false,
  show_modes = false,
  show_mode_inference = false,
  show_compilation = false,
  show_caught_failures = false,
  show_invalid_clauses = false,
  skip_proof = true,
  no_topmost_reordering = false,
  function_flattening = false,
  specialise = false,
  fail_safe_function_flattening = false,
  no_higher_order_predicate = [],
  inductify = false,
  detect_switches = true,
  compilation = Pred
}

val bool_options = ["show_steps", "show_intermediate_results", "show_proof_trace", "show_modes",
  "show_mode_inference", "show_compilation", "show_invalid_clauses", "skip_proof", "inductify",
  "no_function_flattening", "detect_switches", "specialise", "no_topmost_reordering"]

fun print_step options s =
  if show_steps options then tracing s else ()

(* simple transformations *)

(** tuple processing **)

fun expand_tuples thy intro =
  let
    fun rewrite_args [] (pats, intro_t, ctxt) = (pats, intro_t, ctxt)
      | rewrite_args (arg::args) (pats, intro_t, ctxt) = 
      (case HOLogic.strip_tupleT (fastype_of arg) of
        (Ts as _ :: _ :: _) =>
        let
          fun rewrite_arg' (Const (@{const_name Pair}, _) $ _ $ t2, Type (@{type_name Product_Type.prod}, [_, T2]))
            (args, (pats, intro_t, ctxt)) = rewrite_arg' (t2, T2) (args, (pats, intro_t, ctxt))
            | rewrite_arg' (t, Type (@{type_name Product_Type.prod}, [T1, T2])) (args, (pats, intro_t, ctxt)) =
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
    val ctxt = ProofContext.init_global thy
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
    (* splitting conjunctions introduced by Pair_eq*)
    fun split_conj prem =
      map HOLogic.mk_Trueprop (conjuncts (HOLogic.dest_Trueprop prem))
    val intro''''' = map_term thy (maps_premises split_conj) intro''''
  in
    intro'''''
  end

(** eta contract higher-order arguments **)

fun eta_contract_ho_arguments thy intro =
  let
    fun f atom = list_comb (apsnd ((map o map_products) Envir.eta_contract) (strip_comb atom))
  in
    map_term thy (map_concl f o map_atoms f) intro
  end

(** remove equalities **)

fun remove_equalities thy intro =
  let
    fun remove_eqs intro_t =
      let
        val (prems, concl) = Logic.strip_horn intro_t
        fun remove_eq (prems, concl) =
          let
            fun removable_eq prem =
              case try (HOLogic.dest_eq o HOLogic.dest_Trueprop) prem of
                SOME (lhs, rhs) => (case lhs of
                  Var _ => true
                  | _ => (case rhs of Var _ => true | _ => false))
              | NONE => false
          in
            case find_first removable_eq prems of
              NONE => (prems, concl)
            | SOME eq =>
              let
                val (lhs, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop eq)
                val prems' = remove (op =) eq prems
                val subst = (case lhs of
                  (v as Var _) =>
                    (fn t => if t = v then rhs else t)
                | _ => (case rhs of
                   (v as Var _) => (fn t => if t = v then lhs else t)))
              in
                remove_eq (map (map_aterms subst) prems', map_aterms subst concl)
              end
          end
      in
        Logic.list_implies (remove_eq (prems, concl))
      end
  in
    map_term thy remove_eqs intro
  end

(* Some last processing *)

fun remove_pointless_clauses intro =
  if Logic.strip_imp_prems (prop_of intro) = [@{prop "False"}] then
    []
  else [intro]

(* some peephole optimisations *)

fun peephole_optimisation thy intro =
  let
    val process =
      MetaSimplifier.rewrite_rule (Predicate_Compile_Simps.get (ProofContext.init_global thy))
    fun process_False intro_t =
      if member (op =) (Logic.strip_imp_prems intro_t) @{prop "False"} then NONE else SOME intro_t
    fun process_True intro_t =
      map_filter_premises (fn p => if p = @{prop True} then NONE else SOME p) intro_t
  in
    Option.map (Skip_Proof.make_thm thy)
      (process_False (process_True (prop_of (process intro))))
  end

(* defining a quickcheck predicate *)

fun strip_imp_prems (Const(@{const_name HOL.implies}, _) $ A $ B) = A :: strip_imp_prems B
  | strip_imp_prems _ = [];

fun strip_imp_concl (Const(@{const_name HOL.implies}, _) $ A $ B) = strip_imp_concl B
  | strip_imp_concl A = A : term;

fun strip_horn A = (strip_imp_prems A, strip_imp_concl A);

fun define_quickcheck_predicate t thy =
  let
    val (vs, t') = strip_abs t
    val vs' = Variable.variant_frees (ProofContext.init_global thy) [] vs
    val t'' = subst_bounds (map Free (rev vs'), t')
    val (prems, concl) = strip_horn t''
    val constname = "quickcheck"
    val full_constname = Sign.full_bname thy constname
    val constT = map snd vs' ---> @{typ bool}
    val thy1 = Sign.add_consts_i [(Binding.name constname, constT, NoSyn)] thy
    val const = Const (full_constname, constT)
    val t = Logic.list_implies
      (map HOLogic.mk_Trueprop (prems @ [HOLogic.mk_not concl]),
       HOLogic.mk_Trueprop (list_comb (const, map Free vs')))
    val tac = fn _ => Skip_Proof.cheat_tac thy1
    val intro = Goal.prove (ProofContext.init_global thy1) (map fst vs') [] t tac
  in
    ((((full_constname, constT), vs'), intro), thy1)
  end

end;

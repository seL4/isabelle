(*  Title:      HOL/Tools/Predicate_Compile/predicate_compile_aux.ML
    Author:     Lukas Bulwahn, TU Muenchen

Auxilary functions for predicate compiler.
*)

(* FIXME proper signature *)

structure TermGraph = Graph(type key = term val ord = TermOrd.fast_term_ord);

structure Predicate_Compile_Aux =
struct

(* general functions *)

fun apfst3 f (x, y, z) = (f x, y, z)
fun apsnd3 f (x, y, z) = (x, f y, z)
fun aptrd3 f (x, y, z) = (x, y, f z)

fun comb_option f (SOME x1, SOME x2) = SOME (f (x1, x2))
  | comb_option f (NONE, SOME x2) = SOME x2
  | comb_option f (SOME x1, NONE) = SOME x1
  | comb_option f (NONE, NONE) = NONE

fun map2_optional f (x :: xs) (y :: ys) = (f x (SOME y)) :: (map2_optional f xs ys)
  | map2_optional f (x :: xs) [] = (f x NONE) :: (map2_optional f xs [])
  | map2_optional f [] [] = []

fun find_indices f xs =
  map_filter (fn (i, true) => SOME i | (i, false) => NONE) (map_index (apsnd f) xs)

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

(* name: binder_modes? *)
fun strip_fun_mode (Fun (mode, mode')) = mode :: strip_fun_mode mode'
  | strip_fun_mode Bool = []
  | strip_fun_mode _ = error "Bad mode for strip_fun_mode"

fun dest_fun_mode (Fun (mode, mode')) = mode :: dest_fun_mode mode'
  | dest_fun_mode mode = [mode]

fun dest_tuple_mode (Pair (mode, mode')) = mode :: dest_tuple_mode mode'
  | dest_tuple_mode _ = []

fun all_modes_of_typ (T as Type ("fun", _)) = 
  let
    val (S, U) = strip_type T
  in
    if U = HOLogic.boolT then
      fold_rev (fn m1 => fn m2 => map_product (curry Fun) m1 m2)
        (map all_modes_of_typ S) [Bool]
    else
      [Input, Output]
  end
  | all_modes_of_typ (Type ("*", [T1, T2])) = 
    map_product (curry Pair) (all_modes_of_typ T1) (all_modes_of_typ T2)
  | all_modes_of_typ (Type ("bool", [])) = [Bool]
  | all_modes_of_typ _ = [Input, Output]

fun extract_params arg =
  case fastype_of arg of
    (T as Type ("fun", _)) =>
      (if (body_type T = HOLogic.boolT) then
        (case arg of
          Free _ => [arg] | _ => error "extract_params: Unexpected term")
      else [])
  | (Type ("*", [T1, T2])) =>
      let
        val (t1, t2) = HOLogic.dest_prod arg
      in
        extract_params t1 @ extract_params t2
      end
  | _ => []

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
      | ho_arg (Fun _) NONE = error "ho_arg_of"
      | ho_arg (Pair (m1, m2)) (SOME (Const ("Pair", _) $ t1 $ t2)) =
          ho_arg m1 (SOME t1) @ ho_arg m2 (SOME t2)
      | ho_arg (Pair (m1, m2)) NONE = ho_arg m1 NONE @ ho_arg m2 NONE
      | ho_arg _ _ = []
  in
    flat (map2_optional ho_arg (strip_fun_mode mode) ts)
  end

(* temporary function should be replaced by unsplit_input or so? *)
fun replace_ho_args mode hoargs ts =
  let
    fun replace (Fun _, _) (arg' :: hoargs') = (arg', hoargs')
      | replace (Pair (m1, m2), Const ("Pair", T) $ t1 $ t2) hoargs =
        let
          val (t1', hoargs') = replace (m1, t1) hoargs
          val (t2', hoargs'') = replace (m2, t2) hoargs'
        in
          (Const ("Pair", T) $ t1' $ t2', hoargs'')
        end
      | replace (_, t) hoargs = (t, hoargs)
  in
    fst (fold_map replace ((strip_fun_mode mode) ~~ ts) hoargs)
  end

fun ho_argsT_of mode Ts =
  let
    fun ho_arg (Fun _) T = [T]
      | ho_arg (Pair (m1, m2)) (Type ("*", [T1, T2])) = ho_arg m1 T1 @ ho_arg m2 T2
      | ho_arg _ _ = []
  in
    flat (map2 ho_arg (strip_fun_mode mode) Ts)
  end

(* splits mode and maps function to higher-order argument types *)
fun split_map_mode f mode ts =
  let
    fun split_arg_mode' (m as Fun _) t = f m t
      | split_arg_mode' (Pair (m1, m2)) (Const ("Pair", _) $ t1 $ t2) =
        let
          val (i1, o1) = split_arg_mode' m1 t1
          val (i2, o2) = split_arg_mode' m2 t2
        in
          (comb_option HOLogic.mk_prod (i1, i2), comb_option HOLogic.mk_prod (o1, o2))
        end
      | split_arg_mode' Input t = (SOME t, NONE)
      | split_arg_mode' Output t = (NONE,  SOME t)
      | split_arg_mode' _ _ = error "split_map_mode: mode and term do not match"
  in
    (pairself (map_filter I) o split_list) (map2 split_arg_mode' (strip_fun_mode mode) ts)
  end

(* splits mode and maps function to higher-order argument types *)
fun split_map_modeT f mode Ts =
  let
    fun split_arg_mode' (m as Fun _) T = f m T
      | split_arg_mode' (Pair (m1, m2)) (Type ("*", [T1, T2])) =
        let
          val (i1, o1) = split_arg_mode' m1 T1
          val (i2, o2) = split_arg_mode' m2 T2
        in
          (comb_option HOLogic.mk_prodT (i1, i2), comb_option HOLogic.mk_prodT (o1, o2))
        end
      | split_arg_mode' Input T = (SOME T, NONE)
      | split_arg_mode' Output T = (NONE,  SOME T)
      | split_arg_mode' _ _ = error "split_modeT': mode and type do not match"
  in
    (pairself (map_filter I) o split_list) (map2 split_arg_mode' (strip_fun_mode mode) Ts)
  end

fun split_mode mode ts = split_map_mode (fn _ => fn _ => (NONE, NONE)) mode ts

fun fold_map_aterms_prodT comb f (Type ("*", [T1, T2])) s =
  let
    val (x1, s') = fold_map_aterms_prodT comb f T1 s
    val (x2, s'') = fold_map_aterms_prodT comb f T2 s'
  in
    (comb x1 x2, s'')
  end
  | fold_map_aterms_prodT comb f T s = f T s

fun map_filter_prod f (Const ("Pair", _) $ t1 $ t2) =
  comb_option HOLogic.mk_prod (map_filter_prod f t1, map_filter_prod f t2)
  | map_filter_prod f t = f t

(* obviously, split_mode' and split_modeT' do not match? where does that cause problems? *)
  
fun split_modeT' mode Ts =
  let
    fun split_arg_mode' (Fun _) T = ([], [])
      | split_arg_mode' (Pair (m1, m2)) (Type ("*", [T1, T2])) =
        let
          val (i1, o1) = split_arg_mode' m1 T1
          val (i2, o2) = split_arg_mode' m2 T2
        in
          (i1 @ i2, o1 @ o2)
        end
      | split_arg_mode' Input T = ([T], [])
      | split_arg_mode' Output T = ([], [T])
      | split_arg_mode' _ _ = error "split_modeT': mode and type do not match"
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

(* general syntactic functions *)

(*Like dest_conj, but flattens conjunctions however nested*)
fun conjuncts_aux (Const ("op &", _) $ t $ t') conjs = conjuncts_aux t (conjuncts_aux t' conjs)
  | conjuncts_aux t conjs = t::conjs;

fun conjuncts t = conjuncts_aux t [];

fun is_equationlike_term (Const ("==", _) $ _ $ _) = true
  | is_equationlike_term (Const ("Trueprop", _) $ (Const ("op =", _) $ _ $ _)) = true
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

fun is_pred thy constname =
  let
    val T = (Sign.the_const_type thy constname)
  in body_type T = @{typ "bool"} end;
  

fun is_predT (T as Type("fun", [_, _])) = (snd (strip_type T) = HOLogic.boolT)
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
        (Free _, []) => true
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

(* must be exported in code.ML *)
(* TODO: is there copy in the core? *)
fun is_constr thy = is_some o Code.get_datatype_of_constr thy;

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

fun map_atoms f intro = 
  let
    val (literals, head) = Logic.strip_horn intro
    fun appl t = (case t of
        (@{term "Not"} $ t') => HOLogic.mk_not (f t')
      | _ => f t)
  in
    Logic.list_implies
      (map (HOLogic.mk_Trueprop o appl o HOLogic.dest_Trueprop) literals, head)
  end

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
      (@{term "Not"} $ t') => apfst HOLogic.mk_not (f t' s)
      | _ => f t s)
    val (literals', s') = fold_map appl (map HOLogic.dest_Trueprop literals) s
  in
    (Logic.list_implies (map HOLogic.mk_Trueprop literals', head), s')
  end;

fun maps_premises f intro =
  let
    val (premises, head) = Logic.strip_horn intro
  in
    Logic.list_implies (maps f premises, head)
  end
  
(* lifting term operations to theorems *)

fun map_term thy f th =
  Skip_Proof.make_thm thy (f (prop_of th))

(*
fun equals_conv lhs_cv rhs_cv ct =
  case Thm.term_of ct of
    Const ("==", _) $ _ $ _ => Conv.arg_conv cv ct  
  | _ => error "equals_conv"  
*)

(* Different options for compiler *)

datatype compilation = Pred | Random | Depth_Limited | DSeq | Annotated | Random_DSeq

fun string_of_compilation c = case c of
    Pred => ""
  | Random => "random"
  | Depth_Limited => "depth limited"
  | DSeq => "dseq"
  | Annotated => "annotated"
  | Random_DSeq => "random dseq"

(*datatype compilation_options =
  Pred | Random of int | Depth_Limited of int | DSeq of int | Annotated*)

datatype options = Options of {  
  expected_modes : (string * mode list) option,
  proposed_modes : (string * mode list) option,
  proposed_names : ((string * mode) * string) list,
  show_steps : bool,
  show_proof_trace : bool,
  show_intermediate_results : bool,
  show_mode_inference : bool,
  show_modes : bool,
  show_compilation : bool,
  skip_proof : bool,

  inductify : bool,
  compilation : compilation
};

fun expected_modes (Options opt) = #expected_modes opt
fun proposed_modes (Options opt) = #proposed_modes opt
fun proposed_names (Options opt) name mode = AList.lookup (eq_pair (op =) eq_mode)
  (#proposed_names opt) (name, mode)

fun show_steps (Options opt) = #show_steps opt
fun show_intermediate_results (Options opt) = #show_intermediate_results opt
fun show_proof_trace (Options opt) = #show_proof_trace opt
fun show_modes (Options opt) = #show_modes opt
fun show_mode_inference (Options opt) = #show_mode_inference opt
fun show_compilation (Options opt) = #show_compilation opt
fun skip_proof (Options opt) = #skip_proof opt

fun is_inductify (Options opt) = #inductify opt

fun compilation (Options opt) = #compilation opt

val default_options = Options {
  expected_modes = NONE,
  proposed_modes = NONE,
  proposed_names = [],
  show_steps = false,
  show_intermediate_results = false,
  show_proof_trace = false,
  show_modes = false,
  show_mode_inference = false,
  show_compilation = false,
  skip_proof = true,
  
  inductify = false,
  compilation = Pred
}

val bool_options = ["show_steps", "show_intermediate_results", "show_proof_trace", "show_modes",
  "show_mode_inference", "show_compilation", "skip_proof", "inductify"]

val compilation_names = [("pred", Pred),
  (*("random", Random), ("depth_limited", Depth_Limited), ("annotated", Annotated),*)
  ("dseq", DSeq), ("random_dseq", Random_DSeq)]

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
    (* splitting conjunctions introduced by Pair_eq*)
    fun split_conj prem =
      map HOLogic.mk_Trueprop (conjuncts (HOLogic.dest_Trueprop prem))
    val intro''''' = map_term thy (maps_premises split_conj) intro''''
  in
    intro'''''
  end

end;

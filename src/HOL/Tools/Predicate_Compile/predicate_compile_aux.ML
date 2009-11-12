(*  Title:      HOL/Tools/Predicate_Compile/predicate_compile_aux.ML
    Author:     Lukas Bulwahn, TU Muenchen

Auxilary functions for predicate compiler.
*)

(* FIXME proper signature *)

structure Predicate_Compile_Aux =
struct


(* mode *)

type smode = (int * int list option) list
type mode = smode option list * smode
datatype tmode = Mode of mode * smode * tmode option list;

fun string_of_smode js =
    commas (map
      (fn (i, is) =>
        string_of_int i ^ (case is of NONE => ""
    | SOME is => "p" ^ enclose "[" "]" (commas (map string_of_int is)))) js)
(* FIXME: remove! *)

fun string_of_mode (iss, is) = space_implode " -> " (map
  (fn NONE => "X"
    | SOME js => enclose "[" "]" (string_of_smode js))
       (iss @ [SOME is]));

fun string_of_tmode (Mode (predmode, termmode, param_modes)) =
  "predmode: " ^ (string_of_mode predmode) ^
  (if null param_modes then "" else
    "; " ^ "params: " ^ commas (map (the_default "NONE" o Option.map string_of_tmode) param_modes))

(* new datatype for mode *)

datatype mode' = Bool | Input | Output | Pair of mode' * mode' | Fun of mode' * mode'

(* equality of instantiatedness with respect to equivalences:
  Pair Input Input == Input and Pair Output Output == Output *)
fun eq_mode' (Fun (m1, m2), Fun (m3, m4)) = eq_mode' (m1, m3) andalso eq_mode' (m2, m4)
  | eq_mode' (Pair (m1, m2), Pair (m3, m4)) = eq_mode' (m1, m3) andalso eq_mode' (m2, m4)
  | eq_mode' (Pair (m1, m2), Input) = eq_mode' (m1, Input) andalso eq_mode' (m2, Input)
  | eq_mode' (Pair (m1, m2), Output) = eq_mode' (m1, Output) andalso eq_mode' (m2, Output)
  | eq_mode' (Input, Pair (m1, m2)) = eq_mode' (Input, m1) andalso eq_mode' (Input, m2)
  | eq_mode' (Output, Pair (m1, m2)) = eq_mode' (Output, m1) andalso eq_mode' (Output, m2)
  | eq_mode' (Input, Input) = true
  | eq_mode' (Output, Output) = true
  | eq_mode' (Bool, Bool) = true
  | eq_mode' _ = false

(* name: binder_modes? *)
fun strip_fun_mode (Fun (mode, mode')) = mode :: strip_fun_mode mode'
  | strip_fun_mode Bool = []
  | strip_fun_mode _ = error "Bad mode for strip_fun_mode"

fun dest_fun_mode (Fun (mode, mode')) = mode :: dest_fun_mode mode'
  | dest_fun_mode mode = [mode]

fun dest_tuple_mode (Pair (mode, mode')) = mode :: dest_tuple_mode mode'
  | dest_tuple_mode _ = []

fun string_of_mode' mode' =
  let
    fun string_of_mode1 Input = "i"
      | string_of_mode1 Output = "o"
      | string_of_mode1 Bool = "bool"
      | string_of_mode1 mode = "(" ^ (string_of_mode3 mode) ^ ")"
    and string_of_mode2 (Pair (m1, m2)) = string_of_mode3 m1 ^ " * " ^  string_of_mode2 m2
      | string_of_mode2 mode = string_of_mode1 mode
    and string_of_mode3 (Fun (m1, m2)) = string_of_mode2 m1 ^ " => " ^ string_of_mode3 m2
      | string_of_mode3 mode = string_of_mode2 mode
  in string_of_mode3 mode' end

fun ascii_string_of_mode' mode' =
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

fun translate_mode T (iss, is) =
  let
    val Ts = binder_types T
    val (Ts1, Ts2) = chop (length iss) Ts
    fun translate_smode Ts is =
      let
        fun translate_arg (i, T) =
          case AList.lookup (op =) is (i + 1) of
            SOME NONE => Input
          | SOME (SOME its) =>
            let
              fun translate_tuple (i, T) = if member (op =) its (i + 1) then Input else Output
            in 
              foldr1 Pair (map_index translate_tuple (HOLogic.strip_tupleT T))
            end
          | NONE => Output
      in map_index translate_arg Ts end
    fun mk_mode arg_modes = foldr1 Fun (arg_modes @ [Bool])
    val param_modes =
      map (fn (T, NONE) => Input | (T, SOME is) => mk_mode (translate_smode (binder_types T) is))
        (Ts1 ~~ iss)
  in
    mk_mode (param_modes @ translate_smode Ts2 is)
  end;

fun translate_mode' nparams mode' =
  let
    fun err () = error "translate_mode': given mode cannot be translated"
    val (m1, m2) = chop nparams (strip_fun_mode mode')
    val translate_to_tupled_mode =
      (map_filter I) o (map_index (fn (i, m) =>
        if eq_mode' (m, Input) then SOME (i + 1)
        else if eq_mode' (m, Output) then NONE
        else err ()))
    val translate_to_smode =
      (map_filter I) o (map_index (fn (i, m) =>
        if eq_mode' (m, Input) then SOME (i + 1, NONE)
        else if eq_mode' (m, Output) then NONE
        else SOME (i + 1, SOME (translate_to_tupled_mode (dest_tuple_mode m)))))
    fun translate_to_param_mode m =
      case rev (dest_fun_mode m) of
        Bool :: _ :: _ => SOME (translate_to_smode (strip_fun_mode m))
      | _ => if eq_mode' (m, Input) then NONE else err ()
  in
    (map translate_to_param_mode m1, translate_to_smode m2)
  end

fun string_of_mode thy constname mode =
  string_of_mode' (translate_mode (Sign.the_const_type thy constname) mode)

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

(* guessing number of parameters *)
fun find_indexes pred xs =
  let
    fun find is n [] = is
      | find is n (x :: xs) = find (if pred x then (n :: is) else is) (n + 1) xs;
  in rev (find [] 0 xs) end;

fun guess_nparams T =
  let
    val argTs = binder_types T
    val nparams = fold Integer.max
      (map (fn x => x + 1) (find_indexes is_predT argTs)) 0
  in nparams end;

(*** check if a term contains only constructor functions ***)
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

datatype options = Options of {  
  expected_modes : (string * mode' list) option,
  proposed_modes : (string * mode' list) list,
  proposed_names : ((string * mode') * string) list,
  show_steps : bool,
  show_proof_trace : bool,
  show_intermediate_results : bool,
  show_mode_inference : bool,
  show_modes : bool,
  show_compilation : bool,
  skip_proof : bool,

  inductify : bool,
  random : bool,
  depth_limited : bool,
  annotated : bool
};

fun expected_modes (Options opt) = #expected_modes opt
fun proposed_modes (Options opt) name = AList.lookup (op =) (#proposed_modes opt) name
fun proposed_names (Options opt) name mode = AList.lookup (eq_pair (op =) eq_mode')
  (#proposed_names opt) (name, mode)

fun show_steps (Options opt) = #show_steps opt
fun show_intermediate_results (Options opt) = #show_intermediate_results opt
fun show_proof_trace (Options opt) = #show_proof_trace opt
fun show_modes (Options opt) = #show_modes opt
fun show_mode_inference (Options opt) = #show_mode_inference opt
fun show_compilation (Options opt) = #show_compilation opt
fun skip_proof (Options opt) = #skip_proof opt

fun is_inductify (Options opt) = #inductify opt
fun is_random (Options opt) = #random opt
fun is_depth_limited (Options opt) = #depth_limited opt
fun is_annotated (Options opt) = #annotated opt

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
  skip_proof = false,
  
  inductify = false,
  random = false,
  depth_limited = false,
  annotated = false
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
    (* splitting conjunctions introduced by Pair_eq*)
    fun split_conj prem =
      map HOLogic.mk_Trueprop (conjuncts (HOLogic.dest_Trueprop prem))
    val intro''''' = map_term thy (maps_premises split_conj) intro''''
  in
    intro'''''
  end

end;

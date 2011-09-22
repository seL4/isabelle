(*  Title:      HOL/Tools/Quickcheck/quickcheck_common.ML
    Author:     Florian Haftmann, Lukas Bulwahn, TU Muenchen

Common functions for quickcheck's generators.
*)

signature QUICKCHECK_COMMON =
sig
  val strip_imp : term -> (term list * term)
  val define_functions : ((term list -> term list) * (Proof.context -> tactic) option)
    -> string -> string list -> string list -> typ list -> Proof.context -> Proof.context 
  val perhaps_constrain: theory -> (typ * sort) list -> (string * sort) list
    -> (string * sort -> string * sort) option
  val ensure_sort_datatype:
    ((sort * sort) * sort) * (Datatype.config -> Datatype.descr -> (string * sort) list
      -> string list -> string -> string list * string list -> typ list * typ list -> theory -> theory)
    -> Datatype.config -> string list -> theory -> theory
  val gen_mk_parametric_generator_expr :
   (((Proof.context -> term * term list -> term) * term) * typ)
     -> Proof.context -> (term * term list) list -> term
  val mk_fun_upd : typ -> typ -> term * term -> term -> term
  val post_process_term : term -> term
end;

structure Quickcheck_Common : QUICKCHECK_COMMON =
struct

(* static options *)

val define_foundationally = false

(* HOLogic's term functions *)

fun strip_imp (Const(@{const_name HOL.implies},_) $ A $ B) = apfst (cons A) (strip_imp B)
  | strip_imp A = ([], A)

fun mk_undefined T = Const(@{const_name undefined}, T)
  
(* defining functions *)

fun pat_completeness_auto ctxt =
  Pat_Completeness.pat_completeness_tac ctxt 1 THEN auto_tac ctxt

fun define_functions (mk_equations, termination_tac) prfx argnames names Ts =
  if define_foundationally andalso is_some termination_tac then
    let
      val eqs_t = mk_equations (map2 (fn name => fn T => Free (name, T)) names Ts)
    in
      Function.add_function
        (map (fn (name, T) => (Binding.conceal (Binding.name name), SOME T, NoSyn))
          (names ~~ Ts))
        (map (pair (apfst Binding.conceal Attrib.empty_binding)) eqs_t)
        Function_Common.default_config pat_completeness_auto
      #> snd
      #> Local_Theory.restore
      #> (fn lthy => Function.prove_termination NONE (the termination_tac lthy) lthy)
      #> snd
    end
  else
    fold_map (fn (name, T) => Local_Theory.define
        ((Binding.conceal (Binding.name name), NoSyn),
          (apfst Binding.conceal Attrib.empty_binding, mk_undefined T))
      #> apfst fst) (names ~~ Ts)
    #> (fn (consts, lthy) =>
      let
        val eqs_t = mk_equations consts
        val eqs = map (fn eq => Goal.prove lthy argnames [] eq
          (fn _ => Skip_Proof.cheat_tac (Proof_Context.theory_of lthy))) eqs_t
      in
        fold (fn (name, eq) => Local_Theory.note
        ((Binding.conceal (Binding.qualify true prfx
           (Binding.qualify true name (Binding.name "simps"))),
           Code.add_default_eqn_attrib :: map (Attrib.internal o K)
             [Simplifier.simp_add, Nitpick_Simps.add]), [eq]) #> snd) (names ~~ eqs) lthy
      end)

(** ensuring sort constraints **)

fun perhaps_constrain thy insts raw_vs =
  let
    fun meet (T, sort) = Sorts.meet_sort (Sign.classes_of thy) 
      (Logic.varifyT_global T, sort);
    val vtab = Vartab.empty
      |> fold (fn (v, sort) => Vartab.update ((v, 0), sort)) raw_vs
      |> fold meet insts;
  in SOME (fn (v, _) => (v, (the o Vartab.lookup vtab) (v, 0)))
  end handle Sorts.CLASS_ERROR _ => NONE;

fun ensure_sort_datatype (((sort_vs, aux_sort), sort), instantiate_datatype) config raw_tycos thy =
  let
    val algebra = Sign.classes_of thy;
    val (descr, raw_vs, tycos, prfx, (names, auxnames), raw_TUs) = Datatype.the_descr thy raw_tycos
    val vs = (map o apsnd) (curry (Sorts.inter_sort algebra) sort_vs) raw_vs
    fun insts_of sort constr  = (map (rpair sort) o flat o maps snd o maps snd)
      (Datatype_Aux.interpret_construction descr vs constr)
    val insts = insts_of sort  { atyp = single, dtyp = (K o K o K) [] }
      @ insts_of aux_sort { atyp = K [], dtyp = K o K }
    val has_inst = exists (fn tyco => can (Sorts.mg_domain algebra tyco) sort) tycos;
  in if has_inst then thy
    else case perhaps_constrain thy insts vs
     of SOME constrain => instantiate_datatype config descr
          (map constrain vs) tycos prfx (names, auxnames)
            ((pairself o map o map_atyps) (fn TFree v => TFree (constrain v)) raw_TUs) thy
      | NONE => thy
  end;
  
(** generic parametric compilation **)

fun gen_mk_parametric_generator_expr ((mk_generator_expr, out_of_bounds), T) ctxt ts =
  let
    val if_t = Const (@{const_name "If"}, @{typ bool} --> T --> T --> T)
    fun mk_if (index, (t, eval_terms)) else_t =
      if_t $ (HOLogic.eq_const @{typ code_numeral} $ Bound 0 $ HOLogic.mk_number @{typ code_numeral} index) $
        (mk_generator_expr ctxt (t, eval_terms)) $ else_t
  in
    absdummy @{typ "code_numeral"} (fold_rev mk_if (1 upto (length ts) ~~ ts) out_of_bounds)
  end

(** post-processing of function terms **)

fun dest_fun_upd (Const (@{const_name fun_upd}, _) $ t0 $ t1 $ t2) = (t0, (t1, t2))
  | dest_fun_upd t = raise TERM ("dest_fun_upd", [t])

fun mk_fun_upd T1 T2 (t1, t2) t = 
  Const (@{const_name fun_upd}, (T1 --> T2) --> T1 --> T2 --> T1 --> T2) $ t $ t1 $ t2

fun dest_fun_upds t =
  case try dest_fun_upd t of
    NONE =>
      (case t of
        Abs (_, _, _) => ([], t) 
      | _ => raise TERM ("dest_fun_upds", [t]))
  | SOME (t0, (t1, t2)) => apfst (cons (t1, t2)) (dest_fun_upds t0)

fun make_fun_upds T1 T2 (tps, t) = fold_rev (mk_fun_upd T1 T2) tps t

fun make_set T1 [] = Const (@{const_abbrev Set.empty}, T1 --> @{typ bool})
  | make_set T1 ((_, @{const False}) :: tps) = make_set T1 tps
  | make_set T1 ((t1, @{const True}) :: tps) =
    Const (@{const_name insert}, T1 --> (T1 --> @{typ bool}) --> T1 --> @{typ bool})
      $ t1 $ (make_set T1 tps)
  | make_set T1 ((_, t) :: tps) = raise TERM ("make_set", [t])

fun make_coset T [] = Const (@{const_abbrev UNIV}, T --> @{typ bool})
  | make_coset T tps = 
    let
      val U = T --> @{typ bool}
      fun invert @{const False} = @{const True}
        | invert @{const True} = @{const False}
    in
      Const (@{const_name "Groups.minus_class.minus"}, U --> U --> U)
        $ Const (@{const_abbrev UNIV}, U) $ make_set T (map (apsnd invert) tps)
    end

fun make_map T1 T2 [] = Const (@{const_abbrev Map.empty}, T1 --> T2)
  | make_map T1 T2 ((_, Const (@{const_name None}, _)) :: tps) = make_map T1 T2 tps
  | make_map T1 T2 ((t1, t2) :: tps) = mk_fun_upd T1 T2 (t1, t2) (make_map T1 T2 tps)
  
fun post_process_term t =
  let
    fun map_Abs f t =
      case t of Abs (x, T, t') => Abs (x, T, f t') | _ => raise TERM ("map_Abs", [t]) 
    fun process_args t = case strip_comb t of
      (c as Const (_, _), ts) => list_comb (c, map post_process_term ts)
  in
    case fastype_of t of
      Type (@{type_name fun}, [T1, T2]) =>
        (case try dest_fun_upds t of
          SOME (tps, t) =>
            (map (pairself post_process_term) tps, map_Abs post_process_term t)
            |> (case T2 of
              @{typ bool} => 
                (case t of
                   Abs(_, _, @{const False}) => fst #> rev #> make_set T1
                 | Abs(_, _, @{const True}) => fst #> rev #> make_coset T1
                 | Abs(_, _, Const (@{const_name undefined}, _)) => fst #> rev #> make_set T1
                 | _ => raise TERM ("post_process_term", [t]))
            | Type (@{type_name option}, _) =>
                (case t of
                  Abs(_, _, Const (@{const_name None}, _)) => fst #> make_map T1 T2
                | Abs(_, _, Const (@{const_name undefined}, _)) => fst #> make_map T1 T2
                | _ => make_fun_upds T1 T2)
            | _ => make_fun_upds T1 T2)
        | NONE => process_args t)
    | _ => process_args t
  end
  

end;

(*  Title:      HOL/Tools/ATP/atp_proof_reconstruct.ML
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Claire Quigley, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Basic proof reconstruction from ATP proofs.
*)

signature ATP_PROOF_RECONSTRUCT =
sig
  type 'a atp_type = 'a ATP_Problem.atp_type
  type ('a, 'b) atp_term = ('a, 'b) ATP_Problem.atp_term
  type ('a, 'b, 'c, 'd) atp_formula = ('a, 'b, 'c, 'd) ATP_Problem.atp_formula
  type stature = ATP_Problem_Generate.stature
  type atp_step_name = ATP_Proof.atp_step_name
  type ('a, 'b) atp_step = ('a, 'b) ATP_Proof.atp_step
  type 'a atp_proof = 'a ATP_Proof.atp_proof

  val metisN : string
  val full_typesN : string
  val partial_typesN : string
  val no_typesN : string
  val really_full_type_enc : string
  val full_type_enc : string
  val partial_type_enc : string
  val no_type_enc : string
  val full_type_encs : string list
  val partial_type_encs : string list
  val default_metis_lam_trans : string

  val forall_of : term -> term -> term
  val exists_of : term -> term -> term
  val type_enc_aliases : (string * string list) list
  val unalias_type_enc : string -> string list
  val term_of_atp : Proof.context -> ATP_Problem.atp_format -> ATP_Problem_Generate.type_enc ->
    bool -> int Symtab.table -> typ option -> (string, string atp_type) atp_term -> term
  val prop_of_atp : Proof.context -> ATP_Problem.atp_format -> ATP_Problem_Generate.type_enc ->
    bool -> int Symtab.table ->
    (string, string, (string, string atp_type) atp_term, string) atp_formula -> term

  val used_facts_in_atp_proof : Proof.context -> (string * stature) list -> string atp_proof ->
    (string * stature) list
  val used_facts_in_unsound_atp_proof : Proof.context -> (string * stature) list -> 'a atp_proof ->
    string list option
  val atp_proof_prefers_lifting : string atp_proof -> bool
  val is_typed_helper_used_in_atp_proof : string atp_proof -> bool
  val replace_dependencies_in_line : atp_step_name * atp_step_name list -> ('a, 'b) atp_step ->
    ('a, 'b) atp_step
  val termify_atp_proof : Proof.context -> string -> ATP_Problem.atp_format ->
    ATP_Problem_Generate.type_enc -> string Symtab.table -> (string * term) list ->
    int Symtab.table -> string atp_proof -> (term, string) atp_step list
  val repair_waldmeister_endgame : (term, 'a) atp_step list -> (term, 'a) atp_step list
  val infer_formulas_types : Proof.context -> term list -> term list
  val introduce_spass_skolem : (term, string) atp_step list -> (term, string) atp_step list
  val factify_atp_proof : (string * 'a) list -> term list -> term -> (term, string) atp_step list ->
    (term, string) atp_step list
end;

structure ATP_Proof_Reconstruct : ATP_PROOF_RECONSTRUCT =
struct

open ATP_Util
open ATP_Problem
open ATP_Proof
open ATP_Problem_Generate

val metisN = "metis"

val full_typesN = "full_types"
val partial_typesN = "partial_types"
val no_typesN = "no_types"

val really_full_type_enc = "mono_tags"
val full_type_enc = "poly_guards_query"
val partial_type_enc = "poly_args"
val no_type_enc = "erased"

val full_type_encs = [full_type_enc, really_full_type_enc]
val partial_type_encs = partial_type_enc :: full_type_encs

val type_enc_aliases =
  [(full_typesN, full_type_encs),
   (partial_typesN, partial_type_encs),
   (no_typesN, [no_type_enc])]

fun unalias_type_enc s =
  AList.lookup (op =) type_enc_aliases s |> the_default [s]

val default_metis_lam_trans = combsN

fun term_name' (Var ((s, _), _)) = perhaps (try Name.dest_skolem) s
  | term_name' _ = ""

fun lambda' v = Term.lambda_name (term_name' v, v)

fun forall_of v t = HOLogic.all_const (fastype_of v) $ lambda' v t
fun exists_of v t = HOLogic.exists_const (fastype_of v) $ lambda' v t

fun make_tfree ctxt w =
  let val ww = "'" ^ w in
    TFree (ww, the_default @{sort type} (Variable.def_sort ctxt (ww, ~1)))
  end

exception ATP_CLASS of string list
exception ATP_TYPE of string atp_type list
exception ATP_TERM of (string, string atp_type) atp_term list
exception ATP_FORMULA of
  (string, string, (string, string atp_type) atp_term, string) atp_formula list
exception SAME of unit

fun class_of_atp_class cls =
  (case unprefix_and_unascii class_prefix cls of
    SOME s => s
  | NONE => raise ATP_CLASS [cls])

(* Type variables are given the basic sort "HOL.type". Some will later be constrained by information
   from type literals, or by type inference. *)
fun typ_of_atp_type ctxt (ty as AType ((a, clss), tys)) =
    let val Ts = map (typ_of_atp_type ctxt) tys in
      (case unprefix_and_unascii type_const_prefix a of
        SOME b => Type (invert_const b, Ts)
      | NONE =>
        if not (null tys) then
          raise ATP_TYPE [ty] (* only "tconst"s have type arguments *)
        else
          (case unprefix_and_unascii tfree_prefix a of
            SOME b => make_tfree ctxt b
          | NONE =>
            (* The term could be an Isabelle variable or a variable from the ATP, say "X1" or "_5018".
               Sometimes variables from the ATP are indistinguishable from Isabelle variables, which
               forces us to use a type parameter in all cases. *)
            Type_Infer.param 0 ("'" ^ perhaps (unprefix_and_unascii tvar_prefix) a,
              (if null clss then @{sort type} else map class_of_atp_class clss))))
    end
  | typ_of_atp_type ctxt (AFun (ty1, ty2)) = typ_of_atp_type ctxt ty1 --> typ_of_atp_type ctxt ty2

fun atp_type_of_atp_term (ATerm ((s, _), us)) =
  let val tys = map atp_type_of_atp_term us in
    if s = tptp_fun_type then
      (case tys of
        [ty1, ty2] => AFun (ty1, ty2)
      | _ => raise ATP_TYPE tys)
    else
      AType ((s, []), tys)
  end

fun typ_of_atp_term ctxt = typ_of_atp_type ctxt o atp_type_of_atp_term

(* Type class literal applied to a type. Returns triple of polarity, class, type. *)
fun type_constraint_of_term ctxt (u as ATerm ((a, _), us)) =
  (case (unprefix_and_unascii class_prefix a, map (typ_of_atp_term ctxt) us) of
    (SOME b, [T]) => (b, T)
  | _ => raise ATP_TERM [u])

(* Accumulate type constraints in a formula: negative type literals. *)
fun add_var (key, z) = Vartab.map_default (key, []) (cons z)
fun add_type_constraint false (cl, TFree (a ,_)) = add_var ((a, ~1), cl)
  | add_type_constraint false (cl, TVar (ix, _)) = add_var (ix, cl)
  | add_type_constraint _ _ = I

fun repair_var_name_raw s =
  let
    fun subscript_name s n = s ^ nat_subscript n
    val s = s |> String.map Char.toLower
  in
    (case space_explode "_" s of
      [_] =>
      (case take_suffix Char.isDigit (String.explode s) of
        (cs1 as _ :: _, cs2 as _ :: _) =>
        subscript_name (String.implode cs1) (the (Int.fromString (String.implode cs2)))
      | (_, _) => s)
    | [s1, s2] => (case Int.fromString s2 of SOME n => subscript_name s1 n | NONE => s)
    | _ => s)
  end

fun repair_var_name textual s =
  (case unprefix_and_unascii schematic_var_prefix s of
    SOME s => s
  | NONE => s |> textual ? repair_var_name_raw)

(* The number of type arguments of a constant, zero if it's monomorphic. For (instances of) Skolem
   pseudoconstants, this information is encoded in the constant name. *)
fun robust_const_num_type_args thy s =
  if String.isPrefix skolem_const_prefix s then
    s |> Long_Name.explode |> List.last |> Int.fromString |> the
  else if String.isPrefix lam_lifted_prefix s then
    if String.isPrefix lam_lifted_poly_prefix s then 2 else 0
  else
    (s, Sign.the_const_type thy s) |> Sign.const_typargs thy |> length

fun slack_fastype_of t = fastype_of t handle TERM _ => Type_Infer.anyT @{sort type}

(* Cope with "tt(X) = X" atoms, where "X" is existentially quantified. *)
fun loose_aconv (Free (s, _), Free (s', _)) = s = s'
  | loose_aconv (t, t') = t aconv t'

val spass_skolem_prefix = "sk" (* "skc" or "skf" *)
val vampire_skolem_prefix = "sK"

fun var_index_of_textual textual = if textual then 0 else 1

fun quantify_over_var textual quant_of var_s var_T t =
  let
    val vars = ((var_s, var_index_of_textual textual), var_T) ::
                 filter (fn ((s, _), _) => s = var_s) (Term.add_vars t [])
    val normTs = vars |> AList.group (op =) |> map (apsnd hd)
    fun norm_var_types (Var (x, T)) =
        Var (x, the_default T (AList.lookup (op =) normTs x))
      | norm_var_types t = t
  in t |> map_aterms norm_var_types |> fold_rev quant_of (map Var normTs) end


(* Higher-order translation. Variables are typed (although we don't use that information). Lambdas
   are typed.

  The code is similar to term_of_atp_fo. *)
fun term_of_atp_ho ctxt textual sym_tab =
  let
    val thy = Proof_Context.theory_of ctxt
    val var_index = var_index_of_textual textual

    fun do_term opt_T u =
      (case u of
        AAbs(((var, ty), term), []) =>
        let
          val typ = typ_of_atp_type ctxt ty
          val var_name = repair_var_name textual var
          val tm = do_term NONE term
        in quantify_over_var textual lambda' var_name typ tm end
      | ATerm ((s, tys), us) =>
        if s = ""
        then error "Isar proof reconstruction failed because the ATP proof \
                     \contains unparsable material."
        else if s = tptp_equal then
          let
            val ts = map (do_term NONE) us
            fun equal_term ts =
                list_comb (Const (@{const_name HOL.eq}, Type_Infer.anyT @{sort type}), ts)
          in
            if textual then
              (case ts of
                [fst, lst] =>
                if loose_aconv (fst, lst) then
                  @{const True}
                else if Term.aconv_untyped (lst, @{const True}) then
                  fst
                else if Term.aconv_untyped (fst, @{const True}) then
                  lst
                else
                  equal_term ts
              | _ => equal_term ts)
            else
              equal_term ts
          end
        else if not (null us) then
          let
            val args = List.map (do_term NONE) us
            val opt_T' = SOME (map slack_fastype_of args ---> the_default dummyT opt_T)
            val func = do_term opt_T' (ATerm ((s, tys), []))
          in foldl1 (op $) (func :: args) end
        else if s = tptp_or then HOLogic.disj
        else if s = tptp_and then HOLogic.conj
        else if s = tptp_implies then HOLogic.imp
        else if s = tptp_iff orelse s = tptp_equal then HOLogic.eq_const dummyT
        else if s = tptp_not_iff orelse s = tptp_not_equal then @{term "% P Q. Q ~= P"}
        else if s = tptp_if then @{term "% P Q. Q --> P"}
        else if s = tptp_not_and then @{term "% P Q. ~ (P & Q)"}
        else if s = tptp_not_or then @{term "% P Q. ~ (P | Q)"}
        else if s = tptp_not then HOLogic.Not
        else if s = tptp_ho_forall then HOLogic.all_const dummyT
        else if s = tptp_ho_exists then HOLogic.exists_const dummyT
        else
          (case unprefix_and_unascii const_prefix s of
            SOME s' =>
            let
              val ((s', _), mangled_us) = s' |> unmangled_const |>> `invert_const
              val num_ty_args = length us - the_default 0 (Symtab.lookup sym_tab s)
              val (type_us, term_us) = chop num_ty_args us |>> append mangled_us
              val term_ts = map (do_term NONE) term_us
              val Ts = map (typ_of_atp_type ctxt) tys @ map (typ_of_atp_term ctxt) type_us
              val T =
                (if not (null Ts) andalso robust_const_num_type_args thy s' = length Ts then
                   if textual then try (Sign.const_instance thy) (s', Ts) else NONE
                 else
                   NONE)
                |> (fn SOME T => T
                     | NONE =>
                       map slack_fastype_of term_ts --->
                       the_default (Type_Infer.anyT @{sort type}) opt_T)
              val t = Const (unproxify_const s', T)
            in list_comb (t, term_ts) end
          | NONE => (* a free or schematic variable *)
            let
              fun fresh_up s =
                [(s, ())] |> Variable.variant_frees ctxt [] |> hd |> fst
              val ts = map (do_term NONE) us
              val T =
                (case opt_T of
                  SOME T => map slack_fastype_of ts ---> T
                | NONE =>
                  map slack_fastype_of ts --->
                    (case tys of
                      [ty] => typ_of_atp_type ctxt ty
                    | _ => Type_Infer.anyT @{sort type}))
              val t =
                (case unprefix_and_unascii fixed_var_prefix s of
                  SOME s => Free (s, T)
                | NONE =>
                  if textual andalso not (is_tptp_variable s) then
                    Free (s |> textual ? (repair_var_name_raw #> fresh_up), T)
                  else
                    Var ((repair_var_name textual s, var_index), T))
            in list_comb (t, ts) end))
  in do_term end

(* First-order translation. No types are known for variables. "Type_Infer.anyT @{sort type}"
   should allow them to be inferred. *)
fun term_of_atp_fo ctxt textual sym_tab =
  let
    val thy = Proof_Context.theory_of ctxt
    (* For Metis, we use 1 rather than 0 because variable references in clauses may otherwise
       conflict with variable constraints in the goal. At least, type inference often fails
       otherwise. See also "axiom_inference" in "Metis_Reconstruct". *)
    val var_index = var_index_of_textual textual

    fun do_term extra_ts opt_T u =
      (case u of
        ATerm ((s, tys), us) =>
        if s = "" then
          error "Isar proof reconstruction failed because the ATP proof contains unparsable \
            \material."
        else if String.isPrefix native_type_prefix s then
          @{const True} (* ignore TPTP type information *)
        else if s = tptp_equal then
          let val ts = map (do_term [] NONE) us in
            if textual andalso length ts = 2 andalso loose_aconv (hd ts, List.last ts) then
              @{const True}
            else
              list_comb (Const (@{const_name HOL.eq}, Type_Infer.anyT @{sort type}), ts)
          end
        else
          (case unprefix_and_unascii const_prefix s of
            SOME s' =>
            let val ((s', s''), mangled_us) = s' |> unmangled_const |>> `invert_const in
              if s' = type_tag_name then
                (case mangled_us @ us of
                  [typ_u, term_u] => do_term extra_ts (SOME (typ_of_atp_term ctxt typ_u)) term_u
                | _ => raise ATP_TERM us)
              else if s' = predicator_name then
                do_term [] (SOME @{typ bool}) (hd us)
              else if s' = app_op_name then
                let val extra_t = do_term [] NONE (List.last us) in
                  do_term (extra_t :: extra_ts)
                    (case opt_T of SOME T => SOME (slack_fastype_of extra_t --> T) | NONE => NONE)
                    (nth us (length us - 2))
                end
              else if s' = type_guard_name then
                @{const True} (* ignore type predicates *)
              else
                let
                  val new_skolem = String.isPrefix new_skolem_const_prefix s''
                  val num_ty_args = length us - the_default 0 (Symtab.lookup sym_tab s)
                  val (type_us, term_us) = chop num_ty_args us |>> append mangled_us
                  val term_ts = map (do_term [] NONE) term_us

                  val Ts = map (typ_of_atp_type ctxt) tys @ map (typ_of_atp_term ctxt) type_us
                  val T =
                    (if not (null Ts) andalso robust_const_num_type_args thy s' = length Ts then
                       if new_skolem then SOME (Type_Infer.paramify_vars (tl Ts ---> hd Ts))
                       else if textual then try (Sign.const_instance thy) (s', Ts)
                       else NONE
                     else
                       NONE)
                    |> (fn SOME T => T
                         | NONE =>
                           map slack_fastype_of term_ts --->
                           the_default (Type_Infer.anyT @{sort type}) opt_T)
                  val t =
                    if new_skolem then Var ((new_skolem_var_name_of_const s'', var_index), T)
                    else Const (unproxify_const s', T)
                in
                  list_comb (t, term_ts @ extra_ts)
                end
            end
          | NONE => (* a free or schematic variable *)
            let
              (* This assumes that distinct names are mapped to distinct names by
                 "Variable.variant_frees". This does not hold in general but should hold for
                 ATP-generated Skolem function names, since these end with a digit and
                 "variant_frees" appends letters. *)
              fun fresh_up s = [(s, ())] |> Variable.variant_frees ctxt [] |> hd |> fst

              val term_ts =
                map (do_term [] NONE) us
                (* SPASS (3.8ds) and Vampire (2.6) pass arguments to Skolem functions in reverse
                   order, which is incompatible with "metis"'s new skolemizer. *)
                |> exists (fn pre => String.isPrefix pre s)
                  [spass_skolem_prefix, vampire_skolem_prefix] ? rev
              val ts = term_ts @ extra_ts
              val T =
                (case opt_T of
                  SOME T => map slack_fastype_of term_ts ---> T
                | NONE =>
                  map slack_fastype_of ts --->
                  (case tys of [ty] => typ_of_atp_type ctxt ty | _ => Type_Infer.anyT @{sort type}))
              val t =
                (case unprefix_and_unascii fixed_var_prefix s of
                  SOME s => Free (s, T)
                | NONE =>
                  if textual andalso not (is_tptp_variable s) then
                    Free (s |> textual ? (repair_var_name_raw #> fresh_up), T)
                  else
                    Var ((repair_var_name textual s, var_index), T))
            in list_comb (t, ts) end))
  in do_term [] end

fun term_of_atp ctxt (ATP_Problem.THF _) type_enc =
    if ATP_Problem_Generate.is_type_enc_higher_order type_enc
    then term_of_atp_ho ctxt
    else error "Unsupported Isar reconstruction."
  | term_of_atp ctxt _ type_enc =
    if not (ATP_Problem_Generate.is_type_enc_higher_order type_enc)
    then term_of_atp_fo ctxt
    else error "Unsupported Isar reconstruction."

fun term_of_atom ctxt format type_enc textual sym_tab pos (u as ATerm ((s, _), _)) =
  if String.isPrefix class_prefix s then
    add_type_constraint pos (type_constraint_of_term ctxt u)
    #> pair @{const True}
  else
    pair (term_of_atp ctxt format type_enc textual sym_tab (SOME @{typ bool}) u)

(* Update schematic type variables with detected sort constraints. It's not
   totally clear whether this code is necessary. *)
fun repair_tvar_sorts (t, tvar_tab) =
  let
    fun do_type (Type (a, Ts)) = Type (a, map do_type Ts)
      | do_type (TVar (xi, s)) =
        TVar (xi, the_default s (Vartab.lookup tvar_tab xi))
      | do_type (TFree z) = TFree z
    fun do_term (Const (a, T)) = Const (a, do_type T)
      | do_term (Free (a, T)) = Free (a, do_type T)
      | do_term (Var (xi, T)) = Var (xi, do_type T)
      | do_term (t as Bound _) = t
      | do_term (Abs (a, T, t)) = Abs (a, do_type T, do_term t)
      | do_term (t1 $ t2) = do_term t1 $ do_term t2
  in t |> not (Vartab.is_empty tvar_tab) ? do_term end

(* Interpret an ATP formula as a HOL term, extracting sort constraints as they appear in the
   formula. *)
fun prop_of_atp ctxt format type_enc textual sym_tab phi =
  let
    fun do_formula pos phi =
      (case phi of
        AQuant (_, [], phi) => do_formula pos phi
      | AQuant (q, (s, _) :: xs, phi') =>
        do_formula pos (AQuant (q, xs, phi'))
        (* FIXME: TFF *)
        #>> quantify_over_var textual (case q of AForall => forall_of | AExists => exists_of)
          (repair_var_name textual s) dummyT
      | AConn (ANot, [phi']) => do_formula (not pos) phi' #>> s_not
      | AConn (c, [phi1, phi2]) =>
        do_formula (pos |> c = AImplies ? not) phi1
        ##>> do_formula pos phi2
        #>> (case c of
              AAnd => s_conj
            | AOr => s_disj
            | AImplies => s_imp
            | AIff => s_iff
            | ANot => raise Fail "impossible connective")
      | AAtom tm => term_of_atom ctxt format type_enc textual sym_tab pos tm
      | _ => raise ATP_FORMULA [phi])
  in
    repair_tvar_sorts (do_formula true phi Vartab.empty)
  end

val unprefix_fact_number = space_implode "_" o tl o space_explode "_"

fun resolve_fact facts s =
  (case try (unprefix fact_prefix) s of
    SOME s' =>
    let val s' = s' |> unprefix_fact_number |> unascii_of in
      AList.lookup (op =) facts s' |> Option.map (pair s')
    end
  | NONE => NONE)

fun resolve_conjecture s =
  (case try (unprefix conjecture_prefix) s of
    SOME s' => Int.fromString s'
  | NONE => NONE)

fun resolve_facts facts = map_filter (resolve_fact facts)
val resolve_conjectures = map_filter resolve_conjecture

fun is_axiom_used_in_proof pred =
  exists (fn ((_, ss), _, _, _, []) => exists pred ss | _ => false)

val leo2_extcnf_equal_neg_rule = "extcnf_equal_neg"

fun add_fact ctxt facts ((_, ss), _, _, rule, deps) =
  (if member (op =) [agsyhol_core_rule, leo2_extcnf_equal_neg_rule, satallax_core_rule] rule then
     insert (op =) (short_thm_name ctxt ext, (Global, General))
   else
     I)
  #> (if null deps then union (op =) (resolve_facts facts ss) else I)

fun used_facts_in_atp_proof ctxt facts atp_proof =
  if null atp_proof then facts else fold (add_fact ctxt facts) atp_proof []

fun used_facts_in_unsound_atp_proof _ _ [] = NONE
  | used_facts_in_unsound_atp_proof ctxt facts atp_proof =
    let val used_facts = used_facts_in_atp_proof ctxt facts atp_proof in
      if forall (fn (_, (sc, _)) => sc = Global) used_facts andalso
         not (is_axiom_used_in_proof (is_some o resolve_conjecture) atp_proof) then
        SOME (map fst used_facts)
      else
        NONE
    end

val ascii_of_lam_fact_prefix = ascii_of lam_fact_prefix

(* overapproximation (good enough) *)
fun is_lam_lifted s =
  String.isPrefix fact_prefix s andalso
  String.isSubstring ascii_of_lam_fact_prefix s

val is_combinator_def = String.isPrefix (helper_prefix ^ combinator_prefix)

fun atp_proof_prefers_lifting atp_proof =
  (is_axiom_used_in_proof is_combinator_def atp_proof,
   is_axiom_used_in_proof is_lam_lifted atp_proof) = (false, true)

val is_typed_helper_name =
  String.isPrefix helper_prefix andf String.isSuffix typed_helper_suffix

fun is_typed_helper_used_in_atp_proof atp_proof =
  is_axiom_used_in_proof is_typed_helper_name atp_proof

fun replace_one_dependency (old, new) dep = if is_same_atp_step dep old then new else [dep]
fun replace_dependencies_in_line old_new (name, role, t, rule, deps) =
  (name, role, t, rule, fold (union (op =) o replace_one_dependency old_new) deps [])

fun repair_name "$true" = "c_True"
  | repair_name "$false" = "c_False"
  | repair_name "$$e" = tptp_equal (* seen in Vampire proofs *)
  | repair_name s =
    if is_tptp_equal s orelse
       (* seen in Vampire proofs *)
       (String.isPrefix "sQ" s andalso String.isSuffix "_eqProxy" s) then
      tptp_equal
    else
      s

fun set_var_index j = map_aterms (fn Var ((s, 0), T) => Var ((s, j), T) | t => t)

fun infer_formulas_types ctxt =
  map_index (uncurry (fn j => set_var_index j #> Type.constraint HOLogic.boolT))
  #> Syntax.check_terms (Proof_Context.set_mode Proof_Context.mode_schematic ctxt)
  #> map (set_var_index 0)

val combinator_table =
  [(@{const_name Meson.COMBI}, @{thm Meson.COMBI_def [abs_def]}),
   (@{const_name Meson.COMBK}, @{thm Meson.COMBK_def [abs_def]}),
   (@{const_name Meson.COMBB}, @{thm Meson.COMBB_def [abs_def]}),
   (@{const_name Meson.COMBC}, @{thm Meson.COMBC_def [abs_def]}),
   (@{const_name Meson.COMBS}, @{thm Meson.COMBS_def [abs_def]})]

fun uncombine_term thy =
  let
    fun aux (t1 $ t2) = betapply (pairself aux (t1, t2))
      | aux (Abs (s, T, t')) = Abs (s, T, aux t')
      | aux (t as Const (x as (s, _))) =
        (case AList.lookup (op =) combinator_table s of
          SOME thm => thm |> prop_of |> specialize_type thy x |> Logic.dest_equals |> snd
        | NONE => t)
      | aux t = t
  in aux end

fun unlift_term lifted =
  map_aterms (fn t as Const (s, _) =>
                 if String.isPrefix lam_lifted_prefix s then
                   (* FIXME: do something about the types *)
                   (case AList.lookup (op =) lifted s of
                     SOME t => unlift_term lifted t
                   | NONE => t)
                 else
                   t
               | t => t)

fun termify_line _ _ _ _ _ (_, Type_Role, _, _, _) = NONE
  | termify_line ctxt format type_enc lifted sym_tab (name, role, u, rule, deps) =
    let
      val thy = Proof_Context.theory_of ctxt
      val t = u
        |> prop_of_atp ctxt format type_enc true sym_tab
        |> uncombine_term thy
        |> unlift_term lifted
    in
      SOME (name, role, t, rule, deps)
    end

val waldmeister_conjecture_num = "1.0.0.0"

fun repair_waldmeister_endgame proof =
  let
    fun repair_tail (name, _, @{const Trueprop} $ t, rule, deps) =
      (name, Negated_Conjecture, @{const Trueprop} $ s_not t, rule, deps)
    fun repair_body [] = []
      | repair_body ((line as ((num, _), _, _, _, _)) :: lines) =
        if num = waldmeister_conjecture_num then map repair_tail (line :: lines)
        else line :: repair_body lines
  in
    repair_body proof
  end

fun map_proof_terms f (lines : ('a * 'b * 'c * 'd * 'e) list) =
  map2 (fn c => fn (a, b, _, d, e) => (a, b, c, d, e)) (f (map #3 lines)) lines

fun termify_atp_proof ctxt local_prover format type_enc pool lifted sym_tab =
  nasty_atp_proof pool
  #> map_term_names_in_atp_proof repair_name
  #> map_filter (termify_line ctxt format type_enc lifted sym_tab)
  #> map_proof_terms (infer_formulas_types ctxt #> map HOLogic.mk_Trueprop)
  #> local_prover = waldmeisterN ? repair_waldmeister_endgame

fun take_distinct_vars seen ((t as Var _) :: ts) =
    if member (op aconv) seen t then rev seen else take_distinct_vars (t :: seen) ts
  | take_distinct_vars seen _ = rev seen

fun unskolemize_term skos t =
  let
    val is_sko = member (op =) skos

    fun find_args args (t $ u) = find_args (u :: args) t #> find_args [] u
      | find_args _ (Abs (_, _, t)) = find_args [] t
      | find_args args (Free (s, _)) =
        if is_sko s then
          let val new = take_distinct_vars [] args in
            (fn [] => new | old => if length new < length old then new else old)
          end
        else
          I
      | find_args _ _ = I

    val alls = find_args [] t []
    val num_alls = length alls

    fun fix_skos args (t $ u) = fix_skos (fix_skos [] u :: args) t
      | fix_skos args (t as Free (s, T)) =
        if is_sko s then list_comb (Free (s, funpow num_alls body_type T), drop num_alls args)
        else list_comb (t, args)
      | fix_skos [] (Abs (s, T, t)) = Abs (s, T, fix_skos [] t)
      | fix_skos [] t = t
      | fix_skos args t = list_comb (fix_skos [] t, args)

    val t' = fix_skos [] t

    fun add_sko (t as Free (s, _)) = is_sko s ? insert (op aconv) t
      | add_sko _ = I

    val exs = Term.fold_aterms add_sko t' []
  in
    t'
    |> HOLogic.dest_Trueprop
    |> fold exists_of exs |> Term.map_abs_vars (K Name.uu)
    |> fold_rev forall_of alls
    |> HOLogic.mk_Trueprop
  end

fun introduce_spass_skolem [] = []
  | introduce_spass_skolem (proof as (_, _, _, rule1, _) :: _) =
    if rule1 = spass_input_rule then
      let
        fun add_sko (Free (s, _)) = String.isPrefix spass_skolem_prefix s ? insert (op =) s
          | add_sko _ = I

        (* union-find would be faster *)
        fun add_cycle [] = I
          | add_cycle ss =
            fold (fn s => Graph.default_node (s, ())) ss
            #> fold Graph.add_edge (ss ~~ tl ss @ [hd ss])

        val (input_steps, other_steps) = List.partition (null o #5) proof

        val skoss = map (fn (_, _, t, _, _) => Term.fold_aterms add_sko t []) input_steps
        val skoss_input_steps = filter_out (null o fst) (skoss ~~ input_steps)
        val groups = Graph.strong_conn (fold add_cycle skoss Graph.empty)

        fun step_name_of_group skos = (implode skos, [])
        fun in_group group = member (op =) group o hd
        fun group_of sko = the (find_first (fn group => in_group group sko) groups)

        fun new_steps (skoss_steps : (string list * (term, 'a) atp_step) list) group =
          let
            val name = step_name_of_group group
            val name0 = name |>> prefix "0"
            val t =
              skoss_steps
              |> map (snd #> #3 #> HOLogic.dest_Trueprop)
              |> Library.foldr1 s_conj
              |> HOLogic.mk_Trueprop
            val skos = fold (union (op =) o fst) skoss_steps []
            val deps = map (snd #> #1) skoss_steps
          in
            [(name0, Unknown, unskolemize_term skos t, spass_pre_skolemize_rule, deps),
             (name, Unknown, t, spass_skolemize_rule, [name0])]
          end

        val sko_steps =
          maps (fn group => new_steps (filter (in_group group o fst) skoss_input_steps) group)
            groups

        val old_news =
          map (fn (skos, (name, _, _, _, _)) => (name, [step_name_of_group (group_of skos)]))
            skoss_input_steps
        val repair_deps = fold replace_dependencies_in_line old_news
      in
        input_steps @ sko_steps @ map repair_deps other_steps
      end
  else
    proof

fun factify_atp_proof facts hyp_ts concl_t atp_proof =
  let
    fun factify_step ((num, ss), _, t, rule, deps) =
      let
        val (ss', role', t') =
          (case resolve_conjectures ss of
            [j] =>
            if j = length hyp_ts then ([], Conjecture, concl_t) else ([], Hypothesis, nth hyp_ts j)
          | _ =>
            (case resolve_facts facts ss of
              [] => (ss, Plain, t)
            | facts => (map fst facts, Axiom, t)))
      in
        ((num, ss'), role', t', rule, deps)
      end

    val atp_proof = map factify_step atp_proof
    val names = map #1 atp_proof

    fun repair_dep (num, ss) = (num, the_default ss (AList.lookup (op =) names num))
    fun repair_deps (name, role, t, rule, deps) = (name, role, t, rule, map repair_dep deps)
  in
    map repair_deps atp_proof
  end

end;

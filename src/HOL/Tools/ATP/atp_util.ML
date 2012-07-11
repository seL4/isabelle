(*  Title:      HOL/Tools/ATP/atp_util.ML
    Author:     Jasmin Blanchette, TU Muenchen

General-purpose functions used by the ATP module.
*)

signature ATP_UTIL =
sig
  val timestamp : unit -> string
  val hash_string : string -> int
  val hash_term : term -> int
  val strip_spaces : bool -> (char -> bool) -> string -> string
  val strip_spaces_except_between_idents : string -> string
  val nat_subscript : int -> string
  val unyxml : string -> string
  val maybe_quote : string -> string
  val string_from_ext_time : bool * Time.time -> string
  val string_from_time : Time.time -> string
  val type_instance : theory -> typ -> typ -> bool
  val type_generalization : theory -> typ -> typ -> bool
  val type_intersect : theory -> typ -> typ -> bool
  val type_equiv : theory -> typ * typ -> bool
  val varify_type : Proof.context -> typ -> typ
  val instantiate_type : theory -> typ -> typ -> typ -> typ
  val varify_and_instantiate_type : Proof.context -> typ -> typ -> typ -> typ
  val typ_of_dtyp : Datatype.descr -> (Datatype.dtyp * typ) list -> Datatype.dtyp -> typ
  val is_type_surely_finite : Proof.context -> typ -> bool
  val is_type_surely_infinite : Proof.context -> bool -> typ list -> typ -> bool
  val s_not : term -> term
  val s_conj : term * term -> term
  val s_disj : term * term -> term
  val s_imp : term * term -> term
  val s_iff : term * term -> term
  val close_form_prefix : string
  val close_form : term -> term
  val open_form : (string -> string) -> term -> term
  val monomorphic_term : Type.tyenv -> term -> term
  val eta_expand : typ list -> term -> int -> term
  val cong_extensionalize_term : theory -> term -> term
  val abs_extensionalize_term : Proof.context -> term -> term
  val unextensionalize_def : term -> term
  val is_legitimate_tptp_def : term -> bool
  val transform_elim_prop : term -> term
  val specialize_type : theory -> (string * typ) -> term -> term
  val strip_subgoal :
    Proof.context -> thm -> int -> (string * typ) list * term list * term
end;

structure ATP_Util : ATP_UTIL =
struct

val timestamp = Date.fmt "%Y-%m-%d %H:%M:%S" o Date.fromTimeLocal o Time.now

(* This hash function is recommended in "Compilers: Principles, Techniques, and
   Tools" by Aho, Sethi, and Ullman. The "hashpjw" function, which they
   particularly recommend, triggers a bug in versions of Poly/ML up to 4.2.0. *)
fun hashw (u, w) = Word.+ (u, Word.* (0w65599, w))
fun hashw_char (c, w) = hashw (Word.fromInt (Char.ord c), w)
fun hashw_string (s : string, w) = CharVector.foldl hashw_char w s
fun hashw_term (t1 $ t2) = hashw (hashw_term t1, hashw_term t2)
  | hashw_term (Const (s, _)) = hashw_string (s, 0w0)
  | hashw_term (Free (s, _)) = hashw_string (s, 0w0)
  | hashw_term _ = 0w0

fun hash_string s = Word.toInt (hashw_string (s, 0w0))
val hash_term = Word.toInt o hashw_term

fun strip_spaces skip_comments is_evil =
  let
    fun strip_c_style_comment [] accum = accum
      | strip_c_style_comment (#"*" :: #"/" :: cs) accum =
        strip_spaces_in_list true cs accum
      | strip_c_style_comment (_ :: cs) accum = strip_c_style_comment cs accum
    and strip_spaces_in_list _ [] accum = rev accum
      | strip_spaces_in_list true (#"%" :: cs) accum =
        strip_spaces_in_list true (cs |> chop_while (not_equal #"\n") |> snd)
                             accum
      | strip_spaces_in_list true (#"/" :: #"*" :: cs) accum =
        strip_c_style_comment cs accum
      | strip_spaces_in_list _ [c1] accum =
        accum |> not (Char.isSpace c1) ? cons c1
      | strip_spaces_in_list skip_comments (cs as [_, _]) accum =
        accum |> fold (strip_spaces_in_list skip_comments o single) cs
      | strip_spaces_in_list skip_comments (c1 :: c2 :: c3 :: cs) accum =
        if Char.isSpace c1 then
          strip_spaces_in_list skip_comments (c2 :: c3 :: cs) accum
        else if Char.isSpace c2 then
          if Char.isSpace c3 then
            strip_spaces_in_list skip_comments (c1 :: c3 :: cs) accum
          else
            strip_spaces_in_list skip_comments (c3 :: cs)
                (c1 :: accum |> forall is_evil [c1, c3] ? cons #" ")
        else
          strip_spaces_in_list skip_comments (c2 :: c3 :: cs) (cons c1 accum)
  in
    String.explode
    #> rpair [] #-> strip_spaces_in_list skip_comments
    #> rev #> String.implode
  end

fun is_ident_char c = Char.isAlphaNum c orelse c = #"_"
val strip_spaces_except_between_idents = strip_spaces true is_ident_char

val subscript = implode o map (prefix "\<^isub>") o raw_explode  (* FIXME Symbol.explode (?) *)
fun nat_subscript n =
  n |> string_of_int |> print_mode_active Symbol.xsymbolsN ? subscript

val unyxml = XML.content_of o YXML.parse_body

val is_long_identifier = forall Lexicon.is_identifier o Long_Name.explode
fun maybe_quote y =
  let val s = unyxml y in
    y |> ((not (is_long_identifier (perhaps (try (unprefix "'")) s)) andalso
           not (is_long_identifier (perhaps (try (unprefix "?")) s))) orelse
           Keyword.is_keyword s) ? quote
  end

fun string_from_ext_time (plus, time) =
  let val ms = Time.toMilliseconds time in
    (if plus then "> " else "") ^
    (if plus andalso ms mod 1000 = 0 then
       signed_string_of_int (ms div 1000) ^ " s"
     else if ms < 1000 then
       signed_string_of_int ms ^ " ms"
     else
       string_of_real (0.01 * Real.fromInt (ms div 10)) ^ " s")
  end

val string_from_time = string_from_ext_time o pair false

fun type_instance thy T T' = Sign.typ_instance thy (T, T')
fun type_generalization thy T T' = Sign.typ_instance thy (T', T)

fun type_intersect _ (TVar _) _ = true
  | type_intersect _ _ (TVar _) = true
  | type_intersect thy T T' =
    let
      val tvars = Term.add_tvar_namesT T []
      val tvars' = Term.add_tvar_namesT T' []
      val T =
        if exists (member (op =) tvars') tvars then
          T |> Logic.incr_tvar (maxidx_of_typ T' + 1)
        else
          T
    in can (Sign.typ_unify thy (T, T')) (Vartab.empty, 0) end

val type_equiv = Sign.typ_equiv

fun varify_type ctxt T =
  Variable.polymorphic_types ctxt [Const (@{const_name undefined}, T)]
  |> snd |> the_single |> dest_Const |> snd

(* TODO: use "Term_Subst.instantiateT" instead? *)
fun instantiate_type thy T1 T1' T2 =
  Same.commit (Envir.subst_type_same
                   (Sign.typ_match thy (T1, T1') Vartab.empty)) T2
  handle Type.TYPE_MATCH => raise TYPE ("instantiate_type", [T1, T1'], [])

fun varify_and_instantiate_type ctxt T1 T1' T2 =
  let val thy = Proof_Context.theory_of ctxt in
    instantiate_type thy (varify_type ctxt T1) T1' (varify_type ctxt T2)
  end

fun typ_of_dtyp _ typ_assoc (Datatype.DtTFree a) =
    the (AList.lookup (op =) typ_assoc (Datatype.DtTFree a))
  | typ_of_dtyp descr typ_assoc (Datatype.DtType (s, Us)) =
    Type (s, map (typ_of_dtyp descr typ_assoc) Us)
  | typ_of_dtyp descr typ_assoc (Datatype.DtRec i) =
    let val (s, ds, _) = the (AList.lookup (op =) descr i) in
      Type (s, map (typ_of_dtyp descr typ_assoc) ds)
    end

fun datatype_constrs thy (T as Type (s, Ts)) =
    (case Datatype.get_info thy s of
       SOME {index, descr, ...} =>
       let val (_, dtyps, constrs) = AList.lookup (op =) descr index |> the in
         map (apsnd (fn Us => map (typ_of_dtyp descr (dtyps ~~ Ts)) Us ---> T))
             constrs
       end
     | NONE => [])
  | datatype_constrs _ _ = []

(* Similar to "Nitpick_HOL.bounded_exact_card_of_type".
   0 means infinite type, 1 means singleton type (e.g., "unit"), and 2 means
   cardinality 2 or more. The specified default cardinality is returned if the
   cardinality of the type can't be determined. *)
fun tiny_card_of_type ctxt sound assigns default_card T =
  let
    val thy = Proof_Context.theory_of ctxt
    val max = 2 (* 1 would be too small for the "fun" case *)
    fun aux slack avoid T =
      if member (op =) avoid T then
        0
      else case AList.lookup (type_equiv thy) assigns T of
        SOME k => k
      | NONE =>
        case T of
          Type (@{type_name fun}, [T1, T2]) =>
          (case (aux slack avoid T1, aux slack avoid T2) of
             (k, 1) => if slack andalso k = 0 then 0 else 1
           | (0, _) => 0
           | (_, 0) => 0
           | (k1, k2) =>
             if k1 >= max orelse k2 >= max then max
             else Int.min (max, Integer.pow k2 k1))
        | Type (@{type_name set}, [T']) => aux slack avoid (T' --> @{typ bool})
        | @{typ prop} => 2
        | @{typ bool} => 2 (* optimization *)
        | @{typ nat} => 0 (* optimization *)
        | Type ("Int.int", []) => 0 (* optimization *)
        | Type (s, _) =>
          (case datatype_constrs thy T of
             constrs as _ :: _ =>
             let
               val constr_cards =
                 map (Integer.prod o map (aux slack (T :: avoid)) o binder_types
                      o snd) constrs
             in
               if exists (curry (op =) 0) constr_cards then 0
               else Int.min (max, Integer.sum constr_cards)
             end
           | [] =>
             case Typedef.get_info ctxt s of
               ({abs_type, rep_type, ...}, _) :: _ =>
               if not sound then
                 (* We cheat here by assuming that typedef types are infinite if
                    their underlying type is infinite. This is unsound in
                    general but it's hard to think of a realistic example where
                    this would not be the case. We are also slack with
                    representation types: If a representation type has the form
                    "sigma => tau", we consider it enough to check "sigma" for
                    infiniteness. *)
                 (case varify_and_instantiate_type ctxt
                           (Logic.varifyT_global abs_type) T
                           (Logic.varifyT_global rep_type)
                       |> aux true avoid of
                    0 => 0
                  | 1 => 1
                  | _ => default_card)
               else
                 default_card
             | [] => default_card)
          (* Very slightly unsound: Type variables are assumed not to be
             constrained to cardinality 1. (In practice, the user would most
             likely have used "unit" directly anyway.) *)
        | TFree _ =>
          if not sound andalso default_card = 1 then 2 else default_card
        | TVar _ => default_card
  in Int.min (max, aux false [] T) end

fun is_type_surely_finite ctxt T = tiny_card_of_type ctxt true [] 0 T <> 0
fun is_type_surely_infinite ctxt sound infinite_Ts T =
  tiny_card_of_type ctxt sound (map (rpair 0) infinite_Ts) 1 T = 0

(* Simple simplifications to ensure that sort annotations don't leave a trail of
   spurious "True"s. *)
fun s_not (Const (@{const_name All}, T) $ Abs (s, T', t')) =
    Const (@{const_name Ex}, T) $ Abs (s, T', s_not t')
  | s_not (Const (@{const_name Ex}, T) $ Abs (s, T', t')) =
    Const (@{const_name All}, T) $ Abs (s, T', s_not t')
  | s_not (@{const HOL.implies} $ t1 $ t2) = @{const HOL.conj} $ t1 $ s_not t2
  | s_not (@{const HOL.conj} $ t1 $ t2) =
    @{const HOL.disj} $ s_not t1 $ s_not t2
  | s_not (@{const HOL.disj} $ t1 $ t2) =
    @{const HOL.conj} $ s_not t1 $ s_not t2
  | s_not (@{const False}) = @{const True}
  | s_not (@{const True}) = @{const False}
  | s_not (@{const Not} $ t) = t
  | s_not t = @{const Not} $ t
fun s_conj (@{const True}, t2) = t2
  | s_conj (t1, @{const True}) = t1
  | s_conj p = HOLogic.mk_conj p
fun s_disj (@{const False}, t2) = t2
  | s_disj (t1, @{const False}) = t1
  | s_disj p = HOLogic.mk_disj p
fun s_imp (@{const True}, t2) = t2
  | s_imp (t1, @{const False}) = s_not t1
  | s_imp p = HOLogic.mk_imp p
fun s_iff (@{const True}, t2) = t2
  | s_iff (t1, @{const True}) = t1
  | s_iff (t1, t2) = HOLogic.eq_const HOLogic.boolT $ t1 $ t2

val close_form_prefix = "ATP.close_form."

fun close_form t =
  fold (fn ((s, i), T) => fn t' =>
           HOLogic.all_const T
           $ Abs (close_form_prefix ^ s, T,
                  abstract_over (Var ((s, i), T), t')))
       (Term.add_vars t []) t

fun open_form unprefix (t as Const (@{const_name All}, _) $ Abs (s, T, t')) =
    (case try unprefix s of
       SOME s =>
       let
         val names = Name.make_context (map fst (Term.add_var_names t' []))
         val (s, _) = Name.variant s names
       in open_form unprefix (subst_bound (Var ((s, 0), T), t')) end
     | NONE => t)
  | open_form _ t = t

fun monomorphic_term subst =
  map_types (map_type_tvar (fn v =>
      case Type.lookup subst v of
        SOME typ => typ
      | NONE => TVar v))

fun eta_expand _ t 0 = t
  | eta_expand Ts (Abs (s, T, t')) n =
    Abs (s, T, eta_expand (T :: Ts) t' (n - 1))
  | eta_expand Ts t n =
    fold_rev (fn T => fn t' => Abs ("x" ^ nat_subscript n, T, t'))
             (List.take (binder_types (fastype_of1 (Ts, t)), n))
             (list_comb (incr_boundvars n t, map Bound (n - 1 downto 0)))

fun cong_extensionalize_term thy t =
  if exists_Const (fn (s, _) => s = @{const_name Not}) t then
    t |> Skip_Proof.make_thm thy
      |> Meson.cong_extensionalize_thm thy
      |> prop_of
  else
    t

fun is_fun_equality (@{const_name HOL.eq},
                     Type (_, [Type (@{type_name fun}, _), _])) = true
  | is_fun_equality _ = false

fun abs_extensionalize_term ctxt t =
  if exists_Const is_fun_equality t then
    let val thy = Proof_Context.theory_of ctxt in
      t |> cterm_of thy |> Meson.abs_extensionalize_conv ctxt
        |> prop_of |> Logic.dest_equals |> snd
    end
  else
    t

fun unextensionalize_def t =
  case t of
    @{const Trueprop} $ (Const (@{const_name HOL.eq}, _) $ lhs $ rhs) =>
    (case strip_comb lhs of
       (c as Const (_, T), args) =>
       if forall is_Var args andalso not (has_duplicates (op =) args) then
         @{const Trueprop}
         $ (Const (@{const_name HOL.eq}, T --> T --> @{typ bool})
            $ c $ fold_rev lambda args rhs)
       else
         t
     | _ => t)
  | _ => t

fun is_legitimate_tptp_def (@{const Trueprop} $ t) = is_legitimate_tptp_def t
  | is_legitimate_tptp_def (Const (@{const_name HOL.eq}, _) $ t $ u) =
    (is_Const t orelse is_Free t) andalso
    not (exists_subterm (curry (op =) t) u)
  | is_legitimate_tptp_def _ = false

(* Converts an elim-rule into an equivalent theorem that does not have the
   predicate variable. Leaves other theorems unchanged. We simply instantiate
   the conclusion variable to "False". (Cf. "transform_elim_theorem" in
   "Meson_Clausify".) *)
fun transform_elim_prop t =
  case Logic.strip_imp_concl t of
    @{const Trueprop} $ Var (z, @{typ bool}) =>
    subst_Vars [(z, @{const False})] t
  | Var (z, @{typ prop}) => subst_Vars [(z, @{prop False})] t
  | _ => t

fun specialize_type thy (s, T) t =
  let
    fun subst_for (Const (s', T')) =
      if s = s' then
        SOME (Sign.typ_match thy (T', T) Vartab.empty)
        handle Type.TYPE_MATCH => NONE
      else
        NONE
    | subst_for (t1 $ t2) =
      (case subst_for t1 of SOME x => SOME x | NONE => subst_for t2)
    | subst_for (Abs (_, _, t')) = subst_for t'
    | subst_for _ = NONE
  in
    case subst_for t of
      SOME subst => monomorphic_term subst t
    | NONE => raise Type.TYPE_MATCH
  end

fun strip_subgoal ctxt goal i =
  let
    val (t, (frees, params)) =
      Logic.goal_params (prop_of goal) i
      ||> (map dest_Free #> Variable.variant_frees ctxt [] #> `(map Free))
    val hyp_ts = t |> Logic.strip_assums_hyp |> map (curry subst_bounds frees)
    val concl_t = t |> Logic.strip_assums_concl |> curry subst_bounds frees
  in (rev params, hyp_ts, concl_t) end

end;

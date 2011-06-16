(*  Title:      HOL/Tools/ATP/atp_util.ML
    Author:     Jasmin Blanchette, TU Muenchen

General-purpose functions used by the ATP module.
*)

signature ATP_UTIL =
sig
  val timestamp : unit -> string
  val hashw : word * word -> word
  val hashw_string : string * word -> word
  val strip_spaces : bool -> (char -> bool) -> string -> string
  val nat_subscript : int -> string
  val unyxml : string -> string
  val maybe_quote : string -> string
  val string_from_ext_time : bool * Time.time -> string
  val string_from_time : Time.time -> string
  val varify_type : Proof.context -> typ -> typ
  val instantiate_type : theory -> typ -> typ -> typ -> typ
  val varify_and_instantiate_type : Proof.context -> typ -> typ -> typ -> typ
  val typ_of_dtyp :
    Datatype_Aux.descr -> (Datatype_Aux.dtyp * typ) list -> Datatype_Aux.dtyp
    -> typ
  val is_type_surely_finite : Proof.context -> typ -> bool
  val is_type_surely_infinite : Proof.context -> typ -> bool
  val monomorphic_term : Type.tyenv -> term -> term
  val eta_expand : typ list -> term -> int -> term
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

fun strip_c_style_comment _ [] = []
  | strip_c_style_comment is_evil (#"*" :: #"/" :: cs) =
    strip_spaces_in_list true is_evil cs
  | strip_c_style_comment is_evil (_ :: cs) = strip_c_style_comment is_evil cs
and strip_spaces_in_list _ _ [] = []
  | strip_spaces_in_list true is_evil (#"%" :: cs) =
    strip_spaces_in_list true is_evil
                         (cs |> chop_while (not_equal #"\n") |> snd)
  | strip_spaces_in_list true is_evil (#"/" :: #"*" :: cs) =
    strip_c_style_comment is_evil cs
  | strip_spaces_in_list _ _ [c1] = if Char.isSpace c1 then [] else [str c1]
  | strip_spaces_in_list skip_comments is_evil [c1, c2] =
    strip_spaces_in_list skip_comments is_evil [c1] @
    strip_spaces_in_list skip_comments is_evil [c2]
  | strip_spaces_in_list skip_comments is_evil (c1 :: c2 :: c3 :: cs) =
    if Char.isSpace c1 then
      strip_spaces_in_list skip_comments is_evil (c2 :: c3 :: cs)
    else if Char.isSpace c2 then
      if Char.isSpace c3 then
        strip_spaces_in_list skip_comments is_evil (c1 :: c3 :: cs)
      else
        str c1 :: (if forall is_evil [c1, c3] then [" "] else []) @
        strip_spaces_in_list skip_comments is_evil (c3 :: cs)
    else
      str c1 :: strip_spaces_in_list skip_comments is_evil (c2 :: c3 :: cs)
fun strip_spaces skip_comments is_evil =
  implode o strip_spaces_in_list skip_comments is_evil o String.explode

val subscript = implode o map (prefix "\<^isub>") o raw_explode  (* FIXME Symbol.explode (?) *)
fun nat_subscript n =
  n |> string_of_int |> print_mode_active Symbol.xsymbolsN ? subscript

val unyxml = XML.content_of o YXML.parse_body

val is_long_identifier = forall Lexicon.is_identifier o space_explode "."
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

fun typ_of_dtyp _ typ_assoc (Datatype_Aux.DtTFree a) =
    the (AList.lookup (op =) typ_assoc (Datatype_Aux.DtTFree a))
  | typ_of_dtyp descr typ_assoc (Datatype_Aux.DtType (s, Us)) =
    Type (s, map (typ_of_dtyp descr typ_assoc) Us)
  | typ_of_dtyp descr typ_assoc (Datatype_Aux.DtRec i) =
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
fun tiny_card_of_type ctxt default_card T =
  let
    val thy = Proof_Context.theory_of ctxt
    val max = 2 (* 1 would be too small for the "fun" case *)
    fun aux slack avoid T =
      if member (op =) avoid T then
        0
      else case T of
        Type (@{type_name fun}, [T1, T2]) =>
        (case (aux slack avoid T1, aux slack avoid T2) of
           (k, 1) => if slack andalso k = 0 then 0 else 1
         | (0, _) => 0
         | (_, 0) => 0
         | (k1, k2) =>
           if k1 >= max orelse k2 >= max then max
           else Int.min (max, Integer.pow k2 k1))
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
             (* We cheat here by assuming that typedef types are infinite if
                their underlying type is infinite. This is unsound in general
                but it's hard to think of a realistic example where this would
                not be the case. We are also slack with representation types:
                If a representation type has the form "sigma => tau", we
                consider it enough to check "sigma" for infiniteness. (Look
                for "slack" in this function.) *)
             (case varify_and_instantiate_type ctxt
                       (Logic.varifyT_global abs_type) T
                       (Logic.varifyT_global rep_type)
                   |> aux true avoid of
                0 => 0
              | 1 => 1
              | _ => default_card)
           | [] => default_card)
        (* Very slightly unsound: Type variables are assumed not to be
           constrained to cardinality 1. (In practice, the user would most
           likely have used "unit" directly anyway.) *)
      | TFree _ => if default_card = 1 then 2 else default_card
      | TVar _ => default_card
  in Int.min (max, aux false [] T) end

fun is_type_surely_finite ctxt T = tiny_card_of_type ctxt 0 T <> 0
fun is_type_surely_infinite ctxt T = tiny_card_of_type ctxt 1 T = 0

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

(* Converts an elim-rule into an equivalent theorem that does not have the
   predicate variable. Leaves other theorems unchanged. We simply instantiate
   the conclusion variable to False. (Cf. "transform_elim_theorem" in
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

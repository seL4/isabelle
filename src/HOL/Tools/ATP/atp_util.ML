(*  Title:      HOL/Tools/ATP/atp_util.ML
    Author:     Jasmin Blanchette, TU Muenchen

General-purpose functions used by the ATP module.
*)

signature ATP_UTIL =
sig
  val timestamp : unit -> string
  val hashw : word * word -> word
  val hashw_string : string * word -> word
  val hash_string : string -> int
  val chunk_list : int -> 'a list -> 'a list list
  val stringN_of_int : int -> int -> string
  val strip_spaces : bool -> (char -> bool) -> string -> string
  val strip_spaces_except_between_idents : string -> string
  val elide_string : int -> string -> string
  val find_enclosed : string -> string -> string -> string list
  val nat_subscript : int -> string
  val unquote_tvar : string -> string
  val maybe_quote : Keyword.keywords -> string -> string
  val string_of_ext_time : bool * Time.time -> string
  val string_of_time : Time.time -> string
  val type_instance : theory -> typ -> typ -> bool
  val type_generalization : theory -> typ -> typ -> bool
  val type_intersect : theory -> typ -> typ -> bool
  val type_equiv : theory -> typ * typ -> bool
  val varify_type : Proof.context -> typ -> typ
  val instantiate_type : theory -> typ -> typ -> typ -> typ
  val varify_and_instantiate_type : Proof.context -> typ -> typ -> typ -> typ
  val is_type_surely_finite : Proof.context -> typ -> bool
  val is_type_surely_infinite : Proof.context -> bool -> typ list -> typ -> bool
  val s_not : term -> term
  val s_conj : term * term -> term
  val s_disj : term * term -> term
  val s_imp : term * term -> term
  val s_iff : term * term -> term
  val close_form : term -> term
  val hol_close_form_prefix : string
  val hol_close_form : term -> term
  val hol_open_form : (string -> string) -> term -> term
  val eta_expand : typ list -> term -> int -> term
  val cong_extensionalize_term : Proof.context -> term -> term
  val abs_extensionalize_term : Proof.context -> term -> term
  val unextensionalize_def : term -> term
  val transform_elim_prop : term -> term
  val specialize_type : theory -> (string * typ) -> term -> term
  val strip_subgoal : thm -> int -> Proof.context -> (string * typ) list * term list * term
  val extract_lambda_def : (term -> string * typ) -> term -> string * term
  val short_thm_name : Proof.context -> thm -> string
  val map_prod : ('a -> 'b) -> ('c -> 'd) -> 'a * 'c -> 'b * 'd
end;

structure ATP_Util : ATP_UTIL =
struct

fun timestamp_format time =
  Date.fmt "%Y-%m-%d %H:%M:%S." (Date.fromTimeLocal time) ^
  (StringCvt.padLeft #"0" 3 (string_of_int (Time.toMilliseconds time - 1000 * Time.toSeconds time)))

val timestamp = timestamp_format o Time.now

(* This hash function is recommended in "Compilers: Principles, Techniques, and
   Tools" by Aho, Sethi, and Ullman. The "hashpjw" function, which they
   particularly recommend, triggers a bug in versions of Poly/ML up to 4.2.0. *)
fun hashw (u, w) = Word.+ (u, Word.* (0w65599, w))
fun hashw_char (c, w) = hashw (Word.fromInt (Char.ord c), w)
fun hashw_string (s : string, w) = CharVector.foldl hashw_char w s
fun hash_string s = Word.toInt (hashw_string (s, 0w0))

fun chunk_list _ [] = []
  | chunk_list k xs =
    let val (xs1, xs2) = chop k xs in xs1 :: chunk_list k xs2 end

fun stringN_of_int 0 _ = ""
  | stringN_of_int k n =
    stringN_of_int (k - 1) (n div 10) ^ string_of_int (n mod 10)

fun is_spaceish c = Char.isSpace c orelse c = #"\127" (* DEL -- no idea where these come from *)

fun strip_spaces skip_comments is_evil =
  let
    fun strip_c_style_comment [] accum = accum
      | strip_c_style_comment (#"*" :: #"/" :: cs) accum = strip_spaces_in_list true cs accum
      | strip_c_style_comment (_ :: cs) accum = strip_c_style_comment cs accum
    and strip_spaces_in_list _ [] accum = accum
      | strip_spaces_in_list true (#"%" :: cs) accum =
        strip_spaces_in_list true (cs |> drop_prefix (not_equal #"\n")) accum
      | strip_spaces_in_list true (#"/" :: #"*" :: cs) accum = strip_c_style_comment cs accum
      | strip_spaces_in_list _ [c1] accum = accum |> not (is_spaceish c1) ? cons c1
      | strip_spaces_in_list skip_comments (cs as [_, _]) accum =
        accum |> fold (strip_spaces_in_list skip_comments o single) cs
      | strip_spaces_in_list skip_comments (c1 :: c2 :: c3 :: cs) accum =
        if is_spaceish c1 then
          strip_spaces_in_list skip_comments (c2 :: c3 :: cs) accum
        else if is_spaceish c2 then
          if is_spaceish c3 then
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

fun elide_string threshold s =
  if size s > threshold then
    String.extract (s, 0, SOME (threshold div 2 - 5)) ^ " ...... " ^
    String.extract (s, size s - (threshold + 1) div 2 + 6, NONE)
  else
    s

fun find_enclosed left right s =
  case first_field left s of
    SOME (_, s) =>
    (case first_field right s of
       SOME (enclosed, s) => enclosed :: find_enclosed left right s
     | NONE => [])
  | NONE => []

val subscript = implode o map (prefix "\<^sub>") o raw_explode  (* FIXME Symbol.explode (?) *)
fun nat_subscript n =
  n |> string_of_int |> not (print_mode_active Print_Mode.ASCII) ? subscript

val unquote_tvar = perhaps (try (unprefix "'"))
val unquery_var = perhaps (try (unprefix "?"))

val is_long_identifier = forall Symbol_Pos.is_identifier o Long_Name.explode
fun maybe_quote keywords y =
  let val s = YXML.content_of y in
    y |> ((not (is_long_identifier (unquote_tvar s)) andalso
           not (is_long_identifier (unquery_var s))) orelse
           Keyword.is_literal keywords s) ? quote
  end

fun string_of_ext_time (plus, time) =
  let val us = Time.toMicroseconds time in
    (if plus then "> " else "") ^
    (if us < 1000 then string_of_real (Real.fromInt (us div 100) / 10.0) ^ " ms"
     else if us < 1000000 then signed_string_of_int (us div 1000) ^ " ms"
     else string_of_real (Real.fromInt (us div 100000) / 10.0) ^ " s")
  end

val string_of_time = string_of_ext_time o pair false

fun type_instance thy T T' = Sign.typ_instance thy (T, T')
fun type_generalization thy T T' = Sign.typ_instance thy (T', T)

fun type_intersect _ (TVar _) _ = true
  | type_intersect _ _ (TVar _) = true
  | type_intersect thy T T' =
    let
      val tvars = Term.add_tvar_namesT T []
      val tvars' = Term.add_tvar_namesT T' []
      val maxidx' = maxidx_of_typ T'
      val T =
        T |> exists (member (op =) tvars') tvars ? Logic.incr_tvar (maxidx' + 1)
      val maxidx = Integer.max (maxidx_of_typ T) maxidx'
    in can (Sign.typ_unify thy (T, T')) (Vartab.empty, maxidx) end

val type_equiv = Sign.typ_equiv

fun varify_type ctxt T =
  Variable.polymorphic_types ctxt [Const (\<^const_name>\<open>undefined\<close>, T)]
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

fun free_constructors_of ctxt (Type (s, Ts)) =
    (case Ctr_Sugar.ctr_sugar_of ctxt s of
      SOME {ctrs, ...} => map_filter (try dest_Const o Ctr_Sugar.mk_ctr Ts) ctrs
    | NONE => [])
  | free_constructors_of _ _ = []

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
          Type (\<^type_name>\<open>fun\<close>, [T1, T2]) =>
          (case (aux slack avoid T1, aux slack avoid T2) of
             (k, 1) => if slack andalso k = 0 then 0 else 1
           | (0, _) => 0
           | (_, 0) => 0
           | (k1, k2) =>
             if k1 >= max orelse k2 >= max then max
             else Int.min (max, Integer.pow k2 k1))
        | Type (\<^type_name>\<open>set\<close>, [T']) => aux slack avoid (T' --> \<^typ>\<open>bool\<close>)
        | \<^typ>\<open>prop\<close> => 2
        | \<^typ>\<open>bool\<close> => 2 (* optimization *)
        | \<^typ>\<open>nat\<close> => 0 (* optimization *)
        | Type ("Int.int", []) => 0 (* optimization *)
        | Type (s, _) =>
          (case free_constructors_of ctxt T of
             constrs as _ :: _ =>
             let
               val constr_cards =
                 map (Integer.prod o map (aux slack (T :: avoid)) o binder_types o snd) constrs
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
        | TFree _ =>
          (* Very slightly unsound: Type variables are assumed not to be
             constrained to cardinality 1. (In practice, the user would most
             likely have used "unit" directly anyway.) *)
          if not sound andalso default_card = 1 then 2 else default_card
        | TVar _ => default_card
  in Int.min (max, aux false [] T) end

fun is_type_surely_finite ctxt T = tiny_card_of_type ctxt true [] 0 T <> 0
fun is_type_surely_infinite ctxt sound infinite_Ts T =
  tiny_card_of_type ctxt sound (map (rpair 0) infinite_Ts) 1 T = 0

(* Simple simplifications to ensure that sort annotations don't leave a trail of
   spurious "True"s. *)
fun s_not \<^Const_>\<open>All T for \<open>Abs (s, T', t')\<close>\<close> = \<^Const>\<open>Ex T for \<open>Abs (s, T', s_not t')\<close>\<close>
  | s_not \<^Const_>\<open>Ex T for \<open>Abs (s, T', t')\<close>\<close> = \<^Const>\<open>All T for \<open>Abs (s, T', s_not t')\<close>\<close>
  | s_not \<^Const_>\<open>implies for t1 t2\<close> = \<^Const>\<open>conj for t1 \<open>s_not t2\<close>\<close>
  | s_not \<^Const_>\<open>conj for t1 t2\<close> = \<^Const>\<open>disj for \<open>s_not t1\<close> \<open>s_not t2\<close>\<close> 
  | s_not \<^Const_>\<open>disj for t1 t2\<close> = \<^Const>\<open>conj for \<open>s_not t1\<close> \<open>s_not t2\<close>\<close>
  | s_not \<^Const_>\<open>False\<close> = \<^Const>\<open>True\<close>
  | s_not \<^Const_>\<open>True\<close> = \<^Const>\<open>False\<close>
  | s_not \<^Const_>\<open>Not for t\<close> = t
  | s_not t = \<^Const>\<open>Not for t\<close>

fun s_conj (\<^Const_>\<open>True\<close>, t2) = t2
  | s_conj (t1, \<^Const_>\<open>True\<close>) = t1
  | s_conj (\<^Const_>\<open>False\<close>, _) = \<^Const>\<open>False\<close>
  | s_conj (_, \<^Const_>\<open>False\<close>) = \<^Const>\<open>False\<close>
  | s_conj (t1, t2) = if t1 aconv t2 then t1 else HOLogic.mk_conj (t1, t2)

fun s_disj (\<^Const_>\<open>False\<close>, t2) = t2
  | s_disj (t1, \<^Const_>\<open>False\<close>) = t1
  | s_disj (\<^Const_>\<open>True\<close>, _) = \<^Const>\<open>True\<close>
  | s_disj (_, \<^Const_>\<open>True\<close>) = \<^Const>\<open>True\<close>
  | s_disj (t1, t2) = if t1 aconv t2 then t1 else HOLogic.mk_disj (t1, t2)

fun s_imp (\<^Const_>\<open>True\<close>, t2) = t2
  | s_imp (t1, \<^Const_>\<open>False\<close>) = s_not t1
  | s_imp (\<^Const_>\<open>False\<close>, _) = \<^Const>\<open>True\<close>
  | s_imp (_, \<^Const_>\<open>True\<close>) = \<^Const>\<open>True\<close>
  | s_imp p = HOLogic.mk_imp p

fun s_iff (\<^Const_>\<open>True\<close>, t2) = t2
  | s_iff (t1, \<^Const_>\<open>True\<close>) = t1
  | s_iff (\<^Const_>\<open>False\<close>, t2) = s_not t2
  | s_iff (t1, \<^Const_>\<open>False\<close>) = s_not t1
  | s_iff (t1, t2) = if t1 aconv t2 then \<^Const>\<open>True\<close> else HOLogic.eq_const HOLogic.boolT $ t1 $ t2

fun close_form t =
  fold (fn ((s, i), T) => fn t' =>
      Logic.all_const T $ Abs (s, T, abstract_over (Var ((s, i), T), t')))
    (Term.add_vars t []) t

val hol_close_form_prefix = "ATP."

fun hol_close_form t =
  fold (fn ((s, i), T) => fn t' =>
           HOLogic.all_const T
           $ Abs (hol_close_form_prefix ^ s, T,
                  abstract_over (Var ((s, i), T), t')))
       (Term.add_vars t []) t

fun hol_open_form unprefix
      (t as Const (\<^const_name>\<open>All\<close>, _) $ Abs (s, T, t')) =
    (case try unprefix s of
       SOME s =>
       let
         val names = Name.make_context (map fst (Term.add_var_names t' []))
         val (s, _) = Name.variant s names
       in hol_open_form unprefix (subst_bound (Var ((s, 0), T), t')) end
     | NONE => t)
  | hol_open_form _ t = t

fun eta_expand _ t 0 = t
  | eta_expand Ts (Abs (s, T, t')) n =
    Abs (s, T, eta_expand (T :: Ts) t' (n - 1))
  | eta_expand Ts t n =
    fold_rev (fn T => fn t' => Abs ("x" ^ nat_subscript n, T, t'))
             (List.take (binder_types (fastype_of1 (Ts, t)), n))
             (list_comb (incr_boundvars n t, map Bound (n - 1 downto 0)))

fun cong_extensionalize_term ctxt t =
  if exists_Const (fn (s, _) => s = \<^const_name>\<open>Not\<close>) t then
    t |> Skip_Proof.make_thm (Proof_Context.theory_of ctxt)
      |> Meson.cong_extensionalize_thm ctxt
      |> Thm.prop_of
  else
    t

fun is_fun_equality (\<^const_name>\<open>HOL.eq\<close>,
                     Type (_, [Type (\<^type_name>\<open>fun\<close>, _), _])) = true
  | is_fun_equality _ = false

fun abs_extensionalize_term ctxt t =
  if exists_Const is_fun_equality t then
    t |> Thm.cterm_of ctxt |> Meson.abs_extensionalize_conv ctxt
      |> Thm.prop_of |> Logic.dest_equals |> snd
  else
    t

fun unextensionalize_def t =
  (case t of
    \<^Const_>\<open>Trueprop for \<^Const_>\<open>HOL.eq _ for lhs rhs\<close>\<close> =>
      (case strip_comb lhs of
        (c as Const (_, T), args) =>
          if forall is_Var args andalso not (has_duplicates (op =) args) then
            \<^Const>\<open>Trueprop for \<^Const>\<open>HOL.eq T for c \<open>fold_rev lambda args rhs\<close>\<close>\<close>
          else t
      | _ => t)
  | _ => t)

(* Converts an elim-rule into an equivalent theorem that does not have the
   predicate variable. Leaves other theorems unchanged. We simply instantiate
   the conclusion variable to "False". (Cf. "transform_elim_theorem" in
   "Meson_Clausify".) *)
fun transform_elim_prop t =
  case Logic.strip_imp_concl t of
    \<^Const_>\<open>Trueprop for \<open>Var (z, \<^typ>\<open>bool\<close>)\<close>\<close> => subst_Vars [(z, \<^Const>\<open>False\<close>)] t
  | Var (z, \<^Type>\<open>prop\<close>) => subst_Vars [(z, \<^prop>\<open>False\<close>)] t
  | _ => t

fun specialize_type thy (s, T) t =
  let
    fun subst_for (Const (s', T')) =
        if s = s' then
          SOME (Sign.typ_match thy (T', T) Vartab.empty)
          handle Type.TYPE_MATCH => NONE
        else
          NONE
      | subst_for (t1 $ t2) = (case subst_for t1 of SOME x => SOME x | NONE => subst_for t2)
      | subst_for (Abs (_, _, t')) = subst_for t'
      | subst_for _ = NONE
  in
    (case subst_for t of
      SOME subst => Envir.subst_term_types subst t
    | NONE => raise Type.TYPE_MATCH)
  end

fun strip_subgoal goal i ctxt =
  let
    val (t, (frees, params)) =
      Logic.goal_params (Thm.prop_of goal) i
      ||> (map dest_Free #> Variable.variant_frees ctxt [] #> `(map Free))
    val hyp_ts = t |> Logic.strip_assums_hyp |> map (curry subst_bounds frees)
    val concl_t = t |> Logic.strip_assums_concl |> curry subst_bounds frees
  in (rev params, hyp_ts, concl_t) end

fun extract_lambda_def dest_head (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ t $ u) =
    let val (head, args) = strip_comb t in
      (head |> dest_head |> fst,
       fold_rev (fn t as Var ((s, _), T) =>
                    (fn u => Abs (s, T, abstract_over (t, u)))
                  | _ => raise Fail "expected \"Var\"") args u)
    end
  | extract_lambda_def _ _ = raise Fail "malformed lifted lambda"

fun short_thm_name ctxt th =
  let
    val long = Thm.get_name_hint th
    val short = Long_Name.base_name long
  in
    if Thm.eq_thm_prop (th, singleton (Attrib.eval_thms ctxt) (Facts.named short, [])) then short
    else long
  end

  val map_prod = Ctr_Sugar_Util.map_prod

end;

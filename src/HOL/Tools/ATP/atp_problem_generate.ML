(*  Title:      HOL/Tools/ATP/atp_problem_generate.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Translation of HOL to FOL for Metis and Sledgehammer.
*)

signature ATP_PROBLEM_GENERATE =
sig
  type ('a, 'b) ho_term = ('a, 'b) ATP_Problem.ho_term
  type connective = ATP_Problem.connective
  type ('a, 'b, 'c, 'd) formula = ('a, 'b, 'c, 'd) ATP_Problem.formula
  type atp_format = ATP_Problem.atp_format
  type formula_role = ATP_Problem.formula_role
  type 'a problem = 'a ATP_Problem.problem

  datatype mode = Metis | Sledgehammer | Sledgehammer_Completish | Exporter

  datatype scope = Global | Local | Assum | Chained
  datatype status = General | Induction | Intro | Inductive | Elim | Simp | Def
  type stature = scope * status

  datatype strictness = Strict | Non_Strict
  datatype uniformity = Uniform | Non_Uniform
  datatype constr_optim = With_Constr_Optim | Without_Constr_Optim
  datatype type_level =
    All_Types |
    Nonmono_Types of strictness * uniformity |
    Undercover_Types |
    Const_Types of constr_optim |
    No_Types
  type type_enc

  val no_lamsN : string
  val hide_lamsN : string
  val liftingN : string
  val combsN : string
  val combs_and_liftingN : string
  val combs_or_liftingN : string
  val lam_liftingN : string
  val keep_lamsN : string
  val schematic_var_prefix : string
  val fixed_var_prefix : string
  val tvar_prefix : string
  val tfree_prefix : string
  val const_prefix : string
  val type_const_prefix : string
  val class_prefix : string
  val lam_lifted_prefix : string
  val lam_lifted_mono_prefix : string
  val lam_lifted_poly_prefix : string
  val skolem_const_prefix : string
  val old_skolem_const_prefix : string
  val new_skolem_const_prefix : string
  val combinator_prefix : string
  val class_decl_prefix : string
  val type_decl_prefix : string
  val sym_decl_prefix : string
  val class_memb_prefix : string
  val guards_sym_formula_prefix : string
  val tags_sym_formula_prefix : string
  val fact_prefix : string
  val conjecture_prefix : string
  val helper_prefix : string
  val subclass_prefix : string
  val tcon_clause_prefix : string
  val tfree_clause_prefix : string
  val lam_fact_prefix : string
  val typed_helper_suffix : string
  val untyped_helper_suffix : string
  val predicator_name : string
  val app_op_name : string
  val type_guard_name : string
  val type_tag_name : string
  val native_type_prefix : string
  val prefixed_predicator_name : string
  val prefixed_app_op_name : string
  val prefixed_type_tag_name : string
  val ascii_of : string -> string
  val unascii_of : string -> string
  val unprefix_and_unascii : string -> string -> string option
  val proxy_table : (string * (string * (thm * (string * string)))) list
  val proxify_const : string -> (string * string) option
  val invert_const : string -> string
  val unproxify_const : string -> string
  val new_skolem_var_name_from_const : string -> string
  val atp_irrelevant_consts : string list
  val atp_schematic_consts_of : term -> typ list Symtab.table
  val is_type_enc_higher_order : type_enc -> bool
  val is_type_enc_polymorphic : type_enc -> bool
  val level_of_type_enc : type_enc -> type_level
  val is_type_enc_sound : type_enc -> bool
  val type_enc_from_string : strictness -> string -> type_enc
  val adjust_type_enc : atp_format -> type_enc -> type_enc
  val mk_aconns :
    connective -> ('a, 'b, 'c, 'd) formula list -> ('a, 'b, 'c, 'd) formula
  val unmangled_const : string -> string * (string, 'b) ho_term list
  val unmangled_const_name : string -> string list
  val helper_table : ((string * bool) * (status * thm) list) list
  val trans_lams_from_string :
    Proof.context -> type_enc -> string -> term list -> term list * term list
  val factsN : string
  val prepare_atp_problem :
    Proof.context -> atp_format -> formula_role -> type_enc -> mode -> string
    -> bool -> bool -> bool -> term list -> term
    -> ((string * stature) * term) list
    -> string problem * string Symtab.table * (string * stature) list vector
       * (string * term) list * int Symtab.table
  val atp_problem_selection_weights : string problem -> (string * real) list
  val atp_problem_term_order_info : string problem -> (string * int) list
end;

structure ATP_Problem_Generate : ATP_PROBLEM_GENERATE =
struct

open ATP_Util
open ATP_Problem

datatype mode = Metis | Sledgehammer | Sledgehammer_Completish | Exporter

datatype scope = Global | Local | Assum | Chained
datatype status = General | Induction | Intro | Inductive | Elim | Simp | Def
type stature = scope * status

datatype order =
  First_Order |
  Higher_Order of thf_choice
datatype phantom_policy = Without_Phantom_Type_Vars | With_Phantom_Type_Vars
datatype polymorphism =
  Type_Class_Polymorphic |
  Raw_Polymorphic of phantom_policy |
  Raw_Monomorphic |
  Mangled_Monomorphic
datatype strictness = Strict | Non_Strict
datatype uniformity = Uniform | Non_Uniform
datatype constr_optim = With_Constr_Optim | Without_Constr_Optim
datatype type_level =
  All_Types |
  Nonmono_Types of strictness * uniformity |
  Undercover_Types |
  Const_Types of constr_optim |
  No_Types

datatype type_enc =
  Native of order * polymorphism * type_level |
  Guards of polymorphism * type_level |
  Tags of polymorphism * type_level

fun is_type_enc_native (Native _) = true
  | is_type_enc_native _ = false
fun is_type_enc_higher_order (Native (Higher_Order _, _, _)) = true
  | is_type_enc_higher_order _ = false

fun polymorphism_of_type_enc (Native (_, poly, _)) = poly
  | polymorphism_of_type_enc (Guards (poly, _)) = poly
  | polymorphism_of_type_enc (Tags (poly, _)) = poly

fun is_type_enc_polymorphic type_enc =
  case polymorphism_of_type_enc type_enc of
    Raw_Polymorphic _ => true
  | Type_Class_Polymorphic => true
  | _ => false

fun level_of_type_enc (Native (_, _, level)) = level
  | level_of_type_enc (Guards (_, level)) = level
  | level_of_type_enc (Tags (_, level)) = level

fun is_type_level_uniform (Nonmono_Types (_, Non_Uniform)) = false
  | is_type_level_uniform Undercover_Types = false
  | is_type_level_uniform _ = true

fun is_type_level_sound (Const_Types _) = false
  | is_type_level_sound No_Types = false
  | is_type_level_sound _ = true
val is_type_enc_sound = is_type_level_sound o level_of_type_enc

fun is_type_level_monotonicity_based (Nonmono_Types _) = true
  | is_type_level_monotonicity_based _ = false

val no_lamsN = "no_lams" (* used internally; undocumented *)
val hide_lamsN = "hide_lams"
val liftingN = "lifting"
val combsN = "combs"
val combs_and_liftingN = "combs_and_lifting"
val combs_or_liftingN = "combs_or_lifting"
val keep_lamsN = "keep_lams"
val lam_liftingN = "lam_lifting" (* legacy FIXME: remove *)

val bound_var_prefix = "B_"
val all_bound_var_prefix = "A_"
val exist_bound_var_prefix = "E_"
val schematic_var_prefix = "V_"
val fixed_var_prefix = "v_"
val tvar_prefix = "T_"
val tfree_prefix = "t_"
val const_prefix = "c_"
val type_const_prefix = "tc_"
val native_type_prefix = "n_"
val class_prefix = "cl_"

(* Freshness almost guaranteed! *)
val atp_prefix = "ATP" ^ Long_Name.separator
val atp_weak_prefix = "ATP:"

val lam_lifted_prefix = atp_weak_prefix ^ "Lam"
val lam_lifted_mono_prefix = lam_lifted_prefix ^ "m"
val lam_lifted_poly_prefix = lam_lifted_prefix ^ "p"

val skolem_const_prefix = atp_prefix ^ "Sko"
val old_skolem_const_prefix = skolem_const_prefix ^ "o"
val new_skolem_const_prefix = skolem_const_prefix ^ "n"

val combinator_prefix = "COMB"

val class_decl_prefix = "cl_"
val type_decl_prefix = "ty_"
val sym_decl_prefix = "sy_"
val class_memb_prefix = "clmb_"
val guards_sym_formula_prefix = "gsy_"
val tags_sym_formula_prefix = "tsy_"
val uncurried_alias_eq_prefix = "unc_"
val fact_prefix = "fact_"
val conjecture_prefix = "conj_"
val helper_prefix = "help_"
val subclass_prefix = "subcl_"
val tcon_clause_prefix = "tcon_"
val tfree_clause_prefix = "tfree_"

val lam_fact_prefix = "ATP.lambda_"
val typed_helper_suffix = "_T"
val untyped_helper_suffix = "_U"

val predicator_name = "pp"
val app_op_name = "aa"
val type_guard_name = "gg"
val type_tag_name = "tt"

val prefixed_predicator_name = const_prefix ^ predicator_name
val prefixed_app_op_name = const_prefix ^ app_op_name
val prefixed_type_tag_name = const_prefix ^ type_tag_name

(*Escaping of special characters.
  Alphanumeric characters are left unchanged.
  The character _ goes to __
  Characters in the range ASCII space to / go to _A to _P, respectively.
  Other characters go to _nnn where nnn is the decimal ASCII code.*)
val upper_a_minus_space = Char.ord #"A" - Char.ord #" "

fun stringN_of_int 0 _ = ""
  | stringN_of_int k n =
    stringN_of_int (k - 1) (n div 10) ^ string_of_int (n mod 10)

fun ascii_of_char c =
  if Char.isAlphaNum c then
    String.str c
  else if c = #"_" then
    "__"
  else if #" " <= c andalso c <= #"/" then
    "_" ^ String.str (Char.chr (Char.ord c + upper_a_minus_space))
  else
    (* fixed width, in case more digits follow *)
    "_" ^ stringN_of_int 3 (Char.ord c)

val ascii_of = String.translate ascii_of_char

(** Remove ASCII armoring from names in proof files **)

(* We don't raise error exceptions because this code can run inside a worker
   thread. Also, the errors are impossible. *)
val unascii_of =
  let
    fun un rcs [] = String.implode (rev rcs)
      | un rcs [#"_"] = un (#"_" :: rcs) [] (* ERROR *)
        (* Three types of _ escapes: __, _A to _P, _nnn *)
      | un rcs (#"_" :: #"_" :: cs) = un (#"_" :: rcs) cs
      | un rcs (#"_" :: c :: cs) =
        if #"A" <= c andalso c<= #"P" then
          (* translation of #" " to #"/" *)
          un (Char.chr (Char.ord c - upper_a_minus_space) :: rcs) cs
        else
          let val digits = List.take (c :: cs, 3) handle General.Subscript => [] in
            case Int.fromString (String.implode digits) of
              SOME n => un (Char.chr n :: rcs) (List.drop (cs, 2))
            | NONE => un (c :: #"_" :: rcs) cs (* ERROR *)
          end
      | un rcs (c :: cs) = un (c :: rcs) cs
  in un [] o String.explode end

(* If string s has the prefix s1, return the result of deleting it,
   un-ASCII'd. *)
fun unprefix_and_unascii s1 s =
  if String.isPrefix s1 s then
    SOME (unascii_of (String.extract (s, size s1, NONE)))
  else
    NONE

val proxy_table =
  [("c_False", (@{const_name False}, (@{thm fFalse_def},
       ("fFalse", @{const_name ATP.fFalse})))),
   ("c_True", (@{const_name True}, (@{thm fTrue_def},
       ("fTrue", @{const_name ATP.fTrue})))),
   ("c_Not", (@{const_name Not}, (@{thm fNot_def},
       ("fNot", @{const_name ATP.fNot})))),
   ("c_conj", (@{const_name conj}, (@{thm fconj_def},
       ("fconj", @{const_name ATP.fconj})))),
   ("c_disj", (@{const_name disj}, (@{thm fdisj_def},
       ("fdisj", @{const_name ATP.fdisj})))),
   ("c_implies", (@{const_name implies}, (@{thm fimplies_def},
       ("fimplies", @{const_name ATP.fimplies})))),
   ("equal", (@{const_name HOL.eq}, (@{thm fequal_def},
       ("fequal", @{const_name ATP.fequal})))),
   ("c_All", (@{const_name All}, (@{thm fAll_def},
       ("fAll", @{const_name ATP.fAll})))),
   ("c_Ex", (@{const_name Ex}, (@{thm fEx_def},
       ("fEx", @{const_name ATP.fEx}))))]

val proxify_const = AList.lookup (op =) proxy_table #> Option.map (snd o snd)

(* Readable names for the more common symbolic functions. Do not mess with the
   table unless you know what you are doing. *)
val const_trans_table =
  [(@{type_name Product_Type.prod}, "prod"),
   (@{type_name Sum_Type.sum}, "sum"),
   (@{const_name False}, "False"),
   (@{const_name True}, "True"),
   (@{const_name Not}, "Not"),
   (@{const_name conj}, "conj"),
   (@{const_name disj}, "disj"),
   (@{const_name implies}, "implies"),
   (@{const_name HOL.eq}, "equal"),
   (@{const_name All}, "All"),
   (@{const_name Ex}, "Ex"),
   (@{const_name If}, "If"),
   (@{const_name Set.member}, "member"),
   (@{const_name Meson.COMBI}, combinator_prefix ^ "I"),
   (@{const_name Meson.COMBK}, combinator_prefix ^ "K"),
   (@{const_name Meson.COMBB}, combinator_prefix ^ "B"),
   (@{const_name Meson.COMBC}, combinator_prefix ^ "C"),
   (@{const_name Meson.COMBS}, combinator_prefix ^ "S")]
  |> Symtab.make
  |> fold (Symtab.update o swap o snd o snd o snd) proxy_table

(* Invert the table of translations between Isabelle and ATPs. *)
val const_trans_table_inv =
  const_trans_table |> Symtab.dest |> map swap |> Symtab.make
val const_trans_table_unprox =
  Symtab.empty
  |> fold (fn (_, (isa, (_, (_, atp)))) => Symtab.update (atp, isa)) proxy_table

val invert_const = perhaps (Symtab.lookup const_trans_table_inv)
val unproxify_const = perhaps (Symtab.lookup const_trans_table_unprox)

fun lookup_const c =
  case Symtab.lookup const_trans_table c of
    SOME c' => c'
  | NONE => ascii_of c

fun ascii_of_indexname (v, 0) = ascii_of v
  | ascii_of_indexname (v, i) = ascii_of v ^ "_" ^ string_of_int i

fun make_bound_var x = bound_var_prefix ^ ascii_of x
fun make_all_bound_var x = all_bound_var_prefix ^ ascii_of x
fun make_exist_bound_var x = exist_bound_var_prefix ^ ascii_of x
fun make_schematic_var v = schematic_var_prefix ^ ascii_of_indexname v
fun make_fixed_var x = fixed_var_prefix ^ ascii_of x

fun make_tvar (s, i) = tvar_prefix ^ ascii_of_indexname (unprefix "'" s, i)
fun make_tfree s = tfree_prefix ^ ascii_of (unprefix "'" s)
fun tvar_name ((x as (s, _)), _) = (make_tvar x, s)

(* "HOL.eq" and choice are mapped to the ATP's equivalents *)
local
  val choice_const = (fst o dest_Const o HOLogic.choice_const) Term.dummyT
  fun default c = const_prefix ^ lookup_const c
in
  fun make_fixed_const _ @{const_name HOL.eq} = tptp_old_equal
    | make_fixed_const (SOME (Native (Higher_Order THF_With_Choice, _, _))) c =
      if c = choice_const then tptp_choice else default c
    | make_fixed_const _ c = default c
end

fun make_fixed_type_const c = type_const_prefix ^ lookup_const c

fun make_class clas = class_prefix ^ ascii_of clas

fun new_skolem_var_name_from_const s =
  let val ss = s |> space_explode Long_Name.separator in
    nth ss (length ss - 2)
  end

(* These are either simplified away by "Meson.presimplify" (most of the time) or
   handled specially via "fFalse", "fTrue", ..., "fequal". *)
val atp_irrelevant_consts =
  [@{const_name False}, @{const_name True}, @{const_name Not},
   @{const_name conj}, @{const_name disj}, @{const_name implies},
   @{const_name HOL.eq}, @{const_name If}, @{const_name Let}]

val atp_monomorph_bad_consts =
  atp_irrelevant_consts @
  (* These are ignored anyway by the relevance filter (unless they appear in
     higher-order places) but not by the monomorphizer. *)
  [@{const_name all}, @{const_name "==>"}, @{const_name "=="},
   @{const_name Trueprop}, @{const_name All}, @{const_name Ex},
   @{const_name Ex1}, @{const_name Ball}, @{const_name Bex}]

fun add_schematic_const (x as (_, T)) =
  Monomorph.typ_has_tvars T ? Symtab.insert_list (op =) x
val add_schematic_consts_of =
  Term.fold_aterms (fn Const (x as (s, _)) =>
                       not (member (op =) atp_monomorph_bad_consts s)
                       ? add_schematic_const x
                      | _ => I)
fun atp_schematic_consts_of t = add_schematic_consts_of t Symtab.empty

val tvar_a_str = "'a"
val tvar_a_z = ((tvar_a_str, 0), HOLogic.typeS)
val tvar_a = TVar tvar_a_z
val tvar_a_name = tvar_name tvar_a_z
val itself_name = `make_fixed_type_const @{type_name itself}
val TYPE_name = `(make_fixed_const NONE) @{const_name TYPE}
val tvar_a_atype = AType (tvar_a_name, [])
val a_itself_atype = AType (itself_name, [tvar_a_atype])

(** Definitions and functions for FOL clauses and formulas for TPTP **)

(** Type class membership **)

(* In our data structures, [] exceptionally refers to the top class, not to
   the empty class. *)

val class_of_types = the_single @{sort type}

fun normalize_classes cls = if member (op =) cls class_of_types then [] else cls

(* Arity of type constructor "s :: (arg1, ..., argN) res" *)
fun make_axiom_tcon_clause (s, name, (cl, args)) =
  let
    val args = args |> map normalize_classes
    val tvars =
      1 upto length args |> map (fn j => TVar ((tvar_a_str, j), @{sort type}))
  in (name, args ~~ tvars, (cl, Type (s, tvars))) end

(* Generate all pairs (tycon, class, sorts) such that tycon belongs to class in
   theory thy provided its arguments have the corresponding sorts. *)
fun class_pairs thy tycons cls =
  let
    val alg = Sign.classes_of thy
    fun domain_sorts tycon = Sorts.mg_domain alg tycon o single
    fun add_class tycon cl =
      cons (cl, domain_sorts tycon cl)
      handle Sorts.CLASS_ERROR _ => I
    fun try_classes tycon = (tycon, fold (add_class tycon) cls [])
  in map try_classes tycons end

(* Proving one (tycon, class) membership may require proving others, so
   iterate. *)
fun all_class_pairs _ _ [] = ([], [])
  | all_class_pairs thy tycons cls =
    let
      fun maybe_insert_class s =
        (s <> class_of_types andalso not (member (op =) cls s))
        ? insert (op =) s
      val pairs = class_pairs thy tycons cls
      val new_cls =
        [] |> fold (fold (fold (fold maybe_insert_class) o snd) o snd) pairs
      val (cls', pairs') = all_class_pairs thy tycons new_cls
    in (cls' @ cls, union (op =) pairs' pairs) end

fun tcon_clause _ _ (_, []) = []
  | tcon_clause seen n (tcons, (ar as (cl, _)) :: ars) =
    if cl = class_of_types then
      tcon_clause seen n (tcons, ars)
    else if member (op =) seen cl then
      (* multiple clauses for the same (tycon, cl) pair *)
      make_axiom_tcon_clause (tcons,
          lookup_const tcons ^ "___" ^ ascii_of cl ^ "_" ^ string_of_int n,
          ar) ::
      tcon_clause seen (n + 1) (tcons, ars)
    else
      make_axiom_tcon_clause (tcons, lookup_const tcons ^ "___" ^ ascii_of cl,
                              ar) ::
      tcon_clause (cl :: seen) n (tcons, ars)

fun make_tcon_clauses thy tycons =
  all_class_pairs thy tycons ##> maps (tcon_clause [] 1)


(** Isabelle class relations **)

(* Generate a list ("sub", "supers") such that "sub" is a proper subclass of all
   "supers". *)
fun make_subclass_pairs thy subs supers =
  let
    val class_less = curry (Sorts.class_less (Sign.classes_of thy))
    fun supers_of sub = (sub, filter (class_less sub) supers)
  in map supers_of subs |> filter_out (null o snd) end

(* intermediate terms *)
datatype iterm =
  IConst of (string * string) * typ * typ list |
  IVar of (string * string) * typ |
  IApp of iterm * iterm |
  IAbs of ((string * string) * typ) * iterm

fun ityp_of (IConst (_, T, _)) = T
  | ityp_of (IVar (_, T)) = T
  | ityp_of (IApp (t1, _)) = snd (dest_funT (ityp_of t1))
  | ityp_of (IAbs ((_, T), tm)) = T --> ityp_of tm

(*gets the head of a combinator application, along with the list of arguments*)
fun strip_iterm_comb u =
  let
    fun stripc (IApp (t, u), ts) = stripc (t, u :: ts)
      | stripc x = x
  in stripc (u, []) end

fun atomic_types_of T = fold_atyps (insert (op =)) T []

fun new_skolem_const_name s num_T_args =
  [new_skolem_const_prefix, s, string_of_int num_T_args]
  |> Long_Name.implode

val alpha_to_beta = Logic.varifyT_global @{typ "'a => 'b"}
val alpha_to_beta_to_alpha_to_beta = alpha_to_beta --> alpha_to_beta

fun robust_const_type thy s =
  if s = app_op_name then
    alpha_to_beta_to_alpha_to_beta
  else if String.isPrefix lam_lifted_prefix s then
    alpha_to_beta
  else
    (* Old Skolems throw a "TYPE" exception here, which will be caught. *)
    s |> Sign.the_const_type thy

val robust_const_ary =
  let
    fun ary (Type (@{type_name fun}, [_, T])) = 1 + ary T
      | ary _ = 0
  in ary oo robust_const_type end

(* This function only makes sense if "T" is as general as possible. *)
fun robust_const_typargs thy (s, T) =
  if s = app_op_name then
    let val (T1, T2) = T |> domain_type |> dest_funT in [T1, T2] end
  else if String.isPrefix old_skolem_const_prefix s then
    [] |> Term.add_tvarsT T |> rev |> map TVar
  else if String.isPrefix lam_lifted_prefix s then
    if String.isPrefix lam_lifted_poly_prefix s then
      let val (T1, T2) = T |> dest_funT in [T1, T2] end
    else
      []
  else
    (s, T) |> Sign.const_typargs thy

(* Converts an Isabelle/HOL term (with combinators) into an intermediate term.
   Also accumulates sort infomation. *)
fun iterm_from_term thy type_enc bs (P $ Q) =
    let
      val (P', P_atomics_Ts) = iterm_from_term thy type_enc bs P
      val (Q', Q_atomics_Ts) = iterm_from_term thy type_enc bs Q
    in (IApp (P', Q'), union (op =) P_atomics_Ts Q_atomics_Ts) end
  | iterm_from_term thy type_enc _ (Const (c, T)) =
    (IConst (`(make_fixed_const (SOME type_enc)) c, T,
             robust_const_typargs thy (c, T)),
     atomic_types_of T)
  | iterm_from_term _ _ _ (Free (s, T)) =
    (IConst (`make_fixed_var s, T, []), atomic_types_of T)
  | iterm_from_term _ type_enc _ (Var (v as (s, _), T)) =
    (if String.isPrefix Meson_Clausify.new_skolem_var_prefix s then
       let
         val Ts = T |> strip_type |> swap |> op ::
         val s' = new_skolem_const_name s (length Ts)
       in IConst (`(make_fixed_const (SOME type_enc)) s', T, Ts) end
     else
       IVar ((make_schematic_var v, s), T), atomic_types_of T)
  | iterm_from_term _ _ bs (Bound j) =
    nth bs j |> (fn (_, (name, T)) => (IConst (name, T, []), atomic_types_of T))
  | iterm_from_term thy type_enc bs (Abs (s, T, t)) =
    let
      fun vary s = s |> AList.defined (op =) bs s ? vary o Symbol.bump_string
      val s = vary s
      val name = `make_bound_var s
      val (tm, atomic_Ts) =
        iterm_from_term thy type_enc ((s, (name, T)) :: bs) t
    in (IAbs ((name, T), tm), union (op =) atomic_Ts (atomic_types_of T)) end

(* "_query" and "_at" are for the ASCII-challenged Metis and Mirabelle. *)
val queries = ["?", "_query"]
val ats = ["@", "_at"]

fun try_unsuffixes ss s =
  fold (fn s' => fn NONE => try (unsuffix s') s | some => some) ss NONE

fun type_enc_from_string strictness s =
  (case try (unprefix "tc_") s of
     SOME s => (SOME Type_Class_Polymorphic, s)
   | NONE =>
       case try (unprefix "poly_") s of
         (* It's still unclear whether all TFF1 implementations will support
            type signatures such as "!>[A : $tType] : $o", with phantom type
            variables. *)
         SOME s => (SOME (Raw_Polymorphic With_Phantom_Type_Vars), s)
       | NONE =>
         case try (unprefix "raw_mono_") s of
           SOME s => (SOME Raw_Monomorphic, s)
         | NONE =>
           case try (unprefix "mono_") s of
             SOME s => (SOME Mangled_Monomorphic, s)
           | NONE => (NONE, s))
  ||> (fn s =>
          case try_unsuffixes queries s of
          SOME s =>
          (case try_unsuffixes queries s of
             SOME s => (Nonmono_Types (strictness, Non_Uniform), s)
           | NONE => (Nonmono_Types (strictness, Uniform), s))
         | NONE =>
           (case try_unsuffixes ats s of
              SOME s => (Undercover_Types, s)
            | NONE => (All_Types, s)))
  |> (fn (poly, (level, core)) =>
         case (core, (poly, level)) of
           ("native", (SOME poly, _)) =>
           (case (poly, level) of
              (Mangled_Monomorphic, _) =>
              if is_type_level_uniform level then
                Native (First_Order, Mangled_Monomorphic, level)
              else
                raise Same.SAME
            | (Raw_Monomorphic, _) => raise Same.SAME
            | (poly, All_Types) => Native (First_Order, poly, All_Types))
         | ("native_higher", (SOME poly, _)) =>
           (case (poly, level) of
              (_, Nonmono_Types _) => raise Same.SAME
            | (_, Undercover_Types) => raise Same.SAME
            | (Mangled_Monomorphic, _) =>
              if is_type_level_uniform level then
                Native (Higher_Order THF_With_Choice, Mangled_Monomorphic,
                        level)
              else
                raise Same.SAME
            | (poly as Raw_Polymorphic _, All_Types) =>
              Native (Higher_Order THF_With_Choice, poly, All_Types)
            | _ => raise Same.SAME)
         | ("guards", (SOME poly, _)) =>
           if (poly = Mangled_Monomorphic andalso
               level = Undercover_Types) orelse
              poly = Type_Class_Polymorphic then
             raise Same.SAME
           else
             Guards (poly, level)
         | ("tags", (SOME poly, _)) =>
           if (poly = Mangled_Monomorphic andalso
               level = Undercover_Types) orelse
              poly = Type_Class_Polymorphic then
             raise Same.SAME
           else
             Tags (poly, level)
         | ("args", (SOME poly, All_Types (* naja *))) =>
           if poly = Type_Class_Polymorphic then raise Same.SAME
           else Guards (poly, Const_Types Without_Constr_Optim)
         | ("args", (SOME poly, Nonmono_Types (_, Uniform) (* naja *))) =>
           if poly = Mangled_Monomorphic orelse
              poly = Type_Class_Polymorphic then
             raise Same.SAME
           else
             Guards (poly, Const_Types With_Constr_Optim)
         | ("erased", (NONE, All_Types (* naja *))) =>
           Guards (Raw_Polymorphic With_Phantom_Type_Vars, No_Types)
         | _ => raise Same.SAME)
  handle Same.SAME => error ("Unknown type encoding: " ^ quote s ^ ".")

fun adjust_order THF_Without_Choice (Higher_Order _) =
    Higher_Order THF_Without_Choice
  | adjust_order _ type_enc = type_enc

fun no_type_classes Type_Class_Polymorphic =
    Raw_Polymorphic With_Phantom_Type_Vars
  | no_type_classes poly = poly

fun adjust_type_enc (THF (Polymorphic, _, choice, _))
                    (Native (order, poly, level)) =
    Native (adjust_order choice order, no_type_classes poly, level)
  | adjust_type_enc (THF (Monomorphic, _, choice, _))
                         (Native (order, _, level)) =
    Native (adjust_order choice order, Mangled_Monomorphic, level)
  | adjust_type_enc (TFF (Monomorphic, _)) (Native (_, _, level)) =
    Native (First_Order, Mangled_Monomorphic, level)
  | adjust_type_enc (DFG Polymorphic) (Native (_, poly, level)) =
    Native (First_Order, poly, level)
  | adjust_type_enc (DFG Monomorphic) (Native (_, _, level)) =
    Native (First_Order, Mangled_Monomorphic, level)
  | adjust_type_enc (TFF _) (Native (_, poly, level)) =
    Native (First_Order, no_type_classes poly, level)
  | adjust_type_enc format (Native (_, poly, level)) =
    adjust_type_enc format (Guards (no_type_classes poly, level))
  | adjust_type_enc CNF_UEQ (type_enc as Guards stuff) =
    (if is_type_enc_sound type_enc then Tags else Guards) stuff
  | adjust_type_enc _ type_enc = type_enc

fun is_fol_term t =
  case t of
    @{const Not} $ t1 => is_fol_term t1
  | Const (@{const_name All}, _) $ Abs (_, _, t') => is_fol_term t'
  | Const (@{const_name All}, _) $ t1 => is_fol_term t1
  | Const (@{const_name Ex}, _) $ Abs (_, _, t') => is_fol_term t'
  | Const (@{const_name Ex}, _) $ t1 => is_fol_term t1
  | @{const HOL.conj} $ t1 $ t2 => is_fol_term t1 andalso is_fol_term t2
  | @{const HOL.disj} $ t1 $ t2 => is_fol_term t1 andalso is_fol_term t2
  | @{const HOL.implies} $ t1 $ t2 => is_fol_term t1 andalso is_fol_term t2
  | Const (@{const_name HOL.eq}, Type (_, [@{typ bool}, _])) $ t1 $ t2 =>
    is_fol_term t1 andalso is_fol_term t2
  | _ => not (exists_subterm (fn Abs _ => true | _ => false) t)

fun simple_translate_lambdas do_lambdas ctxt t =
  if is_fol_term t then
    t
  else
    let
      fun trans Ts t =
        case t of
          @{const Not} $ t1 => @{const Not} $ trans Ts t1
        | (t0 as Const (@{const_name All}, _)) $ Abs (s, T, t') =>
          t0 $ Abs (s, T, trans (T :: Ts) t')
        | (t0 as Const (@{const_name All}, _)) $ t1 =>
          trans Ts (t0 $ eta_expand Ts t1 1)
        | (t0 as Const (@{const_name Ex}, _)) $ Abs (s, T, t') =>
          t0 $ Abs (s, T, trans (T :: Ts) t')
        | (t0 as Const (@{const_name Ex}, _)) $ t1 =>
          trans Ts (t0 $ eta_expand Ts t1 1)
        | (t0 as @{const HOL.conj}) $ t1 $ t2 =>
          t0 $ trans Ts t1 $ trans Ts t2
        | (t0 as @{const HOL.disj}) $ t1 $ t2 =>
          t0 $ trans Ts t1 $ trans Ts t2
        | (t0 as @{const HOL.implies}) $ t1 $ t2 =>
          t0 $ trans Ts t1 $ trans Ts t2
        | (t0 as Const (@{const_name HOL.eq}, Type (_, [@{typ bool}, _])))
            $ t1 $ t2 =>
          t0 $ trans Ts t1 $ trans Ts t2
        | _ =>
          if not (exists_subterm (fn Abs _ => true | _ => false) t) then t
          else t |> Envir.eta_contract |> do_lambdas ctxt Ts
      val (t, ctxt') = Variable.import_terms true [t] ctxt |>> the_single
    in t |> trans [] |> singleton (Variable.export_terms ctxt' ctxt) end

fun do_cheaply_conceal_lambdas Ts (t1 $ t2) =
    do_cheaply_conceal_lambdas Ts t1
    $ do_cheaply_conceal_lambdas Ts t2
  | do_cheaply_conceal_lambdas Ts (Abs (_, T, t)) =
    Const (lam_lifted_poly_prefix ^ serial_string (),
           T --> fastype_of1 (T :: Ts, t))
  | do_cheaply_conceal_lambdas _ t = t

fun concealed_bound_name j = atp_weak_prefix ^ string_of_int j
fun conceal_bounds Ts t =
  subst_bounds (map (Free o apfst concealed_bound_name)
                    (0 upto length Ts - 1 ~~ Ts), t)
fun reveal_bounds Ts =
  subst_atomic (map (fn (j, T) => (Free (concealed_bound_name j, T), Bound j))
                    (0 upto length Ts - 1 ~~ Ts))

fun do_introduce_combinators ctxt Ts t =
  let val thy = Proof_Context.theory_of ctxt in
    t |> conceal_bounds Ts
      |> cterm_of thy
      |> Meson_Clausify.introduce_combinators_in_cterm
      |> prop_of |> Logic.dest_equals |> snd
      |> reveal_bounds Ts
  end
  (* A type variable of sort "{}" will make abstraction fail. *)
  handle THM _ => t |> do_cheaply_conceal_lambdas Ts
val introduce_combinators = simple_translate_lambdas do_introduce_combinators

fun constify_lifted (t $ u) = constify_lifted t $ constify_lifted u
  | constify_lifted (Abs (s, T, t)) = Abs (s, T, constify_lifted t)
  | constify_lifted (Free (x as (s, _))) =
    (if String.isPrefix lam_lifted_prefix s then Const else Free) x
  | constify_lifted t = t

fun lift_lams_part_1 ctxt type_enc =
  map close_form #> rpair ctxt
  #-> Lambda_Lifting.lift_lambdas
          (SOME ((if is_type_enc_polymorphic type_enc then
                    lam_lifted_poly_prefix
                  else
                    lam_lifted_mono_prefix) ^ "_a"))
          Lambda_Lifting.is_quantifier
  #> fst

fun lift_lams_part_2 ctxt (facts, lifted) =
  (facts, lifted)
  (* Lambda-lifting sometimes leaves some lambdas around; we need some way to get rid
     of them *)
  |> pairself (map (introduce_combinators ctxt))
  |> pairself (map constify_lifted)
  (* Requires bound variables not to clash with any schematic variables (as
     should be the case right after lambda-lifting). *)
  |>> map (open_form (unprefix close_form_prefix))
  ||> map (open_form I)

fun lift_lams ctxt = lift_lams_part_2 ctxt oo lift_lams_part_1 ctxt

fun intentionalize_def (Const (@{const_name All}, _) $ Abs (_, _, t)) =
    intentionalize_def t
  | intentionalize_def (Const (@{const_name HOL.eq}, _) $ t $ u) =
    let
      fun lam T t = Abs (Name.uu, T, t)
      val (head, args) = strip_comb t ||> rev
      val head_T = fastype_of head
      val n = length args
      val arg_Ts = head_T |> binder_types |> take n |> rev
      val u = u |> subst_atomic (args ~~ map Bound (0 upto n - 1))
    in HOLogic.eq_const head_T $ head $ fold lam arg_Ts u end
  | intentionalize_def t = t

type ifact =
  {name : string,
   stature : stature,
   role : formula_role,
   iformula : (string * string, typ, iterm, string * string) formula,
   atomic_types : typ list}

fun update_iformula f ({name, stature, role, iformula, atomic_types} : ifact) =
  {name = name, stature = stature, role = role, iformula = f iformula,
   atomic_types = atomic_types} : ifact

fun ifact_lift f ({iformula, ...} : ifact) = f iformula

fun insert_type thy get_T x xs =
  let val T = get_T x in
    if exists (type_instance thy T o get_T) xs then xs
    else x :: filter_out (type_generalization thy T o get_T) xs
  end

(* The Booleans indicate whether all type arguments should be kept. *)
datatype type_arg_policy =
  Mangled_Type_Args |
  All_Type_Args |
  Not_Input_Type_Args |
  Constr_Input_Type_Args |
  No_Type_Args

fun type_arg_policy constrs type_enc s =
  let val poly = polymorphism_of_type_enc type_enc in
    if s = type_tag_name then
      if poly = Mangled_Monomorphic then Mangled_Type_Args else All_Type_Args
    else case type_enc of
      Native (_, Raw_Polymorphic _, _) => All_Type_Args
    | Native (_, Type_Class_Polymorphic, _) => All_Type_Args
    | Tags (_, All_Types) => No_Type_Args
    | _ =>
      let val level = level_of_type_enc type_enc in
        if level = No_Types orelse s = @{const_name HOL.eq} orelse
           (case level of Const_Types _ => s = app_op_name | _ => false) then
          No_Type_Args
        else if poly = Mangled_Monomorphic then
          Mangled_Type_Args
        else if level = All_Types orelse level = Undercover_Types then
          Not_Input_Type_Args
        else if member (op =) constrs s andalso
                level <> Const_Types Without_Constr_Optim then
          Constr_Input_Type_Args
        else
          All_Type_Args
      end
  end

val fused_infinite_type_name = "ATP.fused_inf" (* shouldn't clash *)
val fused_infinite_type = Type (fused_infinite_type_name, [])

fun raw_ho_type_from_typ type_enc =
  let
    fun term (Type (s, Ts)) =
      AType (case (is_type_enc_higher_order type_enc, s) of
               (true, @{type_name bool}) => `I tptp_bool_type
             | (true, @{type_name fun}) => `I tptp_fun_type
             | _ => if s = fused_infinite_type_name andalso
                       is_type_enc_native type_enc then
                      `I tptp_individual_type
                    else
                      `make_fixed_type_const s,
             map term Ts)
    | term (TFree (s, _)) = AType (`make_tfree s, [])
    | term (TVar z) = AType (tvar_name z, [])
  in term end

fun ho_term_from_ho_type (AType (name, tys)) = ATerm ((name, []), map ho_term_from_ho_type tys)
  | ho_term_from_ho_type _ = raise Fail "unexpected type"

fun ho_type_for_type_arg type_enc T =
  if T = dummyT then NONE else SOME (raw_ho_type_from_typ type_enc T)

(* This shouldn't clash with anything else. *)
val uncurried_alias_sep = "\000"
val mangled_type_sep = "\001"

val ascii_of_uncurried_alias_sep = ascii_of uncurried_alias_sep

fun generic_mangled_type_name f (AType (name, [])) = f name
  | generic_mangled_type_name f (AType (name, tys)) =
    f name ^ "(" ^ space_implode "," (map (generic_mangled_type_name f) tys)
    ^ ")"
  | generic_mangled_type_name _ _ = raise Fail "unexpected type"

fun mangled_type type_enc =
  generic_mangled_type_name fst o raw_ho_type_from_typ type_enc

fun make_native_type s =
  if s = tptp_bool_type orelse s = tptp_fun_type orelse
     s = tptp_individual_type then
    s
  else
    native_type_prefix ^ ascii_of s

fun native_ho_type_from_raw_ho_type type_enc pred_sym ary =
  let
    fun to_mangled_atype ty =
      AType ((make_native_type (generic_mangled_type_name fst ty),
              generic_mangled_type_name snd ty), [])
    fun to_poly_atype (AType (name, tys)) =
        AType (name, map to_poly_atype tys)
      | to_poly_atype _ = raise Fail "unexpected type"
    val to_atype =
      if is_type_enc_polymorphic type_enc then to_poly_atype
      else to_mangled_atype
    fun to_afun f1 f2 tys = AFun (f1 (hd tys), f2 (nth tys 1))
    fun to_fo 0 ty = if pred_sym then bool_atype else to_atype ty
      | to_fo ary (AType (_, tys)) = to_afun to_atype (to_fo (ary - 1)) tys
      | to_fo _ _ = raise Fail "unexpected type"
    fun to_ho (ty as AType ((s, _), tys)) =
        if s = tptp_fun_type then to_afun to_ho to_ho tys else to_atype ty
      | to_ho _ = raise Fail "unexpected type"
  in if is_type_enc_higher_order type_enc then to_ho else to_fo ary end

fun native_ho_type_from_typ type_enc pred_sym ary =
  native_ho_type_from_raw_ho_type type_enc pred_sym ary
  o raw_ho_type_from_typ type_enc

(* Make atoms for sorted type variables. *)
fun generic_add_sorts_on_type _ [] = I
  | generic_add_sorts_on_type T (s :: ss) =
    generic_add_sorts_on_type T ss
    #> (if s = the_single @{sort type} then I else insert (op =) (s, T))
fun add_sorts_on_tfree (T as TFree (_, S)) = generic_add_sorts_on_type T S
  | add_sorts_on_tfree _ = I
fun add_sorts_on_tvar (T as TVar (_, S)) = generic_add_sorts_on_type T S
  | add_sorts_on_tvar _ = I

fun process_type_args type_enc T_args =
  if is_type_enc_native type_enc then
    (map (native_ho_type_from_typ type_enc false 0) T_args, [])
  else
    ([], map_filter (Option.map ho_term_from_ho_type
                     o ho_type_for_type_arg type_enc) T_args)

fun class_atom type_enc (cl, T) =
  let
    val cl = `make_class cl
    val (ty_args, tm_args) = process_type_args type_enc [T]
    val tm_args =
      tm_args @
      (case type_enc of
         Native (First_Order, Raw_Polymorphic Without_Phantom_Type_Vars, _) =>
         [ATerm ((TYPE_name, ty_args), [])]
       | _ => [])
  in AAtom (ATerm ((cl, ty_args), tm_args)) end

fun class_atoms type_enc (cls, T) =
  map (fn cl => class_atom type_enc (cl, T)) cls

fun class_membs_for_types type_enc add_sorts_on_typ Ts =
  [] |> (polymorphism_of_type_enc type_enc <> Type_Class_Polymorphic andalso
         level_of_type_enc type_enc <> No_Types)
        ? fold add_sorts_on_typ Ts

fun mk_aconns c = split_last #> uncurry (fold_rev (mk_aconn c))

fun mk_ahorn [] phi = phi
  | mk_ahorn phis psi = AConn (AImplies, [mk_aconns AAnd phis, psi])

fun mk_aquant _ [] phi = phi
  | mk_aquant q xs (phi as AQuant (q', xs', phi')) =
    if q = q' then AQuant (q, xs @ xs', phi') else AQuant (q, xs, phi)
  | mk_aquant q xs phi = AQuant (q, xs, phi)

fun mk_atyquant _ [] phi = phi
  | mk_atyquant q xs (phi as ATyQuant (q', xs', phi')) =
    if q = q' then ATyQuant (q, xs @ xs', phi') else ATyQuant (q, xs, phi)
  | mk_atyquant q xs phi = ATyQuant (q, xs, phi)

fun close_universally add_term_vars phi =
  let
    fun add_formula_vars bounds (ATyQuant (_, _, phi)) =
        add_formula_vars bounds phi
      | add_formula_vars bounds (AQuant (_, xs, phi)) =
        add_formula_vars (map fst xs @ bounds) phi
      | add_formula_vars bounds (AConn (_, phis)) =
        fold (add_formula_vars bounds) phis
      | add_formula_vars bounds (AAtom tm) = add_term_vars bounds tm
  in mk_aquant AForall (add_formula_vars [] phi []) phi end

fun add_term_vars bounds (ATerm ((name as (s, _), _), tms)) =
    (if is_tptp_variable s andalso
        not (String.isPrefix tvar_prefix s) andalso
        not (member (op =) bounds name) then
       insert (op =) (name, NONE)
     else
       I)
    #> fold (add_term_vars bounds) tms
  | add_term_vars bounds (AAbs (((name, _), tm), args)) =
    add_term_vars (name :: bounds) tm #> fold (add_term_vars bounds) args
fun close_formula_universally phi = close_universally add_term_vars phi

fun add_iterm_vars bounds (IApp (tm1, tm2)) =
    fold (add_iterm_vars bounds) [tm1, tm2]
  | add_iterm_vars _ (IConst _) = I
  | add_iterm_vars bounds (IVar (name, T)) =
    not (member (op =) bounds name) ? insert (op =) (name, SOME T)
  | add_iterm_vars bounds (IAbs (_, tm)) = add_iterm_vars bounds tm

fun aliased_uncurried ary (s, s') =
  (s ^ ascii_of_uncurried_alias_sep ^ string_of_int ary, s' ^ string_of_int ary)
fun unaliased_uncurried (s, s') =
  case space_explode uncurried_alias_sep s of
    [_] => (s, s')
  | [s1, s2] => (s1, unsuffix s2 s')
  | _ => raise Fail "ill-formed explicit application alias"

fun raw_mangled_const_name type_name ty_args (s, s') =
  let
    fun type_suffix f g =
      fold_rev (curry (op ^) o g o prefix mangled_type_sep o type_name f)
               ty_args ""
  in (s ^ type_suffix fst ascii_of, s' ^ type_suffix snd I) end
fun mangled_const_name type_enc =
  map_filter (ho_type_for_type_arg type_enc)
  #> raw_mangled_const_name generic_mangled_type_name

val parse_mangled_ident =
  Scan.many1 (not o member (op =) ["(", ")", ","]) >> implode

fun parse_mangled_type x =
  (parse_mangled_ident
   -- Scan.optional ($$ "(" |-- Scan.optional parse_mangled_types [] --| $$ ")")
                    [] >> (ATerm o apfst (rpair []))) x
and parse_mangled_types x =
  (parse_mangled_type ::: Scan.repeat ($$ "," |-- parse_mangled_type)) x

fun unmangled_type s =
  s |> suffix ")" |> raw_explode
    |> Scan.finite Symbol.stopper
           (Scan.error (!! (fn _ => raise Fail ("unrecognized mangled type " ^
                                                quote s)) parse_mangled_type))
    |> fst

fun unmangled_const_name s =
  (s, s) |> unaliased_uncurried |> fst |> space_explode mangled_type_sep
fun unmangled_const s =
  let val ss = unmangled_const_name s in
    (hd ss, map unmangled_type (tl ss))
  end

fun introduce_proxies_in_iterm type_enc =
  let
    fun tweak_ho_quant ho_quant T [IAbs _] = IConst (`I ho_quant, T, [])
      | tweak_ho_quant ho_quant (T as Type (_, [p_T as Type (_, [x_T, _]), _]))
                       _ =
        (* Eta-expand "!!" and "??", to work around LEO-II 1.2.8 parser
           limitation. This works in conjuction with special code in
           "ATP_Problem" that uses the syntactic sugar "!" and "?" whenever
           possible. *)
        IAbs ((`I "P", p_T),
              IApp (IConst (`I ho_quant, T, []),
                    IAbs ((`I "X", x_T),
                          IApp (IConst (`I "P", p_T, []),
                                IConst (`I "X", x_T, [])))))
      | tweak_ho_quant _ _ _ = raise Fail "unexpected type for quantifier"
    fun intro top_level args (IApp (tm1, tm2)) =
        IApp (intro top_level (tm2 :: args) tm1, intro false [] tm2)
      | intro top_level args (IConst (name as (s, _), T, T_args)) =
        (case proxify_const s of
           SOME proxy_base =>
           if top_level orelse is_type_enc_higher_order type_enc then
             case (top_level, s) of
               (_, "c_False") => IConst (`I tptp_false, T, [])
             | (_, "c_True") => IConst (`I tptp_true, T, [])
             | (false, "c_Not") => IConst (`I tptp_not, T, [])
             | (false, "c_conj") => IConst (`I tptp_and, T, [])
             | (false, "c_disj") => IConst (`I tptp_or, T, [])
             | (false, "c_implies") => IConst (`I tptp_implies, T, [])
             | (false, "c_All") => tweak_ho_quant tptp_ho_forall T args
             | (false, "c_Ex") => tweak_ho_quant tptp_ho_exists T args
             | (false, s) =>
               if is_tptp_equal s then
                 if length args = 2 then
                   IConst (`I tptp_equal, T, [])
                 else
                   (* Eta-expand partially applied THF equality, because the
                      LEO-II and Satallax parsers complain about not being able to
                      infer the type of "=". *)
                   let val i_T = domain_type T in
                     IAbs ((`I "Y", i_T),
                           IAbs ((`I "Z", i_T),
                                 IApp (IApp (IConst (`I tptp_equal, T, []),
                                             IConst (`I "Y", i_T, [])),
                                       IConst (`I "Z", i_T, []))))
                   end
               else
                 IConst (name, T, [])
             | _ => IConst (name, T, [])
           else
             IConst (proxy_base |>> prefix const_prefix, T, T_args)
          | NONE => if s = tptp_choice then tweak_ho_quant tptp_choice T args
                    else IConst (name, T, T_args))
      | intro _ _ (IAbs (bound, tm)) = IAbs (bound, intro false [] tm)
      | intro _ _ tm = tm
  in intro true [] end

fun mangle_type_args_in_const type_enc (name as (s, _)) T_args =
  case unprefix_and_unascii const_prefix s of
    NONE => (name, T_args)
  | SOME s'' =>
    case type_arg_policy [] type_enc (invert_const s'') of
      Mangled_Type_Args => (mangled_const_name type_enc T_args name, [])
    | _ => (name, T_args)
fun mangle_type_args_in_iterm type_enc =
  if polymorphism_of_type_enc type_enc = Mangled_Monomorphic then
    let
      fun mangle (IApp (tm1, tm2)) = IApp (mangle tm1, mangle tm2)
        | mangle (tm as IConst (_, _, [])) = tm
        | mangle (IConst (name, T, T_args)) =
          mangle_type_args_in_const type_enc name T_args
          |> (fn (name, T_args) => IConst (name, T, T_args))
        | mangle (IAbs (bound, tm)) = IAbs (bound, mangle tm)
        | mangle tm = tm
    in mangle end
  else
    I

fun chop_fun 0 T = ([], T)
  | chop_fun n (Type (@{type_name fun}, [dom_T, ran_T])) =
    chop_fun (n - 1) ran_T |>> cons dom_T
  | chop_fun _ T = ([], T)

fun filter_type_args _ _ _ _ [] = []
  | filter_type_args keep thy s strip_ty T_args =
    let
      val U = robust_const_type thy s
      val (binder_Us, body_U) = strip_ty U
      val in_U_vars = fold Term.add_tvarsT binder_Us []
      val out_U_vars = Term.add_tvarsT body_U []
      fun filt (U_var, T) =
        if keep (member (op =) in_U_vars U_var,
                 member (op =) out_U_vars U_var) then
          T
        else
          dummyT
      val U_args = (s, U) |> robust_const_typargs thy
    in map (filt o apfst dest_TVar) (U_args ~~ T_args) end
    handle TYPE _ => T_args

fun filter_type_args_in_const _ _ _ _ _ [] = []
  | filter_type_args_in_const thy constrs type_enc ary s T_args =
    case unprefix_and_unascii const_prefix s of
      NONE =>
      if level_of_type_enc type_enc = No_Types orelse s = tptp_choice then []
      else T_args
    | SOME s'' =>
      let val s'' = invert_const s'' in
        case type_arg_policy constrs type_enc s'' of
          Mangled_Type_Args => raise Fail "unexpected (un)mangled symbol"
        | All_Type_Args => T_args
        | Not_Input_Type_Args =>
          filter_type_args (not o fst) thy s'' (chop_fun ary) T_args
        | Constr_Input_Type_Args =>
          filter_type_args fst thy s'' strip_type T_args
        | No_Type_Args => []
      end
fun filter_type_args_in_iterm thy constrs type_enc =
  let
    fun filt ary (IApp (tm1, tm2)) = IApp (filt (ary + 1) tm1, filt 0 tm2)
      | filt ary (IConst (name as (s, _), T, T_args)) =
        filter_type_args_in_const thy constrs type_enc ary s T_args
        |> (fn T_args => IConst (name, T, T_args))
      | filt _ (IAbs (bound, tm)) = IAbs (bound, filt 0 tm)
      | filt _ tm = tm
  in filt 0 end

fun iformula_from_prop ctxt type_enc iff_for_eq =
  let
    val thy = Proof_Context.theory_of ctxt
    fun do_term bs t atomic_Ts =
      iterm_from_term thy type_enc bs (Envir.eta_contract t)
      |>> (introduce_proxies_in_iterm type_enc
           #> mangle_type_args_in_iterm type_enc #> AAtom)
      ||> union (op =) atomic_Ts
    fun do_quant bs q pos s T t' =
      let
        val s = singleton (Name.variant_list (map fst bs)) s
        val universal = Option.map (q = AExists ? not) pos
        val name =
          s |> `(case universal of
                   SOME true => make_all_bound_var
                 | SOME false => make_exist_bound_var
                 | NONE => make_bound_var)
      in
        do_formula ((s, (name, T)) :: bs) pos t'
        #>> mk_aquant q [(name, SOME T)]
        ##> union (op =) (atomic_types_of T)
      end
    and do_conn bs c pos1 t1 pos2 t2 =
      do_formula bs pos1 t1 ##>> do_formula bs pos2 t2 #>> uncurry (mk_aconn c)
    and do_formula bs pos t =
      case t of
        @{const Trueprop} $ t1 => do_formula bs pos t1
      | @{const Not} $ t1 => do_formula bs (Option.map not pos) t1 #>> mk_anot
      | Const (@{const_name All}, _) $ Abs (s, T, t') =>
        do_quant bs AForall pos s T t'
      | (t0 as Const (@{const_name All}, _)) $ t1 =>
        do_formula bs pos (t0 $ eta_expand (map (snd o snd) bs) t1 1)
      | Const (@{const_name Ex}, _) $ Abs (s, T, t') =>
        do_quant bs AExists pos s T t'
      | (t0 as Const (@{const_name Ex}, _)) $ t1 =>
        do_formula bs pos (t0 $ eta_expand (map (snd o snd) bs) t1 1)
      | @{const HOL.conj} $ t1 $ t2 => do_conn bs AAnd pos t1 pos t2
      | @{const HOL.disj} $ t1 $ t2 => do_conn bs AOr pos t1 pos t2
      | @{const HOL.implies} $ t1 $ t2 =>
        do_conn bs AImplies (Option.map not pos) t1 pos t2
      | Const (@{const_name HOL.eq}, Type (_, [@{typ bool}, _])) $ t1 $ t2 =>
        if iff_for_eq then do_conn bs AIff NONE t1 NONE t2 else do_term bs t
      | _ => do_term bs t
  in do_formula [] end

fun presimplify_term thy t =
  if exists_Const (member (op =) Meson.presimplified_consts o fst) t then
    t |> Skip_Proof.make_thm thy
      |> Meson.presimplify
      |> prop_of
  else
    t

fun preprocess_abstractions_in_terms trans_lams facts =
  let
    val (facts, lambda_ts) =
      facts |> map (snd o snd) |> trans_lams
            |>> map2 (fn (name, (role, _)) => fn t => (name, (role, t))) facts
    val lam_facts =
      map2 (fn t => fn j =>
               ((lam_fact_prefix ^ Int.toString j, (Global, Def)), (Axiom, t)))
           lambda_ts (1 upto length lambda_ts)
  in (facts, lam_facts) end

(* Metis's use of "resolve_tac" freezes the schematic variables. We simulate the
   same in Sledgehammer to prevent the discovery of unreplayable proofs. *)
fun freeze_term t =
  let
    fun freeze (t $ u) = freeze t $ freeze u
      | freeze (Abs (s, T, t)) = Abs (s, T, freeze t)
      | freeze (Var ((s, i), T)) =
        Free (atp_weak_prefix ^ s ^ "_" ^ string_of_int i, T)
      | freeze t = t
  in t |> exists_subterm is_Var t ? freeze end

fun presimp_prop ctxt type_enc t =
  let
    val thy = Proof_Context.theory_of ctxt
    val t = t |> Envir.beta_eta_contract
              |> transform_elim_prop
              |> Object_Logic.atomize_term thy
    val need_trueprop = (fastype_of t = @{typ bool})
    val is_ho = is_type_enc_higher_order type_enc
  in
    t |> need_trueprop ? HOLogic.mk_Trueprop
      |> (if is_ho then unextensionalize_def
          else cong_extensionalize_term thy #> abs_extensionalize_term ctxt)
      |> presimplify_term thy
      |> HOLogic.dest_Trueprop
  end
  handle TERM _ => @{const True}

(* Satallax prefers "=" to "<=>" (for definitions) and Metis (CNF) requires "="
   for obscure technical reasons. *)
fun should_use_iff_for_eq CNF _ = false
  | should_use_iff_for_eq (THF _) format = not (is_type_enc_higher_order format)
  | should_use_iff_for_eq _ _ = true

fun make_formula ctxt format type_enc iff_for_eq name stature role t =
  let
    val iff_for_eq = iff_for_eq andalso should_use_iff_for_eq format type_enc
    val (iformula, atomic_Ts) =
      iformula_from_prop ctxt type_enc iff_for_eq (SOME (role <> Conjecture)) t
                         []
      |>> close_universally add_iterm_vars
  in
    {name = name, stature = stature, role = role, iformula = iformula,
     atomic_types = atomic_Ts}
  end

fun is_format_with_defs (THF (_, _, _, THF_With_Defs)) = true
  | is_format_with_defs _ = false

fun make_fact ctxt format type_enc iff_for_eq
              ((name, stature as (_, status)), t) =
  let
    val role =
      if is_format_with_defs format andalso status = Def andalso
         is_legitimate_tptp_def t then
        Definition
      else
        Axiom
  in
    case t |> make_formula ctxt format type_enc iff_for_eq name stature role of
      formula as {iformula = AAtom (IConst ((s, _), _, _)), ...} =>
      if s = tptp_true then NONE else SOME formula
    | formula => SOME formula
  end

fun s_not_prop (@{const Trueprop} $ t) = @{const Trueprop} $ s_not t
  | s_not_prop (@{const "==>"} $ t $ @{prop False}) = t
  | s_not_prop t = @{const "==>"} $ t $ @{prop False}

fun make_conjecture ctxt format type_enc =
  map (fn ((name, stature), (role, t)) =>
          let
            (* FIXME: The commented-out code is a hack to get decent performance
               out of LEO-II on the TPTP THF benchmarks. *)
            val role =
              if (* is_format_with_defs format andalso *)
                 role <> Conjecture andalso is_legitimate_tptp_def t then
                Definition
              else
                role
          in
            t |> role = Conjecture ? s_not
              |> make_formula ctxt format type_enc true name stature role
          end)

(** Finite and infinite type inference **)

fun tvar_footprint thy body s ary =
  (case unprefix_and_unascii const_prefix s of
     SOME s =>
     let
       val (binder_Ts, body_T) =
         s |> invert_const |> robust_const_type thy |> chop_fun ary
       fun tvars_of T =
         [] |> Term.add_tvarsT T
            |> (fn Ts => if body then Ts
                         else subtract (op =) (Term.add_tvarsT body_T []) Ts)
            |> map fst
     in binder_Ts |> map tvars_of end
   | NONE => [])
  handle TYPE _ => []

fun type_arg_cover thy pos body s ary =
  if is_tptp_equal s then
    if pos = SOME false then [] else 0 upto ary - 1
  else
    let
      val footprint = tvar_footprint thy body s ary
      val eq = (s = @{const_name HOL.eq})
      fun cover _ [] = []
        | cover seen ((i, tvars) :: args) =
          cover (union (op =) seen tvars) args
          |> (eq orelse exists (fn tvar => not (member (op =) seen tvar)) tvars)
             ? cons i
    in
      if forall null footprint then
        []
      else
        0 upto length footprint - 1 ~~ footprint
        |> sort (rev_order o list_ord Term_Ord.indexname_ord o pairself snd)
        |> cover []
    end

type monotonicity_info =
  {maybe_finite_Ts : typ list,
   surely_infinite_Ts : typ list,
   maybe_nonmono_Ts : typ list}

(* These types witness that the type classes they belong to allow infinite
   models and hence that any types with these type classes is monotonic. *)
val known_infinite_types =
  [@{typ nat}, HOLogic.intT, HOLogic.realT, @{typ "nat => bool"}]

fun is_type_kind_of_surely_infinite ctxt strictness cached_Ts T =
  strictness <> Strict andalso is_type_surely_infinite ctxt true cached_Ts T

(* Finite types such as "unit", "bool", "bool * bool", and "bool => bool" are
   dangerous because their "exhaust" properties can easily lead to unsound ATP
   proofs. On the other hand, all HOL infinite types can be given the same
   models in first-order logic (via Löwenheim-Skolem). *)

fun should_encode_type _ (_ : monotonicity_info) All_Types _ = true
  | should_encode_type ctxt {maybe_finite_Ts, surely_infinite_Ts,
                             maybe_nonmono_Ts, ...}
                       (Nonmono_Types (strictness, _)) T =
    let val thy = Proof_Context.theory_of ctxt in
      (exists (type_intersect thy T) maybe_nonmono_Ts andalso
       not (exists (type_instance thy T) surely_infinite_Ts orelse
            (not (member (type_equiv thy) maybe_finite_Ts T) andalso
             is_type_kind_of_surely_infinite ctxt strictness surely_infinite_Ts
                                             T)))
    end
  | should_encode_type _ _ Undercover_Types _ = true
  | should_encode_type _ _ _ _ = false

fun should_guard_type ctxt mono (Guards (_, level)) should_guard_var T =
    should_guard_var () andalso should_encode_type ctxt mono level T
  | should_guard_type _ _ _ _ _ = false

fun is_maybe_universal_var (IConst ((s, _), _, _)) =
    String.isPrefix bound_var_prefix s orelse
    String.isPrefix all_bound_var_prefix s
  | is_maybe_universal_var (IVar _) = true
  | is_maybe_universal_var _ = false

datatype site =
  Top_Level of bool option |
  Eq_Arg of bool option |
  Arg of string * int * int |
  Elsewhere

fun should_tag_with_type _ _ _ (Top_Level _) _ _ = false
  | should_tag_with_type ctxt mono (Tags (_, level)) site u T =
    let val thy = Proof_Context.theory_of ctxt in
      case level of
        Nonmono_Types (_, Non_Uniform) =>
        (case (site, is_maybe_universal_var u) of
           (Eq_Arg _, true) => should_encode_type ctxt mono level T
         | _ => false)
      | Undercover_Types =>
        (case (site, is_maybe_universal_var u) of
           (Eq_Arg pos, true) => pos <> SOME false
         | (Arg (s, j, ary), true) =>
           member (op =) (type_arg_cover thy NONE true s ary) j
         | _ => false)
      | _ => should_encode_type ctxt mono level T
    end
  | should_tag_with_type _ _ _ _ _ _ = false

fun fused_type ctxt mono level =
  let
    val should_encode = should_encode_type ctxt mono level
    fun fuse 0 T = if should_encode T then T else fused_infinite_type
      | fuse ary (Type (@{type_name fun}, [T1, T2])) =
        fuse 0 T1 --> fuse (ary - 1) T2
      | fuse _ _ = raise Fail "expected function type"
  in fuse end

(** predicators and application operators **)

type sym_info =
  {pred_sym : bool, min_ary : int, max_ary : int, types : typ list,
   in_conj : bool}

fun default_sym_tab_entries type_enc =
  (make_fixed_const NONE @{const_name undefined},
       {pred_sym = false, min_ary = 0, max_ary = 0, types = [],
        in_conj = false}) ::
  ([tptp_false, tptp_true]
   |> map (rpair {pred_sym = true, min_ary = 0, max_ary = 0, types = [],
                  in_conj = false})) @
  ([tptp_equal, tptp_old_equal]
   |> map (rpair {pred_sym = true, min_ary = 2, max_ary = 2, types = [],
                  in_conj = false}))
  |> not (is_type_enc_higher_order type_enc)
     ? cons (prefixed_predicator_name,
             {pred_sym = true, min_ary = 1, max_ary = 1, types = [],
              in_conj = false})

datatype app_op_level =
  Min_App_Op |
  Sufficient_App_Op |
  Sufficient_App_Op_And_Predicator |
  Full_App_Op_And_Predicator

fun add_iterm_syms_to_sym_table ctxt app_op_level conj_fact =
  let
    val thy = Proof_Context.theory_of ctxt
    fun consider_var_ary const_T var_T max_ary =
      let
        fun iter ary T =
          if ary = max_ary orelse type_instance thy var_T T orelse
             type_instance thy T var_T then
            ary
          else
            iter (ary + 1) (range_type T)
      in iter 0 const_T end
    fun add_universal_var T (accum as ((bool_vars, fun_var_Ts), sym_tab)) =
      if (app_op_level = Sufficient_App_Op andalso can dest_funT T) orelse
         (app_op_level = Sufficient_App_Op_And_Predicator andalso
          (can dest_funT T orelse T = @{typ bool})) then
        let
          val bool_vars' =
            bool_vars orelse
            (app_op_level = Sufficient_App_Op_And_Predicator andalso
             body_type T = @{typ bool})
          fun repair_min_ary {pred_sym, min_ary, max_ary, types, in_conj} =
            {pred_sym = pred_sym andalso not bool_vars',
             min_ary = fold (fn T' => consider_var_ary T' T) types min_ary,
             max_ary = max_ary, types = types, in_conj = in_conj}
          val fun_var_Ts' =
            fun_var_Ts |> can dest_funT T ? insert_type thy I T
        in
          if bool_vars' = bool_vars andalso
             pointer_eq (fun_var_Ts', fun_var_Ts) then
            accum
          else
            ((bool_vars', fun_var_Ts'), Symtab.map (K repair_min_ary) sym_tab)
        end
      else
        accum
    fun add_iterm_syms top_level tm
                       (accum as ((bool_vars, fun_var_Ts), sym_tab)) =
      let val (head, args) = strip_iterm_comb tm in
        (case head of
           IConst ((s, _), T, _) =>
           if String.isPrefix bound_var_prefix s orelse
              String.isPrefix all_bound_var_prefix s then
             add_universal_var T accum
           else if String.isPrefix exist_bound_var_prefix s then
             accum
           else
             let val ary = length args in
               ((bool_vars, fun_var_Ts),
                case Symtab.lookup sym_tab s of
                  SOME {pred_sym, min_ary, max_ary, types, in_conj} =>
                  let
                    val pred_sym =
                      pred_sym andalso top_level andalso not bool_vars
                    val types' = types |> insert_type thy I T
                    val in_conj = in_conj orelse conj_fact
                    val min_ary =
                      if (app_op_level = Sufficient_App_Op orelse
                          app_op_level = Sufficient_App_Op_And_Predicator)
                         andalso not (pointer_eq (types', types)) then
                        fold (consider_var_ary T) fun_var_Ts min_ary
                      else
                        min_ary
                  in
                    Symtab.update (s, {pred_sym = pred_sym,
                                       min_ary = Int.min (ary, min_ary),
                                       max_ary = Int.max (ary, max_ary),
                                       types = types', in_conj = in_conj})
                                  sym_tab
                  end
                | NONE =>
                  let
                    val pred_sym = top_level andalso not bool_vars
                    val ary =
                      case unprefix_and_unascii const_prefix s of
                        SOME s =>
                        (if String.isSubstring uncurried_alias_sep s then
                           ary
                         else case try (robust_const_ary thy
                                        o invert_const o hd
                                        o unmangled_const_name) s of
                           SOME ary0 => Int.min (ary0, ary)
                         | NONE => ary)
                      | NONE => ary
                    val min_ary =
                      case app_op_level of
                        Min_App_Op => ary
                      | Full_App_Op_And_Predicator => 0
                      | _ => fold (consider_var_ary T) fun_var_Ts ary
                  in
                    Symtab.update_new (s,
                        {pred_sym = pred_sym, min_ary = min_ary,
                         max_ary = ary, types = [T], in_conj = conj_fact})
                        sym_tab
                  end)
             end
         | IVar (_, T) => add_universal_var T accum
         | IAbs ((_, T), tm) =>
           accum |> add_universal_var T |> add_iterm_syms false tm
         | _ => accum)
        |> fold (add_iterm_syms false) args
      end
  in add_iterm_syms end

fun sym_table_for_facts ctxt type_enc app_op_level conjs facts =
  let
    fun add_iterm_syms conj_fact =
      add_iterm_syms_to_sym_table ctxt app_op_level conj_fact true
    fun add_fact_syms conj_fact =
      K (add_iterm_syms conj_fact) |> formula_fold NONE |> ifact_lift
  in
    ((false, []), Symtab.empty)
    |> fold (add_fact_syms true) conjs
    |> fold (add_fact_syms false) facts
    ||> fold Symtab.update (default_sym_tab_entries type_enc)
  end

fun min_ary_of sym_tab s =
  case Symtab.lookup sym_tab s of
    SOME ({min_ary, ...} : sym_info) => min_ary
  | NONE =>
    case unprefix_and_unascii const_prefix s of
      SOME s =>
      let val s = s |> unmangled_const_name |> hd |> invert_const in
        if s = predicator_name then 1
        else if s = app_op_name then 2
        else if s = type_guard_name then 1
        else 0
      end
    | NONE => 0

(* True if the constant ever appears outside of the top-level position in
   literals, or if it appears with different arities (e.g., because of different
   type instantiations). If false, the constant always receives all of its
   arguments and is used as a predicate. *)
fun is_pred_sym sym_tab s =
  case Symtab.lookup sym_tab s of
    SOME ({pred_sym, min_ary, max_ary, ...} : sym_info) =>
    pred_sym andalso min_ary = max_ary
  | NONE => false

val fTrue_iconst =
  IConst ((const_prefix ^ "fTrue", @{const_name ATP.fTrue}), @{typ bool}, [])
val predicator_iconst =
  IConst (`(make_fixed_const NONE) predicator_name, @{typ "bool => bool"}, [])

fun predicatify completish tm =
  if completish then
    IApp (IApp (IConst (`I tptp_equal, @{typ "bool => bool => bool"}, []), tm),
          fTrue_iconst)
  else
    IApp (predicator_iconst, tm)

val app_op = `(make_fixed_const NONE) app_op_name

fun list_app head args = fold (curry (IApp o swap)) args head

fun mk_app_op type_enc head arg =
  let
    val head_T = ityp_of head
    val (arg_T, res_T) = dest_funT head_T
    val app =
      IConst (app_op, head_T --> head_T, [arg_T, res_T])
      |> mangle_type_args_in_iterm type_enc
  in list_app app [head, arg] end

fun firstorderize_fact thy constrs type_enc sym_tab uncurried_aliases
                       completish =
  let
    fun do_app arg head = mk_app_op type_enc head arg
    fun list_app_ops head args = fold do_app args head
    fun introduce_app_ops tm =
      let val (head, args) = tm |> strip_iterm_comb ||> map introduce_app_ops in
        case head of
          IConst (name as (s, _), T, T_args) =>
          if uncurried_aliases andalso String.isPrefix const_prefix s then
            let
              val ary = length args
              val name =
                name |> ary > min_ary_of sym_tab s ? aliased_uncurried ary
            in list_app (IConst (name, T, T_args)) args end
          else
            args |> chop (min_ary_of sym_tab s)
                 |>> list_app head |-> list_app_ops
        | _ => list_app_ops head args
      end
    fun introduce_predicators tm =
      case strip_iterm_comb tm of
        (IConst ((s, _), _, _), _) =>
        if is_pred_sym sym_tab s then tm else predicatify completish tm
      | _ => predicatify completish tm
    val do_iterm =
      not (is_type_enc_higher_order type_enc)
      ? (introduce_app_ops #> introduce_predicators)
      #> filter_type_args_in_iterm thy constrs type_enc
  in update_iformula (formula_map do_iterm) end

(** Helper facts **)

val not_ffalse = @{lemma "~ fFalse" by (unfold fFalse_def) fast}
val ftrue = @{lemma "fTrue" by (unfold fTrue_def) fast}

(* The Boolean indicates that a fairly sound type encoding is needed. *)
val base_helper_table =
  [(("COMBI", false), [(Def, @{thm Meson.COMBI_def})]),
   (("COMBK", false), [(Def, @{thm Meson.COMBK_def})]),
   (("COMBB", false), [(Def, @{thm Meson.COMBB_def})]),
   (("COMBC", false), [(Def, @{thm Meson.COMBC_def})]),
   (("COMBS", false), [(Def, @{thm Meson.COMBS_def})]),
   ((predicator_name, false), [(General, not_ffalse), (General, ftrue)]),
   (("fFalse", false), [(General, not_ffalse)]),
   (("fFalse", true), [(General, @{thm True_or_False})]),
   (("fTrue", false), [(General, ftrue)]),
   (("fTrue", true), [(General, @{thm True_or_False})]),
   (("If", true),
    [(Def, @{thm if_True}), (Def, @{thm if_False}),
     (General, @{thm True_or_False})])]

val helper_table =
  base_helper_table @
  [(("fNot", false),
    @{thms fNot_def [THEN Meson.iff_to_disjD, THEN conjunct1]
           fNot_def [THEN Meson.iff_to_disjD, THEN conjunct2]}
    |> map (pair Def)),
   (("fconj", false),
    @{lemma "~ P | ~ Q | fconj P Q" "~ fconj P Q | P" "~ fconj P Q | Q"
        by (unfold fconj_def) fast+}
    |> map (pair General)),
   (("fdisj", false),
    @{lemma "~ P | fdisj P Q" "~ Q | fdisj P Q" "~ fdisj P Q | P | Q"
        by (unfold fdisj_def) fast+}
    |> map (pair General)),
   (("fimplies", false),
    @{lemma "P | fimplies P Q" "~ Q | fimplies P Q" "~ fimplies P Q | ~ P | Q"
        by (unfold fimplies_def) fast+}
    |> map (pair General)),
   (("fequal", true),
    (* This is a lie: Higher-order equality doesn't need a sound type encoding.
       However, this is done so for backward compatibility: Including the
       equality helpers by default in Metis breaks a few existing proofs. *)
    @{thms fequal_def [THEN Meson.iff_to_disjD, THEN conjunct1]
           fequal_def [THEN Meson.iff_to_disjD, THEN conjunct2]}
    |> map (pair General)),
   (* Partial characterization of "fAll" and "fEx". A complete characterization
      would require the axiom of choice for replay with Metis. *)
   (("fAll", false),
    [(General, @{lemma "~ fAll P | P x" by (auto simp: fAll_def)})]),
   (("fEx", false),
    [(General, @{lemma "~ P x | fEx P" by (auto simp: fEx_def)})])]
  |> map (apsnd (map (apsnd zero_var_indexes)))

val completish_helper_table =
  base_helper_table @
  [((predicator_name, true),
    @{thms True_or_False fTrue_ne_fFalse} |> map (pair General)),
   ((app_op_name, true),
    [(General, @{lemma "EX x. ~ f x = g x | f = g" by blast})]),
   (("fconj", false),
    @{thms fconj_table fconj_laws fdisj_laws} |> map (pair Def)),
   (("fdisj", false),
    @{thms fdisj_table fconj_laws fdisj_laws} |> map (pair Def)),
   (("fimplies", false),
    @{thms fimplies_table fconj_laws fdisj_laws fimplies_laws}
    |> map (pair Def)),
   (("fequal", false),
    (@{thms fequal_table} |> map (pair Def)) @
    (@{thms fequal_laws} |> map (pair General))),
   (("fAll", false),
    @{thms fAll_table fComp_law fAll_law fEx_law} |> map (pair Def)),
   (("fEx", false),
    @{thms fEx_table fComp_law fAll_law fEx_law} |> map (pair Def))]
  |> map (apsnd (map (apsnd zero_var_indexes)))

fun bound_tvars type_enc sorts Ts =
  case filter is_TVar Ts of
    [] => I
  | Ts =>
    (sorts ? mk_ahorn (Ts |> class_membs_for_types type_enc add_sorts_on_tvar
                          |> map (class_atom type_enc)))
    #> (case type_enc of
          Native (_, poly, _) =>
          mk_atyquant AForall
              (map (fn TVar (z as (_, S)) =>
                       (AType (tvar_name z, []),
                        if poly = Type_Class_Polymorphic then
                          map (`make_class) (normalize_classes S)
                        else
                          [])) Ts)
        | _ =>
          mk_aquant AForall (map (fn TVar z => (tvar_name z, NONE)) Ts))

fun eq_formula type_enc atomic_Ts bounds pred_sym tm1 tm2 =
  (if pred_sym then AConn (AIff, [AAtom tm1, AAtom tm2])
   else AAtom (ATerm ((`I tptp_equal, []), [tm1, tm2])))
  |> mk_aquant AForall bounds
  |> close_formula_universally
  |> bound_tvars type_enc true atomic_Ts

val helper_rank = default_rank
val min_rank = 9 * helper_rank div 10
val max_rank = 4 * min_rank

fun rank_of_fact_num n j = min_rank + (max_rank - min_rank) * j div n

val type_tag = `(make_fixed_const NONE) type_tag_name

fun could_specialize_helpers type_enc =
  not (is_type_enc_polymorphic type_enc) andalso
  level_of_type_enc type_enc <> No_Types
fun should_specialize_helper type_enc t =
  could_specialize_helpers type_enc andalso
  not (null (Term.hidden_polymorphism t))

fun add_helper_facts_for_sym ctxt format type_enc completish
                             (s, {types, ...} : sym_info) =
  case unprefix_and_unascii const_prefix s of
    SOME mangled_s =>
    let
      val thy = Proof_Context.theory_of ctxt
      val unmangled_s = mangled_s |> unmangled_const_name |> hd
      fun dub needs_sound j k =
        ascii_of unmangled_s ^ "_" ^ string_of_int j ^ "_" ^ string_of_int k ^
        (if mangled_s = unmangled_s then "" else "_" ^ ascii_of mangled_s) ^
        (if needs_sound then typed_helper_suffix else untyped_helper_suffix)
      fun specialize_helper t T =
        if unmangled_s = app_op_name then
          let
            val tyenv =
              Sign.typ_match thy (alpha_to_beta, domain_type T) Vartab.empty
          in monomorphic_term tyenv t end
        else
          specialize_type thy (invert_const unmangled_s, T) t
      fun dub_and_inst needs_sound ((status, t), j) =
        (if should_specialize_helper type_enc t then
           map_filter (try (specialize_helper t)) types
         else
           [t])
        |> tag_list 1
        |> map (fn (k, t) => ((dub needs_sound j k, (Global, status)), t))
      val make_facts = map_filter (make_fact ctxt format type_enc false)
      val sound = is_type_enc_sound type_enc
      val could_specialize = could_specialize_helpers type_enc
    in
      fold (fn ((helper_s, needs_sound), ths) =>
               if (needs_sound andalso not sound) orelse
                  (helper_s <> unmangled_s andalso
                   (not completish orelse could_specialize)) then
                 I
               else
                 ths ~~ (1 upto length ths)
                 |> maps (dub_and_inst needs_sound o apfst (apsnd prop_of))
                 |> make_facts
                 |> union (op = o pairself #iformula))
           (if completish then completish_helper_table else helper_table)
    end
  | NONE => I
fun helper_facts_for_sym_table ctxt format type_enc completish sym_tab =
  Symtab.fold_rev (add_helper_facts_for_sym ctxt format type_enc completish)
                  sym_tab []

(***************************************************************)
(* Type Classes Present in the Axiom or Conjecture Clauses     *)
(***************************************************************)

fun set_insert (x, s) = Symtab.update (x, ()) s

fun add_classes (cls, cset) = List.foldl set_insert cset (flat cls)

fun classes_of_terms get_Ts =
  map (map snd o get_Ts)
  #> List.foldl add_classes Symtab.empty #> Symtab.delete_safe class_of_types
  #> Symtab.keys

val tfree_classes_of_terms = classes_of_terms Misc_Legacy.term_tfrees
val tvar_classes_of_terms = classes_of_terms Misc_Legacy.term_tvars

fun fold_type_constrs f (Type (s, Ts)) x =
    fold (fold_type_constrs f) Ts (f (s, x))
  | fold_type_constrs _ _ x = x

(* Type constructors used to instantiate overloaded constants are the only ones
   needed. *)
fun add_type_constrs_in_term thy =
  let
    fun add (Const (@{const_name Meson.skolem}, _) $ _) = I
      | add (t $ u) = add t #> add u
      | add (Const x) =
        x |> robust_const_typargs thy |> fold (fold_type_constrs set_insert)
      | add (Abs (_, _, u)) = add u
      | add _ = I
  in add end

fun type_constrs_of_terms thy ts =
  Symtab.keys (fold (add_type_constrs_in_term thy) ts Symtab.empty)

fun extract_lambda_def (Const (@{const_name HOL.eq}, _) $ t $ u) =
    let val (head, args) = strip_comb t in
      (head |> dest_Const |> fst,
       fold_rev (fn t as Var ((s, _), T) =>
                    (fn u => Abs (s, T, abstract_over (t, u)))
                  | _ => raise Fail "expected \"Var\"") args u)
    end
  | extract_lambda_def _ = raise Fail "malformed lifted lambda"

fun trans_lams_from_string ctxt type_enc lam_trans =
  if lam_trans = no_lamsN then
    rpair []
  else if lam_trans = hide_lamsN then
    lift_lams ctxt type_enc ##> K []
  else if lam_trans = liftingN orelse lam_trans = lam_liftingN then
    lift_lams ctxt type_enc
  else if lam_trans = combsN then
    map (introduce_combinators ctxt) #> rpair []
  else if lam_trans = combs_and_liftingN then
    lift_lams_part_1 ctxt type_enc
    ##> maps (fn t => [t, introduce_combinators ctxt (intentionalize_def t)])
    #> lift_lams_part_2 ctxt
  else if lam_trans = combs_or_liftingN then
    lift_lams_part_1 ctxt type_enc
    ##> map (fn t => case head_of (strip_qnt_body @{const_name All} t) of
                       @{term "op =::bool => bool => bool"} => t
                     | _ => introduce_combinators ctxt (intentionalize_def t))
    #> lift_lams_part_2 ctxt
  else if lam_trans = keep_lamsN then
    map (Envir.eta_contract) #> rpair []
  else
    error ("Unknown lambda translation scheme: " ^ quote lam_trans ^ ".")

val pull_and_reorder_definitions =
  let
    fun add_consts (IApp (t, u)) = fold add_consts [t, u]
      | add_consts (IAbs (_, t)) = add_consts t
      | add_consts (IConst (name, _, _)) = insert (op =) name
      | add_consts (IVar _) = I
    fun consts_of_hs l_or_r ({iformula, ...} : ifact) =
      case iformula of
        AAtom (IApp (IApp (IConst _, t), u)) => add_consts (l_or_r (t, u)) []
      | _ => []
    (* Quadratic, but usually OK. *)
    fun reorder [] [] = []
      | reorder (fact :: skipped) [] =
        fact :: reorder [] skipped (* break cycle *)
      | reorder skipped (fact :: facts) =
        let val rhs_consts = consts_of_hs snd fact in
          if exists (exists (exists (member (op =) rhs_consts)
                     o consts_of_hs fst)) [skipped, facts] then
            reorder (fact :: skipped) facts
          else
            fact :: reorder [] (facts @ skipped)
        end
  in List.partition (curry (op =) Definition o #role) #>> reorder [] #> op @ end

fun translate_formulas ctxt prem_role format type_enc lam_trans presimp hyp_ts
                       concl_t facts =
  let
    val thy = Proof_Context.theory_of ctxt
    val trans_lams = trans_lams_from_string ctxt type_enc lam_trans
    val fact_ts = facts |> map snd
    (* Remove existing facts from the conjecture, as this can dramatically
       boost an ATP's performance (for some reason). *)
    val hyp_ts =
      hyp_ts
      |> map (fn t => if member (op aconv) fact_ts t then @{prop True} else t)
    val facts = facts |> map (apsnd (pair Axiom))
    val conjs =
      map (pair prem_role) hyp_ts @ [(Conjecture, s_not_prop concl_t)]
      |> map (apsnd freeze_term)
      |> map2 (pair o rpair (Local, General) o string_of_int)
              (0 upto length hyp_ts)
    val ((conjs, facts), lam_facts) =
      (conjs, facts)
      |> presimp ? pairself (map (apsnd (apsnd (presimp_prop ctxt type_enc))))
      |> (if lam_trans = no_lamsN then
            rpair []
          else
            op @
            #> preprocess_abstractions_in_terms trans_lams
            #>> chop (length conjs))
    val conjs =
      conjs |> make_conjecture ctxt format type_enc
            |> pull_and_reorder_definitions
    val facts =
      facts |> map_filter (fn (name, (_, t)) =>
                              make_fact ctxt format type_enc true (name, t))
            |> pull_and_reorder_definitions
    val fact_names =
      facts |> map (fn {name, stature, ...} : ifact => (name, stature))
    val lifted = lam_facts |> map (extract_lambda_def o snd o snd)
    val lam_facts =
      lam_facts |> map_filter (make_fact ctxt format type_enc true o apsnd snd)
    val all_ts = concl_t :: hyp_ts @ fact_ts
    val subs = tfree_classes_of_terms all_ts
    val supers = tvar_classes_of_terms all_ts
    val tycons = type_constrs_of_terms thy all_ts
    val (supers, tcon_clauses) =
      if level_of_type_enc type_enc = No_Types then ([], [])
      else make_tcon_clauses thy tycons supers
    val subclass_pairs = make_subclass_pairs thy subs supers
  in
    (fact_names |> map single, union (op =) subs supers, conjs,
     facts @ lam_facts, subclass_pairs, tcon_clauses, lifted)
  end

val type_guard = `(make_fixed_const NONE) type_guard_name

fun type_guard_iterm type_enc T tm =
  IApp (IConst (type_guard, T --> @{typ bool}, [T])
        |> mangle_type_args_in_iterm type_enc, tm)

fun is_var_positively_naked_in_term _ (SOME false) _ accum = accum
  | is_var_positively_naked_in_term name _ (ATerm (((s, _), _), tms)) accum =
    accum orelse
    (is_tptp_equal s andalso member (op =) tms (ATerm ((name, []), [])))
  | is_var_positively_naked_in_term _ _ _ _ = true

fun is_var_undercover_in_term thy name pos tm accum =
  accum orelse
  let
    val var = ATerm ((name, []), [])
    fun is_undercover (ATerm (_, [])) = false
      | is_undercover (ATerm (((s, _), _), tms)) =
        let
          val ary = length tms
          val cover = type_arg_cover thy pos true s ary
        in
          exists (fn (j, tm) => tm = var andalso member (op =) cover j)
                 (0 upto ary - 1 ~~ tms) orelse
          exists is_undercover tms
        end
      | is_undercover _ = true
  in is_undercover tm end

fun should_guard_var_in_formula thy level pos phi (SOME true) name =
    (case level of
       All_Types => true
     | Nonmono_Types (_, Uniform) => true
     | Nonmono_Types (_, Non_Uniform) =>
       formula_fold pos (is_var_positively_naked_in_term name) phi false
     | Undercover_Types =>
       formula_fold pos (is_var_undercover_in_term thy name) phi false
     | _ => false)
  | should_guard_var_in_formula _ _ _ _ _ _ = true

fun always_guard_var_in_formula _ _ _ _ _ _ = true

fun should_generate_tag_bound_decl _ _ _ (SOME true) _ = false
  | should_generate_tag_bound_decl ctxt mono (Tags (_, level)) _ T =
    not (is_type_level_uniform level) andalso
    should_encode_type ctxt mono level T
  | should_generate_tag_bound_decl _ _ _ _ _ = false

fun mk_aterm type_enc name T_args args =
  let val (ty_args, tm_args) = process_type_args type_enc T_args in
    ATerm ((name, ty_args), tm_args @ args)
  end

fun do_bound_type ctxt mono type_enc =
  case type_enc of
    Native (_, _, level) =>
    fused_type ctxt mono level 0 #> native_ho_type_from_typ type_enc false 0
    #> SOME
  | _ => K NONE

fun tag_with_type ctxt mono type_enc pos T tm =
  IConst (type_tag, T --> T, [T])
  |> mangle_type_args_in_iterm type_enc
  |> ho_term_from_iterm ctxt mono type_enc pos
  |> (fn ATerm ((s, tys), tms) => ATerm ((s, tys), tms @ [tm])
       | _ => raise Fail "unexpected lambda-abstraction")
and ho_term_from_iterm ctxt mono type_enc pos =
  let
    fun term site u =
      let
        val (head, args) = strip_iterm_comb u
        val pos =
          case site of
            Top_Level pos => pos
          | Eq_Arg pos => pos
          | _ => NONE
        val t =
          case head of
            IConst (name as (s, _), _, T_args) =>
            let
              val ary = length args
              fun arg_site j =
                if is_tptp_equal s then Eq_Arg pos else Arg (s, j, ary)
            in
              map2 (fn j => term (arg_site j)) (0 upto ary - 1) args
              |> mk_aterm type_enc name T_args
            end
          | IVar (name, _) =>
            map (term Elsewhere) args |> mk_aterm type_enc name []
          | IAbs ((name, T), tm) =>
            if is_type_enc_higher_order type_enc then
              AAbs (((name, native_ho_type_from_typ type_enc true 0 T), (* FIXME? why "true"? *)
                     term Elsewhere tm), map (term Elsewhere) args)
            else
              raise Fail "unexpected lambda-abstraction"
          | IApp _ => raise Fail "impossible \"IApp\""
        val T = ityp_of u
      in
        if should_tag_with_type ctxt mono type_enc site u T then
          tag_with_type ctxt mono type_enc pos T t
        else
          t
      end
  in term (Top_Level pos) end
and formula_from_iformula ctxt mono type_enc should_guard_var =
  let
    val thy = Proof_Context.theory_of ctxt
    val level = level_of_type_enc type_enc
    val do_term = ho_term_from_iterm ctxt mono type_enc
    fun do_out_of_bound_type pos phi universal (name, T) =
      if should_guard_type ctxt mono type_enc
             (fn () => should_guard_var thy level pos phi universal name) T then
        IVar (name, T)
        |> type_guard_iterm type_enc T
        |> do_term pos |> AAtom |> SOME
      else if should_generate_tag_bound_decl ctxt mono type_enc universal T then
        let
          val var = ATerm ((name, []), [])
          val tagged_var = tag_with_type ctxt mono type_enc pos T var
        in SOME (AAtom (ATerm ((`I tptp_equal, []), [tagged_var, var]))) end
      else
        NONE
    fun do_formula pos (ATyQuant (q, xs, phi)) =
        ATyQuant (q, map (apfst (native_ho_type_from_typ type_enc false 0)) xs,
                  do_formula pos phi)
      | do_formula pos (AQuant (q, xs, phi)) =
        let
          val phi = phi |> do_formula pos
          val universal = Option.map (q = AExists ? not) pos
          val do_bound_type = do_bound_type ctxt mono type_enc
        in
          AQuant (q, xs |> map (apsnd (fn NONE => NONE
                                        | SOME T => do_bound_type T)),
                  (if q = AForall then mk_ahorn else fold_rev (mk_aconn AAnd))
                      (map_filter
                           (fn (_, NONE) => NONE
                             | (s, SOME T) =>
                               do_out_of_bound_type pos phi universal (s, T))
                           xs)
                      phi)
        end
      | do_formula pos (AConn conn) = aconn_map pos do_formula conn
      | do_formula pos (AAtom tm) = AAtom (do_term pos tm)
  in do_formula end

(* Each fact is given a unique fact number to avoid name clashes (e.g., because
   of monomorphization). The TPTP explicitly forbids name clashes, and some of
   the remote provers might care. *)
fun line_for_fact ctxt prefix encode freshen pos mono type_enc rank
                  (j, {name, stature, role, iformula, atomic_types}) =
  (prefix ^ (if freshen then string_of_int j ^ "_" else "") ^ encode name, role,
   iformula
   |> formula_from_iformula ctxt mono type_enc should_guard_var_in_formula
                            (if pos then SOME true else NONE)
   |> close_formula_universally
   |> bound_tvars type_enc true atomic_types,
   NONE,
   let val rank = rank j in
     case snd stature of
       Intro => isabelle_info introN rank
     | Inductive => isabelle_info inductiveN rank
     | Elim => isabelle_info elimN rank
     | Simp => isabelle_info simpN rank
     | Def => isabelle_info defN rank
     | _ => isabelle_info "" rank
   end)
  |> Formula

fun lines_for_subclass type_enc sub super =
  Formula (subclass_prefix ^ ascii_of sub ^ "___" ^ ascii_of super, Axiom,
           AConn (AImplies,
                  [sub, super] |> map (fn s => class_atom type_enc (s, tvar_a)))
           |> bound_tvars type_enc false [tvar_a],
           NONE, isabelle_info inductiveN helper_rank)

fun lines_for_subclass_pair type_enc (sub, supers) =
  if polymorphism_of_type_enc type_enc = Type_Class_Polymorphic then
    [Class_Decl (class_decl_prefix ^ ascii_of sub, `make_class sub,
                 map (`make_class) supers)]
  else
    map (lines_for_subclass type_enc sub) supers

fun line_for_tcon_clause type_enc (name, prems, (cl, T)) =
  if polymorphism_of_type_enc type_enc = Type_Class_Polymorphic then
    Class_Memb (class_memb_prefix ^ name,
                map (fn (cls, T) =>
                        (T |> dest_TVar |> tvar_name, map (`make_class) cls))
                    prems,
                native_ho_type_from_typ type_enc false 0 T, `make_class cl)
  else
    Formula (tcon_clause_prefix ^ name, Axiom,
             mk_ahorn (maps (class_atoms type_enc) prems)
                      (class_atom type_enc (cl, T))
             |> bound_tvars type_enc true (snd (dest_Type T)),
             NONE, isabelle_info inductiveN helper_rank)

fun line_for_conjecture ctxt mono type_enc
                        ({name, role, iformula, atomic_types, ...} : ifact) =
  Formula (conjecture_prefix ^ name, role,
           iformula
           |> formula_from_iformula ctxt mono type_enc
                  should_guard_var_in_formula (SOME false)
           |> close_formula_universally
           |> bound_tvars type_enc true atomic_types, NONE, [])

fun lines_for_free_types type_enc (facts : ifact list) =
  if is_type_enc_polymorphic type_enc then
    let
      val type_classes =
        (polymorphism_of_type_enc type_enc = Type_Class_Polymorphic)
      fun line j (cl, T) =
        if type_classes then
          Class_Memb (class_memb_prefix ^ string_of_int j, [],
                      native_ho_type_from_typ type_enc false 0 T,
                      `make_class cl)
        else
          Formula (tfree_clause_prefix ^ string_of_int j, Hypothesis,
                   class_atom type_enc (cl, T), NONE, [])
      val membs =
        fold (union (op =)) (map #atomic_types facts) []
        |> class_membs_for_types type_enc add_sorts_on_tfree
    in map2 line (0 upto length membs - 1) membs end
  else
    []

(** Symbol declarations **)

fun decl_line_for_class phantoms s =
  let val name as (s, _) = `make_class s in
    Sym_Decl (sym_decl_prefix ^ s, name,
              APi ([tvar_a_name],
                   if phantoms = Without_Phantom_Type_Vars then
                     AFun (a_itself_atype, bool_atype)
                   else
                     bool_atype))
  end

fun decl_lines_for_classes type_enc classes =
  case type_enc of
    Native (_, Raw_Polymorphic phantoms, _) =>
    map (decl_line_for_class phantoms) classes
  | _ => []

fun sym_decl_table_for_facts thy type_enc sym_tab (conjs, facts, extra_tms) =
  let
    fun add_iterm_syms tm =
      let val (head, args) = strip_iterm_comb tm in
        (case head of
           IConst ((s, s'), T, T_args) =>
           let
             val (pred_sym, in_conj) =
               case Symtab.lookup sym_tab s of
                 SOME ({pred_sym, in_conj, ...} : sym_info) =>
                 (pred_sym, in_conj)
               | NONE => (false, false)
             val decl_sym =
               (case type_enc of
                  Guards _ => not pred_sym
                | _ => true) andalso
               is_tptp_user_symbol s
           in
             if decl_sym then
               Symtab.map_default (s, [])
                   (insert_type thy #3 (s', T_args, T, pred_sym, length args,
                                        in_conj))
             else
               I
           end
         | IAbs (_, tm) => add_iterm_syms tm
         | _ => I)
        #> fold add_iterm_syms args
      end
    val add_fact_syms = K add_iterm_syms |> formula_fold NONE |> ifact_lift
    fun add_formula_var_types (ATyQuant (_, _, phi)) = add_formula_var_types phi
      | add_formula_var_types (AQuant (_, xs, phi)) =
        fold (fn (_, SOME T) => insert_type thy I T | _ => I) xs
        #> add_formula_var_types phi
      | add_formula_var_types (AConn (_, phis)) =
        fold add_formula_var_types phis
      | add_formula_var_types _ = I
    fun var_types () =
      if is_type_enc_polymorphic type_enc then [tvar_a]
      else fold (ifact_lift add_formula_var_types) (conjs @ facts) []
    fun add_undefined_const T =
      let
        val (s, s') =
          `(make_fixed_const NONE) @{const_name undefined}
          |> (case type_arg_policy [] type_enc @{const_name undefined} of
                Mangled_Type_Args => mangled_const_name type_enc [T]
              | _ => I)
      in
        Symtab.map_default (s, [])
                           (insert_type thy #3 (s', [T], T, false, 0, false))
      end
    fun add_TYPE_const () =
      let val (s, s') = TYPE_name in
        Symtab.map_default (s, [])
            (insert_type thy #3
                         (s', [tvar_a], @{typ "'a itself"}, false, 0, false))
      end
  in
    Symtab.empty
    |> is_type_enc_sound type_enc
       ? (fold (fold add_fact_syms) [conjs, facts]
          #> fold add_iterm_syms extra_tms
          #> (case type_enc of
                Native (First_Order, Raw_Polymorphic phantoms, _) =>
                phantoms = Without_Phantom_Type_Vars ? add_TYPE_const ()
              | Native _ => I
              | _ => fold add_undefined_const (var_types ())))
  end

(* We add "bool" in case the helper "True_or_False" is included later. *)
fun default_mono level completish =
  {maybe_finite_Ts = [@{typ bool}],
   surely_infinite_Ts =
     case level of
       Nonmono_Types (Strict, _) => []
     | _ => known_infinite_types,
   maybe_nonmono_Ts = [if completish then tvar_a else @{typ bool}]}

(* This inference is described in section 2.3 of Claessen et al.'s "Sorting it
   out with monotonicity" paper presented at CADE 2011. *)
fun add_iterm_mononotonicity_info _ _ (SOME false) _ mono = mono
  | add_iterm_mononotonicity_info ctxt level _
        (IApp (IApp (IConst ((s, _), Type (_, [T, _]), _), tm1), tm2))
        (mono as {maybe_finite_Ts, surely_infinite_Ts, maybe_nonmono_Ts}) =
    let val thy = Proof_Context.theory_of ctxt in
      if is_tptp_equal s andalso exists is_maybe_universal_var [tm1, tm2] then
        case level of
          Nonmono_Types (strictness, _) =>
          if exists (type_instance thy T) surely_infinite_Ts orelse
             member (type_equiv thy) maybe_finite_Ts T then
            mono
          else if is_type_kind_of_surely_infinite ctxt strictness
                                                  surely_infinite_Ts T then
            {maybe_finite_Ts = maybe_finite_Ts,
             surely_infinite_Ts = surely_infinite_Ts |> insert_type thy I T,
             maybe_nonmono_Ts = maybe_nonmono_Ts}
          else
            {maybe_finite_Ts = maybe_finite_Ts |> insert (type_equiv thy) T,
             surely_infinite_Ts = surely_infinite_Ts,
             maybe_nonmono_Ts = maybe_nonmono_Ts |> insert_type thy I T}
        | _ => mono
      else
        mono
    end
  | add_iterm_mononotonicity_info _ _ _ _ mono = mono
fun add_fact_mononotonicity_info ctxt level ({role, iformula, ...} : ifact) =
  formula_fold (SOME (role <> Conjecture))
               (add_iterm_mononotonicity_info ctxt level) iformula
fun mononotonicity_info_for_facts ctxt type_enc completish facts =
  let val level = level_of_type_enc type_enc in
    default_mono level completish
    |> is_type_level_monotonicity_based level
       ? fold (add_fact_mononotonicity_info ctxt level) facts
  end

fun add_iformula_monotonic_types ctxt mono type_enc =
  let
    val thy = Proof_Context.theory_of ctxt
    val level = level_of_type_enc type_enc
    val should_encode = should_encode_type ctxt mono level
    fun add_type T = not (should_encode T) ? insert_type thy I T
    fun add_args (IApp (tm1, tm2)) = add_args tm1 #> add_term tm2
      | add_args _ = I
    and add_term tm = add_type (ityp_of tm) #> add_args tm
  in formula_fold NONE (K add_term) end
fun add_fact_monotonic_types ctxt mono type_enc =
  add_iformula_monotonic_types ctxt mono type_enc |> ifact_lift
fun monotonic_types_for_facts ctxt mono type_enc facts =
  let val level = level_of_type_enc type_enc in
    [] |> (is_type_enc_polymorphic type_enc andalso
           is_type_level_monotonicity_based level)
          ? fold (add_fact_monotonic_types ctxt mono type_enc) facts
  end

fun line_for_guards_mono_type ctxt mono type_enc T =
  Formula (guards_sym_formula_prefix ^
           ascii_of (mangled_type type_enc T),
           Axiom,
           IConst (`make_bound_var "X", T, [])
           |> type_guard_iterm type_enc T
           |> AAtom
           |> formula_from_iformula ctxt mono type_enc
                                    always_guard_var_in_formula (SOME true)
           |> close_formula_universally
           |> bound_tvars type_enc true (atomic_types_of T),
           NONE, isabelle_info inductiveN helper_rank)

fun line_for_tags_mono_type ctxt mono type_enc T =
  let val x_var = ATerm ((`make_bound_var "X", []), []) in
    Formula (tags_sym_formula_prefix ^
             ascii_of (mangled_type type_enc T),
             Axiom,
             eq_formula type_enc (atomic_types_of T) [] false
                  (tag_with_type ctxt mono type_enc NONE T x_var) x_var,
             NONE, isabelle_info defN helper_rank)
  end

fun lines_for_mono_types ctxt mono type_enc Ts =
  case type_enc of
    Native _ => []
  | Guards _ => map (line_for_guards_mono_type ctxt mono type_enc) Ts
  | Tags _ => map (line_for_tags_mono_type ctxt mono type_enc) Ts

fun decl_line_for_sym ctxt mono type_enc s
                      (s', T_args, T, pred_sym, ary, _) =
  let
    val thy = Proof_Context.theory_of ctxt
    val (T, T_args) =
      if null T_args then
        (T, [])
      else case unprefix_and_unascii const_prefix s of
        SOME s' =>
        let
          val s' = s' |> invert_const
          val T = s' |> robust_const_type thy
        in (T, robust_const_typargs thy (s', T)) end
      | NONE => raise Fail "unexpected type arguments"
  in
    Sym_Decl (sym_decl_prefix ^ s, (s, s'),
              T |> fused_type ctxt mono (level_of_type_enc type_enc) ary
                |> native_ho_type_from_typ type_enc pred_sym ary
                |> not (null T_args)
                   ? curry APi (map (tvar_name o dest_TVar) T_args))
  end

fun honor_conj_sym_role in_conj =
  if in_conj then (Hypothesis, I) else (Axiom, I)

fun line_for_guards_sym_decl ctxt mono type_enc n s j
                             (s', T_args, T, _, ary, in_conj) =
  let
    val thy = Proof_Context.theory_of ctxt
    val (role, maybe_negate) = honor_conj_sym_role in_conj
    val (arg_Ts, res_T) = chop_fun ary T
    val bound_names = 1 upto ary |> map (`I o make_bound_var o string_of_int)
    val bounds =
      bound_names ~~ arg_Ts |> map (fn (name, T) => IConst (name, T, []))
    val bound_Ts =
      if exists (curry (op =) dummyT) T_args then
        let val cover = type_arg_cover thy NONE true s ary in
          map2 (fn j => if member (op =) cover j then SOME else K NONE)
               (0 upto ary - 1) arg_Ts
        end
      else
        replicate ary NONE
  in
    Formula (guards_sym_formula_prefix ^ s ^
             (if n > 1 then "_" ^ string_of_int j else ""), role,
             IConst ((s, s'), T, T_args)
             |> fold (curry (IApp o swap)) bounds
             |> type_guard_iterm type_enc res_T
             |> AAtom |> mk_aquant AForall (bound_names ~~ bound_Ts)
             |> formula_from_iformula ctxt mono type_enc
                                      always_guard_var_in_formula (SOME true)
             |> close_formula_universally
             |> bound_tvars type_enc (n > 1) (atomic_types_of T)
             |> maybe_negate,
             NONE, isabelle_info inductiveN helper_rank)
  end

fun lines_for_tags_sym_decl ctxt mono type_enc n s
                            (j, (s', T_args, T, pred_sym, ary, in_conj)) =
  let
    val thy = Proof_Context.theory_of ctxt
    val level = level_of_type_enc type_enc
    val ident =
      tags_sym_formula_prefix ^ s ^
      (if n > 1 then "_" ^ string_of_int j else "")
    val (role, maybe_negate) = honor_conj_sym_role in_conj
    val (arg_Ts, res_T) = chop_fun ary T
    val bound_names = 1 upto ary |> map (`I o make_bound_var o string_of_int)
    val bounds = bound_names |> map (fn name => ATerm ((name, []), []))
    val cst = mk_aterm type_enc (s, s') T_args
    val eq = maybe_negate oo eq_formula type_enc (atomic_types_of T) [] pred_sym
    val should_encode = should_encode_type ctxt mono level
    val tag_with = tag_with_type ctxt mono type_enc NONE
    val add_formula_for_res =
      if should_encode res_T then
        let
          val (lhs, rhs) =
            if level = Undercover_Types then
              let
                val lhs_cover = type_arg_cover thy NONE false s ary
                val rhs_cover = type_arg_cover thy NONE true s ary
                fun maybe_tag cover (j, arg_T) =
                  member (op =) cover j ? tag_with arg_T
                fun covered_bounds cover =
                  map2 (maybe_tag cover) (0 upto ary - 1 ~~ arg_Ts) bounds
              in (lhs_cover, rhs_cover) |> pairself (covered_bounds #> cst) end
            else
              `I (cst bounds)
        in
          cons (Formula (ident, role, eq (tag_with res_T lhs) rhs,
                         NONE, isabelle_info defN helper_rank))
        end
      else
        I
  in [] |> not pred_sym ? add_formula_for_res end

fun result_type_of_decl (_, _, T, _, ary, _) = chop_fun ary T |> snd

fun rationalize_decls thy (decls as decl :: (decls' as _ :: _)) =
    let
      val T = result_type_of_decl decl
              |> map_type_tvar (fn (z, _) => TVar (z, HOLogic.typeS))
    in
      if forall (type_generalization thy T o result_type_of_decl) decls' then
        [decl]
      else
        decls
    end
  | rationalize_decls _ decls = decls

fun lines_for_sym_decls ctxt mono type_enc (s, decls) =
  case type_enc of
    Native _ => [decl_line_for_sym ctxt mono type_enc s (hd decls)]
  | Guards (_, level) =>
    let
      val thy = Proof_Context.theory_of ctxt
      val decls = decls |> rationalize_decls thy
      val n = length decls
      val decls =
        decls |> filter (should_encode_type ctxt mono level
                         o result_type_of_decl)
    in
      (0 upto length decls - 1, decls)
      |-> map2 (line_for_guards_sym_decl ctxt mono type_enc n s)
    end
  | Tags (_, level) =>
    if is_type_level_uniform level then
      []
    else
      let val n = length decls in
        (0 upto n - 1 ~~ decls)
        |> maps (lines_for_tags_sym_decl ctxt mono type_enc n s)
      end

fun lines_for_sym_decl_table ctxt mono type_enc mono_Ts sym_decl_tab =
  let
    val syms = sym_decl_tab |> Symtab.dest |> sort_wrt fst
    val mono_lines = lines_for_mono_types ctxt mono type_enc mono_Ts
    val decl_lines =
      fold_rev (append o lines_for_sym_decls ctxt mono type_enc) syms []
  in mono_lines @ decl_lines end

fun pair_append (xs1, xs2) (ys1, ys2) = (xs1 @ ys1, xs2 @ ys2)

fun do_uncurried_alias_lines_for_sym ctxt constrs mono type_enc sym_tab0 sym_tab
                                     base_s0 types in_conj =
  let
    fun do_alias ary =
      let
        val thy = Proof_Context.theory_of ctxt
        val (role, maybe_negate) = honor_conj_sym_role in_conj
        val base_name = base_s0 |> `(make_fixed_const (SOME type_enc))
        val T = case types of [T] => T | _ => robust_const_type thy base_s0
        val T_args = robust_const_typargs thy (base_s0, T)
        val (base_name as (base_s, _), T_args) =
          mangle_type_args_in_const type_enc base_name T_args
        val base_ary = min_ary_of sym_tab0 base_s
        fun do_const name = IConst (name, T, T_args)
        val filter_ty_args = filter_type_args_in_iterm thy constrs type_enc
        val ho_term_of = ho_term_from_iterm ctxt mono type_enc (SOME true)
        val name1 as (s1, _) =
          base_name |> ary - 1 > base_ary ? aliased_uncurried (ary - 1)
        val name2 as (s2, _) = base_name |> aliased_uncurried ary
        val (arg_Ts, _) = chop_fun ary T
        val bound_names =
          1 upto ary |> map (`I o make_bound_var o string_of_int)
        val bounds = bound_names ~~ arg_Ts
        val (first_bounds, last_bound) =
          bounds |> map (fn (name, T) => IConst (name, T, [])) |> split_last
        val tm1 =
          mk_app_op type_enc (list_app (do_const name1) first_bounds) last_bound
          |> filter_ty_args
        val tm2 =
          list_app (do_const name2) (first_bounds @ [last_bound])
          |> filter_ty_args
        val do_bound_type = do_bound_type ctxt mono type_enc
        val eq =
          eq_formula type_enc (atomic_types_of T)
                     (map (apsnd do_bound_type) bounds) false
                     (ho_term_of tm1) (ho_term_of tm2)
      in
        ([tm1, tm2],
         [Formula (uncurried_alias_eq_prefix ^ s2, role, eq |> maybe_negate,
                   NONE, isabelle_info defN helper_rank)])
        |> (if ary - 1 = base_ary orelse Symtab.defined sym_tab s1 then I
            else pair_append (do_alias (ary - 1)))
      end
  in do_alias end
fun uncurried_alias_lines_for_sym ctxt constrs mono type_enc sym_tab0
        sym_tab (s, {min_ary, types, in_conj, ...} : sym_info) =
  case unprefix_and_unascii const_prefix s of
    SOME mangled_s =>
    if String.isSubstring uncurried_alias_sep mangled_s then
      let
        val base_s0 = mangled_s |> unmangled_const_name |> hd |> invert_const
      in
        do_uncurried_alias_lines_for_sym ctxt constrs mono type_enc sym_tab0
                                         sym_tab base_s0 types in_conj min_ary
      end
    else
      ([], [])
  | NONE => ([], [])
fun uncurried_alias_lines_for_sym_table ctxt constrs mono type_enc
                                        uncurried_aliases sym_tab0 sym_tab =
  ([], [])
  |> uncurried_aliases
     ? Symtab.fold_rev
           (pair_append
            o uncurried_alias_lines_for_sym ctxt constrs mono type_enc sym_tab0
                                            sym_tab) sym_tab

val implicit_declsN = "Should-be-implicit typings"
val explicit_declsN = "Explicit typings"
val uncurried_alias_eqsN = "Uncurried aliases"
val factsN = "Relevant facts"
val subclassesN = "Subclasses"
val tconsN = "Type constructors"
val helpersN = "Helper facts"
val conjsN = "Conjectures"
val free_typesN = "Free types"

(* TFF allows implicit declarations of types, function symbols, and predicate
   symbols (with "$i" as the type of individuals), but some provers (e.g.,
   SNARK) require explicit declarations. The situation is similar for THF. *)

fun default_type pred_sym =
  let
    fun typ 0 0 = if pred_sym then bool_atype else individual_atype
      | typ 0 tm_ary = AFun (individual_atype, typ 0 (tm_ary - 1))
      | typ ty_ary tm_ary = APi (replicate ty_ary tvar_a_name, typ 0 tm_ary)
  in typ end

fun undeclared_in_problem problem =
  let
    fun do_sym (name as (s, _)) value =
      if is_tptp_user_symbol s then Symtab.default (s, (name, value)) else I
    fun do_class name = apfst (apfst (do_sym name ()))
    fun do_type (AType (name, tys)) =
        apfst (apsnd (do_sym name (length tys))) #> fold do_type tys
      | do_type (AFun (ty1, ty2)) = do_type ty1 #> do_type ty2
      | do_type (APi (_, ty)) = do_type ty
    fun do_term pred_sym (ATerm ((name, tys), tms)) =
        apsnd (do_sym name
                   (fn _ => default_type pred_sym (length tys) (length tms)))
        #> fold do_type tys #> fold (do_term false) tms
      | do_term _ (AAbs (((_, ty), tm), args)) =
        do_type ty #> do_term false tm #> fold (do_term false) args
    fun do_formula (ATyQuant (_, xs, phi)) =
        fold (do_type o fst) xs #> fold (fold do_class o snd) xs
        #> do_formula phi
      | do_formula (AQuant (_, xs, phi)) =
        fold do_type (map_filter snd xs) #> do_formula phi
      | do_formula (AConn (_, phis)) = fold do_formula phis
      | do_formula (AAtom tm) = do_term true tm
    fun do_line (Class_Decl (_, _, cls)) = fold do_class cls
      | do_line (Type_Decl _) = I
      | do_line (Sym_Decl (_, _, ty)) = do_type ty
      | do_line (Class_Memb (_, xs, ty, cl)) =
        fold (fold do_class o snd) xs #> do_type ty #> do_class cl
      | do_line (Formula (_, _, phi, _, _)) = do_formula phi
    val ((cls, tys), syms) = declared_in_atp_problem problem
  in
    ((Symtab.empty, Symtab.empty), Symtab.empty)
    |>> apfst (fold (fn (s, _) => Symtab.default (s, (("", ""), ()))) cls)
    |>> apsnd (fold (fn (s, _) => Symtab.default (s, (("", ""), 0))) tys)
    ||> fold (fn (s, _) => Symtab.default (s, (("", ""), K tvar_a_atype))) syms
    |> fold (fold do_line o snd) problem
  end

fun declare_undeclared_in_problem heading problem =
  let
    val ((cls, tys), syms) = undeclared_in_problem problem
    val decls =
      Symtab.fold (fn (_, (("", ""), _)) => I (* already declared *)
                    | (s, (cls, ())) =>
                      cons (Class_Decl (class_decl_prefix ^ s, cls, [])))
                  cls [] @
      Symtab.fold (fn (_, (("", ""), _)) => I (* already declared *)
                    | (s, (ty, ary)) =>
                      cons (Type_Decl (type_decl_prefix ^ s, ty, ary)))
                  tys [] @
      Symtab.fold (fn (_, (("", ""), _)) => I (* already declared *)
                    | (s, (sym, ty)) =>
                      cons (Sym_Decl (sym_decl_prefix ^ s, sym, ty ())))
                  syms []
  in (heading, decls) :: problem end

fun is_poly_constr (Datatype.DtTFree _) = true
  | is_poly_constr (Datatype.DtType (_, Us)) = exists is_poly_constr Us
  | is_poly_constr _ = false

fun all_constrs_of_polymorphic_datatypes thy =
  Symtab.fold (snd #> #descr #> maps (#3 o snd)
               #> (fn cs => exists (exists is_poly_constr o snd) cs
                            ? append (map fst cs)))
               (Datatype.get_all thy) []

val app_op_and_predicator_threshold = 50

fun prepare_atp_problem ctxt format prem_role type_enc mode lam_trans
                        uncurried_aliases readable_names preproc hyp_ts concl_t
                        facts =
  let
    val thy = Proof_Context.theory_of ctxt
    val type_enc = type_enc |> adjust_type_enc format
    (* Forcing explicit applications is expensive for polymorphic encodings,
       because it takes only one existential variable ranging over "'a => 'b" to
       ruin everything. Hence we do it only if there are few facts (which is
       normally the case for "metis" and the minimizer). *)
    val app_op_level =
      if mode = Sledgehammer_Completish then
        Full_App_Op_And_Predicator
      else if length facts + length hyp_ts
              > app_op_and_predicator_threshold then
        if is_type_enc_polymorphic type_enc then Min_App_Op
        else Sufficient_App_Op
      else
        Sufficient_App_Op_And_Predicator
    val exporter = (mode = Exporter)
    val completish = (mode = Sledgehammer_Completish)
    val lam_trans =
      if lam_trans = keep_lamsN andalso
         not (is_type_enc_higher_order type_enc) then
        liftingN
      else
        lam_trans
    val (fact_names, classes, conjs, facts, subclass_pairs, tcon_clauses,
         lifted) =
      translate_formulas ctxt prem_role format type_enc lam_trans preproc hyp_ts
                         concl_t facts
    val (_, sym_tab0) =
      sym_table_for_facts ctxt type_enc app_op_level conjs facts
    val mono =
      conjs @ facts |> mononotonicity_info_for_facts ctxt type_enc completish
    val constrs = all_constrs_of_polymorphic_datatypes thy
    fun firstorderize in_helper =
      firstorderize_fact thy constrs type_enc sym_tab0
          (uncurried_aliases andalso not in_helper) completish
    val (conjs, facts) = (conjs, facts) |> pairself (map (firstorderize false))
    val (ho_stuff, sym_tab) =
      sym_table_for_facts ctxt type_enc Min_App_Op conjs facts
    val (uncurried_alias_eq_tms, uncurried_alias_eq_lines) =
      uncurried_alias_lines_for_sym_table ctxt constrs mono type_enc
                                          uncurried_aliases sym_tab0 sym_tab
    val (_, sym_tab) =
      (ho_stuff, sym_tab)
      |> fold (add_iterm_syms_to_sym_table ctxt Min_App_Op false false)
              uncurried_alias_eq_tms
    val helpers =
      sym_tab |> helper_facts_for_sym_table ctxt format type_enc completish
              |> map (firstorderize true)
    val mono_Ts =
      helpers @ conjs @ facts |> monotonic_types_for_facts ctxt mono type_enc
    val class_decl_lines = decl_lines_for_classes type_enc classes
    val sym_decl_lines =
      (conjs, helpers @ facts, uncurried_alias_eq_tms)
      |> sym_decl_table_for_facts thy type_enc sym_tab
      |> lines_for_sym_decl_table ctxt mono type_enc mono_Ts
    val num_facts = length facts
    val fact_lines =
      map (line_for_fact ctxt fact_prefix ascii_of (not exporter)
               (not exporter) mono type_enc (rank_of_fact_num num_facts))
          (0 upto num_facts - 1 ~~ facts)
    val subclass_lines = maps (lines_for_subclass_pair type_enc) subclass_pairs
    val tcon_lines = map (line_for_tcon_clause type_enc) tcon_clauses
    val helper_lines =
      0 upto length helpers - 1 ~~ helpers
      |> map (line_for_fact ctxt helper_prefix I false true mono type_enc
                            (K default_rank))
    val free_type_lines = lines_for_free_types type_enc (facts @ conjs)
    val conj_lines = map (line_for_conjecture ctxt mono type_enc) conjs
    (* Reordering these might confuse the proof reconstruction code. *)
    val problem =
      [(explicit_declsN, class_decl_lines @ sym_decl_lines),
       (uncurried_alias_eqsN, uncurried_alias_eq_lines),
       (factsN, fact_lines),
       (subclassesN, subclass_lines),
       (tconsN, tcon_lines),
       (helpersN, helper_lines),
       (free_typesN, free_type_lines),
       (conjsN, conj_lines)]
    val problem =
      problem |> (case format of
                    CNF => ensure_cnf_problem
                  | CNF_UEQ => filter_cnf_ueq_problem
                  | FOF => I
                  | TFF (_, TPTP_Implicit) => I
                  | THF (_, TPTP_Implicit, _, _) => I
                  | _ => declare_undeclared_in_problem implicit_declsN)
    val (problem, pool) = problem |> nice_atp_problem readable_names format
    fun add_sym_ary (s, {min_ary, ...} : sym_info) =
      min_ary > 0 ? Symtab.insert (op =) (s, min_ary)
  in
    (problem, pool |> Option.map snd |> the_default Symtab.empty,
     fact_names |> Vector.fromList, lifted,
     Symtab.empty |> Symtab.fold add_sym_ary sym_tab)
  end

(* FUDGE *)
val conj_weight = 0.0
val hyp_weight = 0.1
val fact_min_weight = 0.2
val fact_max_weight = 1.0
val type_info_default_weight = 0.8

(* Weights are from 0.0 (most important) to 1.0 (least important). *)
fun atp_problem_selection_weights problem =
  let
    fun add_term_weights weight (ATerm ((s, _), tms)) =
        is_tptp_user_symbol s ? Symtab.default (s, weight)
        #> fold (add_term_weights weight) tms
      | add_term_weights weight (AAbs ((_, tm), args)) =
        add_term_weights weight tm #> fold (add_term_weights weight) args
    fun add_line_weights weight (Formula (_, _, phi, _, _)) =
        formula_fold NONE (K (add_term_weights weight)) phi
      | add_line_weights _ _ = I
    fun add_conjectures_weights [] = I
      | add_conjectures_weights conjs =
        let val (hyps, conj) = split_last conjs in
          add_line_weights conj_weight conj
          #> fold (add_line_weights hyp_weight) hyps
        end
    fun add_facts_weights facts =
      let
        val num_facts = length facts
        fun weight_of j =
          fact_min_weight + (fact_max_weight - fact_min_weight) * Real.fromInt j
                            / Real.fromInt num_facts
      in
        map weight_of (0 upto num_facts - 1) ~~ facts
        |> fold (uncurry add_line_weights)
      end
    val get = these o AList.lookup (op =) problem
  in
    Symtab.empty
    |> add_conjectures_weights (get free_typesN @ get conjsN)
    |> add_facts_weights (get factsN)
    |> fold (fold (add_line_weights type_info_default_weight) o get)
            [explicit_declsN, subclassesN, tconsN]
    |> Symtab.dest
    |> sort (prod_ord Real.compare string_ord o pairself swap)
  end

(* Ugly hack: may make innocent victims (collateral damage) *)
fun may_be_app s args = String.isPrefix app_op_name s andalso length args = 2
fun may_be_predicator s =
  member (op =) [predicator_name, prefixed_predicator_name] s

fun strip_predicator (tm as ATerm ((s, _), [tm'])) =
    if may_be_predicator s then tm' else tm
  | strip_predicator tm = tm

fun make_head_roll (ATerm ((s, _), tms)) =
    if may_be_app s tms then make_head_roll (hd tms) ||> append (tl tms)
    else (s, tms)
  | make_head_roll _ = ("", [])

fun strip_up_to_predicator (ATyQuant (_, _, phi)) = strip_up_to_predicator phi
  | strip_up_to_predicator (AQuant (_, _, phi)) = strip_up_to_predicator phi
  | strip_up_to_predicator (AConn (_, phis)) = maps strip_up_to_predicator phis
  | strip_up_to_predicator (AAtom tm) = [strip_predicator tm]

fun strip_ahorn_etc (ATyQuant (_, _, phi)) = strip_ahorn_etc phi
  | strip_ahorn_etc (AQuant (_, _, phi)) = strip_ahorn_etc phi
  | strip_ahorn_etc (AConn (AImplies, [phi1, phi2])) =
    strip_ahorn_etc phi2 |>> append (strip_up_to_predicator phi1)
  | strip_ahorn_etc phi = ([], hd (strip_up_to_predicator phi))

fun strip_iff_etc (ATyQuant (_, _, phi)) = strip_iff_etc phi
  | strip_iff_etc (AQuant (_, _, phi)) = strip_iff_etc phi
  | strip_iff_etc (AConn (AIff, [phi1, phi2])) =
    pairself strip_up_to_predicator (phi1, phi2)
  | strip_iff_etc _ = ([], [])

val max_term_order_weight = 2147483647

fun atp_problem_term_order_info problem =
  let
    fun add_edge s s' =
      Graph.default_node (s, ())
      #> Graph.default_node (s', ())
      #> Graph.add_edge_acyclic (s, s')
    fun add_term_deps head (ATerm ((s, _), args)) =
        if is_tptp_user_symbol head then
          (if is_tptp_user_symbol s then perhaps (try (add_edge s head)) else I)
          #> fold (add_term_deps head) args
        else
          I
      | add_term_deps head (AAbs ((_, tm), args)) =
        add_term_deps head tm #> fold (add_term_deps head) args
    fun add_intro_deps pred (Formula (_, role, phi, _, info)) =
        if pred (role, info) then
          let val (hyps, concl) = strip_ahorn_etc phi in
            case make_head_roll concl of
              (head, args as _ :: _) => fold (add_term_deps head) (hyps @ args)
            | _ => I
          end
        else
          I
      | add_intro_deps _ _ = I
    fun add_atom_eq_deps (SOME true) (ATerm ((s, _), [lhs as _, rhs])) =
        if is_tptp_equal s then
          case make_head_roll lhs of
            (head, args as _ :: _) => fold (add_term_deps head) (rhs :: args)
          | _ => I
        else
          I
      | add_atom_eq_deps _ _ = I
    fun add_eq_deps pred (Formula (_, role, phi, _, info)) =
        if pred (role, info) then
          case strip_iff_etc phi of
            ([lhs], rhs) =>
            (case make_head_roll lhs of
               (head, args as _ :: _) => fold (add_term_deps head) (rhs @ args)
             | _ => I)
          | _ => formula_fold (SOME (role <> Conjecture)) add_atom_eq_deps phi
        else
          I
      | add_eq_deps _ _ = I
    fun has_status status (_, info) = extract_isabelle_status info = SOME status
    fun is_conj (role, _) = (role = Conjecture orelse role = Hypothesis)
    val graph =
      Graph.empty
      |> fold (fold (add_eq_deps (has_status defN)) o snd) problem
      |> fold (fold (add_eq_deps (has_status simpN orf is_conj)) o snd) problem
      |> fold (fold (add_intro_deps (has_status inductiveN)) o snd) problem
      |> fold (fold (add_intro_deps (has_status introN)) o snd) problem
    fun next_weight w = if w + w <= max_term_order_weight then w + w else w + 1
    fun add_weights _ [] = I
      | add_weights weight syms =
        fold (AList.update (op =) o rpair weight) syms
        #> add_weights (next_weight weight)
               (fold (union (op =) o Graph.immediate_succs graph) syms [])
  in
    (* Sorting is not just for aesthetics: It specifies the precedence order
       for the term ordering (KBO or LPO), from smaller to larger values. *)
    [] |> add_weights 1 (Graph.minimals graph) |> sort (int_ord o pairself snd)
  end

end;

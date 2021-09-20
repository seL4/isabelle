(*  Title:      HOL/Tools/ATP/atp_problem_generate.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Martin Desharnais, UniBw Muenchen

Translation of HOL to FOL for Metis and Sledgehammer.
*)

signature ATP_PROBLEM_GENERATE =
sig
  type ('a, 'b) atp_term = ('a, 'b) ATP_Problem.atp_term
  type atp_connective = ATP_Problem.atp_connective
  type ('a, 'b, 'c, 'd) atp_formula = ('a, 'b, 'c, 'd) ATP_Problem.atp_formula
  type atp_format = ATP_Problem.atp_format
  type atp_formula_role = ATP_Problem.atp_formula_role
  type 'a atp_problem = 'a ATP_Problem.atp_problem

  datatype mode = Metis | Sledgehammer | Sledgehammer_Completish of int | Exporter | Translator

  datatype scope = Global | Local | Assum | Chained
  datatype status = General | Induction | Intro | Inductive | Elim | Simp | Non_Rec_Def | Rec_Def

  type stature = scope * status

  datatype strictness = Strict | Non_Strict
  datatype uniformity = Uniform | Non_Uniform
  datatype ctr_optim = With_Ctr_Optim | Without_Ctr_Optim
  datatype type_level =
    All_Types |
    Undercover_Types |
    Nonmono_Types of strictness * uniformity |
    Const_Types of ctr_optim |
    No_Types
  type type_enc

  val no_lamsN : string
  val opaque_liftingN : string
  val liftingN : string
  val opaque_combsN : string
  val combsN : string
  val combs_and_liftingN : string
  val combs_or_liftingN : string
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
  val datatype_decl_prefix : string
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
  val new_skolem_var_name_of_const : string -> string
  val atp_logical_consts : string list
  val atp_irrelevant_consts : string list
  val atp_widely_irrelevant_consts : string list
  val is_irrelevant_const : string -> bool
  val is_widely_irrelevant_const : string -> bool
  val atp_schematic_consts_of : term -> typ list Symtab.table
  val is_type_enc_higher_order : type_enc -> bool
  val is_type_enc_polymorphic : type_enc -> bool
  val level_of_type_enc : type_enc -> type_level
  val is_type_enc_sound : type_enc -> bool
  val type_enc_of_string : strictness -> string -> type_enc
  val adjust_type_enc : atp_format -> type_enc -> type_enc
  val is_first_order_lambda_free : term -> bool
  val do_cheaply_conceal_lambdas : typ list -> term -> term
  val mk_aconns :
    atp_connective -> ('a, 'b, 'c, 'd) atp_formula list
    -> ('a, 'b, 'c, 'd) atp_formula
  val unmangled_type : string -> (string, 'a) ATP_Problem.atp_term
  val unmangled_const : string -> string * (string, 'b) atp_term list
  val unmangled_const_name : string -> string list
  val helper_table : bool -> ((string * bool) * (status * thm) list) list
  val trans_lams_of_string :
    Proof.context -> type_enc -> string -> term list -> term list * term list
  val string_of_status : status -> string
  val factsN : string
  val generate_atp_problem : Proof.context -> bool -> atp_format -> atp_formula_role -> type_enc ->
    mode -> string -> bool -> bool -> bool -> term list -> term ->
    ((string * stature) * term) list -> string atp_problem * string Symtab.table
    * (string * term) list * int Symtab.table
  val atp_problem_selection_weights : string atp_problem -> (string * real) list
  val atp_problem_term_order_info : string atp_problem -> (string * int) list
end;

structure ATP_Problem_Generate : ATP_PROBLEM_GENERATE =
struct

open ATP_Util
open ATP_Problem

datatype mode = Metis | Sledgehammer | Sledgehammer_Completish of int | Exporter | Translator

datatype scope = Global | Local | Assum | Chained
datatype status = General | Induction | Intro | Inductive | Elim | Simp | Non_Rec_Def | Rec_Def

type stature = scope * status

datatype order =
  First_Order |
  Higher_Order of thf_flavor
datatype phantom_policy = Without_Phantom_Type_Vars | With_Phantom_Type_Vars
datatype polymorphism =
  Type_Class_Polymorphic |
  Raw_Polymorphic of phantom_policy |
  Raw_Monomorphic |
  Mangled_Monomorphic
datatype strictness = Strict | Non_Strict
datatype uniformity = Uniform | Non_Uniform
datatype ctr_optim = With_Ctr_Optim | Without_Ctr_Optim
datatype type_level =
  All_Types |
  Undercover_Types |
  Nonmono_Types of strictness * uniformity |
  Const_Types of ctr_optim |
  No_Types

datatype type_enc =
  Native of order * fool * polymorphism * type_level |
  Guards of polymorphism * type_level |
  Tags of polymorphism * type_level

(* not clear whether ATPs prefer to have their negative variables tagged *)
val tag_neg_vars = false

fun is_type_enc_native (Native _) = true
  | is_type_enc_native _ = false
fun is_type_enc_full_higher_order (Native (Higher_Order THF_Lambda_Free, _, _, _)) = false
  | is_type_enc_full_higher_order (Native (Higher_Order _, _, _, _)) = true
  | is_type_enc_full_higher_order _ = false
fun is_type_enc_fool (Native (_, With_FOOL, _, _)) = true
  | is_type_enc_fool _ = false
fun is_type_enc_higher_order (Native (Higher_Order _, _, _, _)) = true
  | is_type_enc_higher_order _ = false

fun polymorphism_of_type_enc (Native (_, _, poly, _)) = poly
  | polymorphism_of_type_enc (Guards (poly, _)) = poly
  | polymorphism_of_type_enc (Tags (poly, _)) = poly

fun is_type_enc_polymorphic type_enc =
  (case polymorphism_of_type_enc type_enc of
    Raw_Polymorphic _ => true
  | Type_Class_Polymorphic => true
  | _ => false)

fun is_type_enc_mangling type_enc =
  polymorphism_of_type_enc type_enc = Mangled_Monomorphic

fun level_of_type_enc (Native (_, _,  _, level)) = level
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
val opaque_liftingN = "opaque_lifting"
val liftingN = "lifting"
val opaque_combsN = "opaque_combs"
val combsN = "combs"
val combs_and_liftingN = "combs_and_lifting"
val combs_or_liftingN = "combs_or_lifting"
val keep_lamsN = "keep_lams"

(* The capitalization of the TPTP output respects the capitalzation of the prefix. *)
val bound_var_prefix = "B_"
val let_bound_var_prefix = "l_"
val all_bound_var_prefix = "A_"
val exist_bound_var_prefix = "E_"
val schematic_var_prefix = "V_"
val fixed_var_prefix = "v_"
val tvar_prefix = "T_"
val tfree_prefix = "tf_"
val const_prefix = "c_"
val type_const_prefix = "t_"
val native_type_prefix = "n_"
val class_prefix = "cl_"

(* Freshness almost guaranteed! *)
val atp_prefix = "ATP" ^ Long_Name.separator
val atp_weak_prefix = "ATP:"
val atp_weak_suffix = ":ATP"

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
val datatype_decl_prefix = "dt_"
val class_memb_prefix = "cm_"
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
  The character _ goes to __.
  Characters in the range ASCII space to / go to _A to _P, respectively.
  Other characters go to _nnn where nnn is the decimal ASCII code. *)
val upper_a_minus_space = Char.ord #"A" - Char.ord #" "

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
            (case Int.fromString (String.implode digits) of
              SOME n => un (Char.chr n :: rcs) (List.drop (cs, 2))
            | NONE => un (c :: #"_" :: rcs) cs (* ERROR *))
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
  [("c_False", (\<^const_name>\<open>False\<close>, (@{thm fFalse_def}, ("fFalse", \<^const_name>\<open>fFalse\<close>)))),
   ("c_True", (\<^const_name>\<open>True\<close>, (@{thm fTrue_def}, ("fTrue", \<^const_name>\<open>fTrue\<close>)))),
   ("c_Not", (\<^const_name>\<open>Not\<close>, (@{thm fNot_def}, ("fNot", \<^const_name>\<open>fNot\<close>)))),
   ("c_conj", (\<^const_name>\<open>conj\<close>, (@{thm fconj_def}, ("fconj", \<^const_name>\<open>fconj\<close>)))),
   ("c_disj", (\<^const_name>\<open>disj\<close>, (@{thm fdisj_def}, ("fdisj", \<^const_name>\<open>fdisj\<close>)))),
   ("c_implies", (\<^const_name>\<open>implies\<close>, (@{thm fimplies_def}, ("fimplies", \<^const_name>\<open>fimplies\<close>)))),
   ("equal", (\<^const_name>\<open>HOL.eq\<close>, (@{thm fequal_def}, ("fequal", \<^const_name>\<open>fequal\<close>)))),
   ("c_All", (\<^const_name>\<open>All\<close>, (@{thm fAll_def}, ("fAll", \<^const_name>\<open>fAll\<close>)))),
   ("c_Ex", (\<^const_name>\<open>Ex\<close>, (@{thm fEx_def}, ("fEx", \<^const_name>\<open>fEx\<close>))))]

val proxify_const = AList.lookup (op =) proxy_table #> Option.map (snd o snd)

(* Readable names for the more common symbolic functions. Do not mess with the
   table unless you know what you are doing. *)
val const_trans_table =
  [(\<^const_name>\<open>False\<close>, "False"),
   (\<^const_name>\<open>True\<close>, "True"),
   (\<^const_name>\<open>Not\<close>, "Not"),
   (\<^const_name>\<open>conj\<close>, "conj"),
   (\<^const_name>\<open>disj\<close>, "disj"),
   (\<^const_name>\<open>implies\<close>, "implies"),
   (\<^const_name>\<open>HOL.eq\<close>, "equal"),
   (\<^const_name>\<open>All\<close>, "All"),
   (\<^const_name>\<open>Ex\<close>, "Ex"),
   (\<^const_name>\<open>If\<close>, "If"),
   (\<^const_name>\<open>Set.member\<close>, "member"),
   (\<^const_name>\<open>HOL.Let\<close>, "Let"),
   (\<^const_name>\<open>Meson.COMBI\<close>, combinator_prefix ^ "I"),
   (\<^const_name>\<open>Meson.COMBK\<close>, combinator_prefix ^ "K"),
   (\<^const_name>\<open>Meson.COMBB\<close>, combinator_prefix ^ "B"),
   (\<^const_name>\<open>Meson.COMBC\<close>, combinator_prefix ^ "C"),
   (\<^const_name>\<open>Meson.COMBS\<close>, combinator_prefix ^ "S")]
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
  (case Symtab.lookup const_trans_table c of
    SOME c' => c'
  | NONE => ascii_of c)

fun ascii_of_indexname (v, 0) = ascii_of v
  | ascii_of_indexname (v, i) = ascii_of v ^ "_" ^ string_of_int i

fun make_bound_var x = bound_var_prefix ^ ascii_of x
fun make_all_bound_var x = all_bound_var_prefix ^ ascii_of x
fun make_exist_bound_var x = exist_bound_var_prefix ^ ascii_of x
fun make_schematic_var v = schematic_var_prefix ^ ascii_of_indexname v
fun make_fixed_var x = fixed_var_prefix ^ ascii_of x

fun make_tvar (s, i) = tvar_prefix ^ ascii_of_indexname (unquote_tvar s, i)
fun make_tfree s = tfree_prefix ^ ascii_of (unquote_tvar s)
fun tvar_name ((x as (s, _)), _) = (make_tvar x, s)

(* "HOL.eq" and choice are mapped to the ATP's equivalents *)
local
  val choice_const = (fst o dest_Const o HOLogic.choice_const) dummyT
  fun default c = const_prefix ^ lookup_const c
in
  fun make_fixed_const _ \<^const_name>\<open>HOL.eq\<close> = tptp_old_equal
    | make_fixed_const (SOME (Native (Higher_Order THF_With_Choice, _, _, _))) c =
      if c = choice_const then tptp_choice else default c
    | make_fixed_const _ c = default c
end

fun make_fixed_type_const c = type_const_prefix ^ lookup_const c

fun make_class clas = class_prefix ^ ascii_of clas

fun new_skolem_var_name_of_const s =
  let val ss = Long_Name.explode s
  in nth ss (length ss - 2) end

(* These are ignored anyway by the relevance filter (unless they appear in
   higher-order places) but not by the monomorphizer. *)
val atp_logical_consts =
  [\<^const_name>\<open>Pure.prop\<close>, \<^const_name>\<open>Pure.conjunction\<close>,
   \<^const_name>\<open>Pure.all\<close>, \<^const_name>\<open>Pure.imp\<close>, \<^const_name>\<open>Pure.eq\<close>,
   \<^const_name>\<open>Trueprop\<close>, \<^const_name>\<open>All\<close>, \<^const_name>\<open>Ex\<close>,
   \<^const_name>\<open>Ex1\<close>, \<^const_name>\<open>Ball\<close>, \<^const_name>\<open>Bex\<close>]

(* These are either simplified away by "Meson.presimplify" (most of the time) or
   handled specially via "fFalse", "fTrue", ..., "fequal". *)
val atp_irrelevant_consts =
  [\<^const_name>\<open>False\<close>, \<^const_name>\<open>True\<close>, \<^const_name>\<open>Not\<close>, \<^const_name>\<open>conj\<close>,
   \<^const_name>\<open>disj\<close>, \<^const_name>\<open>implies\<close>, \<^const_name>\<open>HOL.eq\<close>, \<^const_name>\<open>If\<close>,
   \<^const_name>\<open>Let\<close>]

val atp_widely_irrelevant_consts = atp_logical_consts @ atp_irrelevant_consts

val atp_irrelevant_const_tab = Symtab.make (map (rpair ()) atp_irrelevant_consts)
val atp_widely_irrelevant_const_tab = Symtab.make (map (rpair ()) atp_widely_irrelevant_consts)

val is_irrelevant_const = Symtab.defined atp_irrelevant_const_tab
val is_widely_irrelevant_const = Symtab.defined atp_widely_irrelevant_const_tab

fun add_schematic_const (x as (_, T)) =
  Monomorph.typ_has_tvars T ? Symtab.insert_list (op =) x
val add_schematic_consts_of =
  Term.fold_aterms (fn Const (x as (s, _)) =>
                       not (member (op =) atp_widely_irrelevant_consts s)
                       ? add_schematic_const x
                      | _ => I)
fun atp_schematic_consts_of t = add_schematic_consts_of t Symtab.empty

val tvar_a_str = "'a"
val tvar_a_z = ((tvar_a_str, 0), \<^sort>\<open>type\<close>)
val tvar_a = TVar tvar_a_z
val tvar_a_name = tvar_name tvar_a_z
val itself_name = `make_fixed_type_const \<^type_name>\<open>itself\<close>
val TYPE_name = `(make_fixed_const NONE) \<^const_name>\<open>Pure.type\<close>
val tvar_a_atype = AType ((tvar_a_name, []), [])
val a_itself_atype = AType ((itself_name, []), [tvar_a_atype])

(** Definitions and functions for FOL clauses and formulas for TPTP **)

(** Type class membership **)

(* In our data structures, [] exceptionally refers to the top class, not to
   the empty class. *)

val class_of_types = the_single \<^sort>\<open>type\<close>

fun normalize_classes cls = if member (op =) cls class_of_types then [] else cls

(* Arity of type constructor "s :: (arg1, ..., argN) res" *)
fun make_axiom_tcon_clause (s, name, (cl, args)) =
  let
    val args = args |> map normalize_classes
    val tvars =
      1 upto length args |> map (fn j => TVar ((tvar_a_str, j), \<^sort>\<open>type\<close>))
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
fun all_class_pairs _ _ _ [] = ([], [])
  | all_class_pairs thy tycons old_cls cls =
    let
      val old_cls' = cls @ old_cls
      fun maybe_insert_class s = not (member (op =) old_cls' s) ? insert (op =) s

      val pairs = class_pairs thy tycons cls
      val new_cls = fold (fold (fold (fold maybe_insert_class) o snd) o snd) pairs []
      val (cls', pairs') = all_class_pairs thy tycons old_cls' new_cls
    in (cls' @ cls, union (op =) pairs' pairs) end

fun tcon_clause _ _ [] = []
  | tcon_clause seen n ((_, []) :: rest) = tcon_clause seen n rest
  | tcon_clause seen n ((tcons, (ar as (cl, _)) :: ars) :: rest) =
    if cl = class_of_types then
      tcon_clause seen n ((tcons, ars) :: rest)
    else if member (op =) seen cl then
      (* multiple clauses for the same (tycon, cl) pair *)
      make_axiom_tcon_clause (tcons,
        lookup_const tcons ^ "___" ^ ascii_of cl ^ "_" ^ string_of_int n, ar) ::
      tcon_clause seen (n + 1) ((tcons, ars) :: rest)
    else
      make_axiom_tcon_clause (tcons, lookup_const tcons ^ "___" ^ ascii_of cl, ar) ::
      tcon_clause (cl :: seen) n ((tcons, ars) :: rest)

fun make_tcon_clauses thy tycons =
  all_class_pairs thy tycons [] ##> tcon_clause [] 1


(** Isabelle class relations **)

(* Generate a list ("sub", "supers") such that "sub" is a proper subclass of all
   "supers". *)
fun make_subclass_pairs thy subs supers =
  let
    val class_less = curry (Sorts.class_less (Sign.classes_of thy))
    fun supers_of sub = (sub, filter (class_less sub) supers)
  in map supers_of subs |> filter_out (null o snd) end

(* intermediate terms *)
(* TODO: Merge IConst and IVar *)
datatype iterm =
  IConst of (string * string) * typ * typ list |
  IVar of (string * string) * typ |
  IApp of iterm * iterm |
  IAbs of ((string * string) * typ) * iterm

fun alpha_rename from to =
  let
    fun traverse (tm as IConst (name, T, Ts)) =
        if name = from then IConst (to, T, Ts) else tm
      | traverse (tm as IVar (name, T)) =
        if name = from then IVar (to, T) else tm
      | traverse (tm as IApp (tm1, tm2)) =
        let
          val tm1' = traverse tm1
          val tm2' = traverse tm2
        in
          if tm1 = tm1' andalso tm2 = tm2' then tm else IApp (tm1', tm2')
        end
      | traverse (tm as IAbs (binding as (name, _), tm1)) =
        if name = from then
          tm
        else
          let val tm1' = traverse tm1 in
            if tm1 = tm1' then tm else IAbs (binding, tm1')
          end
  in
    traverse
  end

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

val alpha_to_beta = Logic.varifyT_global \<^typ>\<open>'a => 'b\<close>
val alpha_to_beta_to_alpha_to_beta = alpha_to_beta --> alpha_to_beta

fun robust_const_type thy s =
  if s = app_op_name then
    alpha_to_beta_to_alpha_to_beta
  else if String.isPrefix lam_lifted_prefix s then
    alpha_to_beta
  else
    (* Old Skolems throw a "TYPE" exception here, which will be caught. *)
    s |> Sign.the_const_type thy

fun ary_of (Type (\<^type_name>\<open>fun\<close>, [_, T])) = 1 + ary_of T
  | ary_of _ = 0

(* This function only makes sense if "T" is as general as possible. *)
fun robust_const_type_args thy (s, T) =
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

(* Converts an Isabelle/HOL term (with combinators) into an intermediate term. Also accumulates sort
   infomation. *)
fun iterm_of_term thy type_enc =
  let
    fun iot true bs ((t0 as Const (\<^const_name>\<open>Let\<close>, _)) $ t1 $ (t2 as Abs (s, T, t'))) =
        let
          val (t0', t0_atomics_Ts) = iot true bs t0
          val (t1', t1_atomics_Ts) = iot true bs t1
          val (t2', t2_atomics_Ts) = iot true bs t2
        in
          (IApp (IApp (t0', t1'), t2'),
           fold (union (op =)) [t0_atomics_Ts, t1_atomics_Ts, t2_atomics_Ts] [])
        end
      | iot true bs ((t0 as Const (\<^const_name>\<open>Let\<close>, _)) $ t1 $ t2) =
        iot true bs (t0 $ t1 $ eta_expand (map (snd o snd) bs) t2 1)
      | iot fool bs (P $ Q) =
        let
          val (P', P_atomics_Ts) = iot fool bs P
          val (Q', Q_atomics_Ts) = iot fool bs Q
        in (IApp (P', Q'), union (op =) P_atomics_Ts Q_atomics_Ts) end
      | iot _ _ (Const (c, T)) =
        (IConst (`(make_fixed_const (SOME type_enc)) c, T, robust_const_type_args thy (c, T)),
         atomic_types_of T)
      | iot _ _ (Free (s, T)) = (IConst (`make_fixed_var s, T, []), atomic_types_of T)
      | iot _ _ (Var (v as (s, _), T)) =
        (if String.isPrefix Meson_Clausify.new_skolem_var_prefix s then
           let
             val Ts = T |> strip_type |> swap |> op ::
             val s' = new_skolem_const_name s (length Ts)
           in IConst (`(make_fixed_const (SOME type_enc)) s', T, Ts) end
         else
           IVar ((make_schematic_var v, s), T), atomic_types_of T)
      | iot _ bs (Bound j) =
        nth bs j |> (fn (_, (name, T)) => (IConst (name, T, []), atomic_types_of T))
      | iot fool bs (Abs (s, T, t)) =
        let
          fun vary s = s |> AList.defined (op =) bs s ? vary o Symbol.bump_string
          val s = vary s
          val name = `make_bound_var s
          val (tm, atomic_Ts) = iot fool ((s, (name, T)) :: bs) t
        in
          (IAbs ((name, T), tm), union (op =) atomic_Ts (atomic_types_of T))
        end
  in iot (is_type_enc_fool type_enc)  end

(* "_query" and "_at" are for the ASCII-challenged Metis and Mirabelle. *)
val queries = ["?", "_query"]
val ats = ["@", "_at"]

fun try_unsuffixes ss s =
  fold (fn s' => fn NONE => try (unsuffix s') s | some => some) ss NONE

fun type_enc_of_string strictness s =
  let
    val (poly, s) =
      (case try (unprefix "tc_") s of
        SOME s => (SOME Type_Class_Polymorphic, s)
      | NONE =>
        (case try (unprefix "poly_") s of
          SOME s => (SOME (Raw_Polymorphic With_Phantom_Type_Vars), s)
        | NONE =>
          (case try (unprefix "ml_poly_") s of
            SOME s => (SOME (Raw_Polymorphic Without_Phantom_Type_Vars), s)
          | NONE =>
            (case try (unprefix "raw_mono_") s of
              SOME s => (SOME Raw_Monomorphic, s)
            | NONE =>
              (case try (unprefix "mono_") s of
                SOME s => (SOME Mangled_Monomorphic, s)
              | NONE => (NONE, s))))))

    val (level, s) =
      case try_unsuffixes queries s of
        SOME s =>
        (case try_unsuffixes queries s of
          SOME s => (Nonmono_Types (strictness, Non_Uniform), s)
        | NONE => (Nonmono_Types (strictness, Uniform), s))
      | NONE =>
        (case try_unsuffixes ats s of
          SOME s => (Undercover_Types, s)
        | NONE => (All_Types, s))

    fun native_of_string s =
      let
        val (fool, core) =
          (case try (unsuffix "_fool") s of
            SOME s => (With_FOOL, s)
          | NONE => (Without_FOOL, s))
      in
        (case (core, poly) of
          ("native", SOME poly) =>
          (case (poly, level) of
            (Mangled_Monomorphic, _) =>
            if is_type_level_uniform level then
              Native (First_Order, fool, Mangled_Monomorphic, level)
            else
              raise Same.SAME
          | (Raw_Monomorphic, _) => raise Same.SAME
          | (poly, All_Types) => Native (First_Order, fool, poly, All_Types))
        | ("native_higher", SOME poly) =>
          (case (poly, level) of
            (_, Nonmono_Types _) => raise Same.SAME
          | (_, Undercover_Types) => raise Same.SAME
          | (Mangled_Monomorphic, _) =>
            if is_type_level_uniform level then
              Native (Higher_Order THF_With_Choice, fool, Mangled_Monomorphic, level)
            else
              raise Same.SAME
           | (poly as Raw_Polymorphic _, All_Types) =>
             Native (Higher_Order THF_With_Choice, fool, poly, All_Types)
           | _ => raise Same.SAME))
      end

    fun nonnative_of_string core =
      (case (core, poly, level) of
        ("guards", SOME poly, _) =>
        if (poly = Mangled_Monomorphic andalso level = Undercover_Types) orelse
           poly = Type_Class_Polymorphic then
          raise Same.SAME
        else
          Guards (poly, level)
      | ("tags", SOME poly, _) =>
        if (poly = Mangled_Monomorphic andalso level = Undercover_Types) orelse
           poly = Type_Class_Polymorphic then
          raise Same.SAME
        else
          Tags (poly, level)
      | ("args", SOME poly, All_Types (* naja *)) =>
        if poly = Type_Class_Polymorphic then raise Same.SAME
        else Guards (poly, Const_Types Without_Ctr_Optim)
      | ("args", SOME poly, Nonmono_Types (_, Uniform) (* naja *)) =>
        if poly = Mangled_Monomorphic orelse poly = Type_Class_Polymorphic then
          raise Same.SAME
        else
          Guards (poly, Const_Types With_Ctr_Optim)
      | ("erased", NONE, All_Types (* naja *)) =>
        Guards (Raw_Polymorphic With_Phantom_Type_Vars, No_Types)
      | _ => raise Same.SAME)
  in
    if String.isPrefix "native" s then
      native_of_string s
    else
      nonnative_of_string s
  end
  handle Same.SAME => error ("Unknown type encoding: " ^ quote s)

fun min_hologic THF_Lambda_Free _ = THF_Lambda_Free
  | min_hologic _ THF_Lambda_Free = THF_Lambda_Free
  | min_hologic THF_Without_Choice _ = THF_Without_Choice
  | min_hologic _ THF_Without_Choice = THF_Without_Choice
  | min_hologic _ _ = THF_With_Choice

fun adjust_hologic hologic (Higher_Order hologic') = Higher_Order (min_hologic hologic hologic')
  | adjust_hologic _ type_enc = type_enc

fun adjust_fool Without_FOOL _ = Without_FOOL
  | adjust_fool _ fool = fool

fun no_type_classes Type_Class_Polymorphic = Raw_Polymorphic With_Phantom_Type_Vars
  | no_type_classes poly = poly

fun adjust_type_enc (THF (fool, Polymorphic, hologic)) (Native (order, fool', poly, level)) =
    Native (adjust_hologic hologic order, adjust_fool fool fool', no_type_classes poly, level)
  | adjust_type_enc (THF (fool, Monomorphic, hologic)) (Native (order, fool', _, level)) =
    Native (adjust_hologic hologic order, adjust_fool fool fool', Mangled_Monomorphic, level)
  | adjust_type_enc (TFF (fool, Monomorphic)) (Native (_, fool', _, level)) =
    Native (First_Order, adjust_fool fool fool', Mangled_Monomorphic, level)
  | adjust_type_enc (DFG Polymorphic) (Native (_, _, poly, level)) =
    Native (First_Order, Without_FOOL, poly, level)
  | adjust_type_enc (DFG Monomorphic) (Native (_, _, _, level)) =
    Native (First_Order, Without_FOOL, Mangled_Monomorphic, level)
  | adjust_type_enc (TFF (fool, _)) (Native (_, fool', poly, level)) =
    Native (First_Order, adjust_fool fool fool', no_type_classes poly, level)
  | adjust_type_enc format (Native (_, _, poly, level)) =
    adjust_type_enc format (Guards (no_type_classes poly, level))
  | adjust_type_enc CNF_UEQ (type_enc as Guards stuff) =
    (if is_type_enc_sound type_enc then Tags else Guards) stuff
  | adjust_type_enc _ type_enc = type_enc

fun is_first_order_lambda_free t =
  (case t of
    \<^const>\<open>Not\<close> $ t1 => is_first_order_lambda_free t1
  | Const (\<^const_name>\<open>All\<close>, _) $ Abs (_, _, t') => is_first_order_lambda_free t'
  | Const (\<^const_name>\<open>All\<close>, _) $ t1 => is_first_order_lambda_free t1
  | Const (\<^const_name>\<open>Ex\<close>, _) $ Abs (_, _, t') => is_first_order_lambda_free t'
  | Const (\<^const_name>\<open>Ex\<close>, _) $ t1 => is_first_order_lambda_free t1
  | \<^const>\<open>HOL.conj\<close> $ t1 $ t2 => is_first_order_lambda_free t1 andalso is_first_order_lambda_free t2
  | \<^const>\<open>HOL.disj\<close> $ t1 $ t2 => is_first_order_lambda_free t1 andalso is_first_order_lambda_free t2
  | \<^const>\<open>HOL.implies\<close> $ t1 $ t2 =>
    is_first_order_lambda_free t1 andalso is_first_order_lambda_free t2
  | Const (\<^const_name>\<open>HOL.eq\<close>, Type (_, [\<^typ>\<open>bool\<close>, _])) $ t1 $ t2 =>
    is_first_order_lambda_free t1 andalso is_first_order_lambda_free t2
  | _ => not (exists_subterm (fn Abs _ => true | _ => false) t))

fun simple_translate_lambdas eta_matters do_lambdas ctxt type_enc t =
  if not eta_matters andalso is_first_order_lambda_free t then
    t
  else
    let
      fun trans_first_order Ts t =
        (case t of
          \<^const>\<open>Not\<close> $ t1 => \<^const>\<open>Not\<close> $ trans_first_order Ts t1
        | (t0 as Const (\<^const_name>\<open>All\<close>, _)) $ Abs (s, T, t') =>
          t0 $ Abs (s, T, trans_first_order (T :: Ts) t')
        | (t0 as Const (\<^const_name>\<open>All\<close>, _)) $ t1 =>
          trans_first_order Ts (t0 $ eta_expand Ts t1 1)
        | (t0 as Const (\<^const_name>\<open>Ex\<close>, _)) $ Abs (s, T, t') =>
          t0 $ Abs (s, T, trans_first_order (T :: Ts) t')
        | (t0 as Const (\<^const_name>\<open>Ex\<close>, _)) $ t1 =>
          trans_first_order Ts (t0 $ eta_expand Ts t1 1)
        | (t0 as \<^const>\<open>HOL.conj\<close>) $ t1 $ t2 =>
          t0 $ trans_first_order Ts t1 $ trans_first_order Ts t2
        | (t0 as \<^const>\<open>HOL.disj\<close>) $ t1 $ t2 =>
          t0 $ trans_first_order Ts t1 $ trans_first_order Ts t2
        | (t0 as \<^const>\<open>HOL.implies\<close>) $ t1 $ t2 =>
          t0 $ trans_first_order Ts t1 $ trans_first_order Ts t2
        | (t0 as Const (\<^const_name>\<open>HOL.eq\<close>, Type (_, [\<^typ>\<open>bool\<close>, _]))) $ t1 $ t2 =>
          t0 $ trans_first_order Ts t1 $ trans_first_order Ts t2
        | _ =>
          if not (exists_subterm (fn Abs _ => true | _ => false) t) then t
          else t |> Envir.eta_contract |> do_lambdas ctxt Ts)

      fun trans_fool Ts t =
        (case t of
          (t1 as Const (\<^const_name>\<open>Let\<close>, _)) $ t2 $ t3 =>
          (case t3 of
            Abs (s3, T, t') => t1 $ trans_fool Ts t2 $ Abs (s3, T, trans_fool (T :: Ts) t')
          | _ => trans_fool Ts (t1 $ trans_fool Ts t2 $ eta_expand Ts t3 1))
        | (t0 as Const (\<^const_name>\<open>All\<close>, _)) $ t1 =>
            (case t1 of
              Abs (s, T, t') => t0 $ Abs (s, T, trans_fool (T :: Ts) t')
            | _ => trans_fool Ts (t0 $ eta_expand Ts t1 1))
        | (t0 as Const (\<^const_name>\<open>Ex\<close>, _)) $ t1 =>
            (case t1 of
              Abs (s, T, t') => t0 $ Abs (s, T, trans_fool (T :: Ts) t')
            | _ => trans_fool Ts (t0 $ eta_expand Ts t1 1))
        | t1 $ t2 => trans_fool Ts t1 $ trans_fool Ts t2
        | Abs _ => t |> Envir.eta_contract |> do_lambdas ctxt Ts
        | _ => t)

      val (t', ctxt') = yield_singleton (Variable.import_terms true) t ctxt
    in
      t' |> (if is_type_enc_fool type_enc then trans_fool else trans_first_order) []
         |> singleton (Variable.export_terms ctxt' ctxt)
    end

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
  (t |> conceal_bounds Ts
     |> Thm.cterm_of ctxt
     |> Meson_Clausify.introduce_combinators_in_cterm ctxt
     |> Thm.prop_of |> Logic.dest_equals |> snd
     |> reveal_bounds Ts)
  (* A type variable of sort "{}" will make abstraction fail. *)
  handle THM _ => t |> do_cheaply_conceal_lambdas Ts

val introduce_combinators = simple_translate_lambdas false do_introduce_combinators

fun constify_lifted (t $ u) = constify_lifted t $ constify_lifted u
  | constify_lifted (Abs (s, T, t)) = Abs (s, T, constify_lifted t)
  | constify_lifted (Free (x as (s, _))) =
    (if String.isPrefix lam_lifted_prefix s then Const else Free) x
  | constify_lifted t = t

fun is_binder true (Const (\<^const_name>\<open>Let\<close>, _) $ _) = true
  | is_binder _ t = Lambda_Lifting.is_quantifier t

fun lift_lams_part_1 ctxt type_enc =
  map hol_close_form #> rpair ctxt
  #-> Lambda_Lifting.lift_lambdas (SOME
    ((if is_type_enc_polymorphic type_enc then lam_lifted_poly_prefix
      else lam_lifted_mono_prefix) ^ "_a"))
    (is_binder (is_type_enc_fool type_enc))
  #> fst

fun lift_lams_part_2 ctxt type_enc (facts, lifted) =
  (facts, lifted)
  (* Lambda-lifting sometimes leaves some lambdas around; we need some way to get rid of them *)
  |> apply2 (map (introduce_combinators ctxt type_enc))
  |> apply2 (map constify_lifted)
  (* Requires bound variables not to clash with any schematic variables (as should be the case right
     after lambda-lifting). *)
  |>> map (hol_open_form (unprefix hol_close_form_prefix))
  ||> map (hol_open_form I)

fun lift_lams ctxt type_enc =
  (is_type_enc_fool type_enc ?
   map (simple_translate_lambdas true (fn _ => fn _ => fn t => t) ctxt type_enc))
  #> lift_lams_part_1 ctxt type_enc
  #> lift_lams_part_2 ctxt type_enc

fun intentionalize_def (Const (\<^const_name>\<open>All\<close>, _) $ Abs (_, _, t)) =
    intentionalize_def t
  | intentionalize_def (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ t $ u) =
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
   role : atp_formula_role,
   iformula : (string * string, typ, iterm, string * string) atp_formula,
   atomic_types : typ list}

fun update_iformula f ({name, stature, role, iformula, atomic_types} : ifact) =
  {name = name, stature = stature, role = role, iformula = f iformula, atomic_types = atomic_types}
  : ifact

fun ifact_lift f ({iformula, ...} : ifact) = f iformula

fun insert_type thy get_T x xs =
  let val T = get_T x in
    if exists (type_instance thy T o get_T) xs then xs
    else x :: filter_out (type_generalization thy T o get_T) xs
  end

fun chop_fun 0 T = ([], T)
  | chop_fun n (Type (\<^type_name>\<open>fun\<close>, [dom_T, ran_T])) =
    chop_fun (n - 1) ran_T |>> cons dom_T
  | chop_fun _ T = ([], T)

fun filter_type_args thy ctrss type_enc s ary T_args =
  let val poly = polymorphism_of_type_enc type_enc in
    if s = type_tag_name then (* FIXME: why not "type_guard_name" as well? *)
      T_args
    else
      (case type_enc of
        Native (_, _, Raw_Polymorphic _, _) => T_args
      | Native (_, _, Type_Class_Polymorphic, _) => T_args
      | _ =>
        let
          fun gen_type_args _ _ [] = []
            | gen_type_args keep strip_ty T_args =
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
                val U_args = (s, U) |> robust_const_type_args thy
              in map (filt o apfst dest_TVar) (U_args ~~ T_args) end
              handle TYPE _ => T_args
          fun is_always_ctr (s', T') =
            s' = s andalso type_equiv thy (T', robust_const_type thy s')
          val noninfer_type_args = gen_type_args (not o fst) (chop_fun ary)
          val ctr_infer_type_args = gen_type_args fst strip_type
          val level = level_of_type_enc type_enc
        in
          if level = No_Types orelse s = \<^const_name>\<open>HOL.eq\<close> orelse
             (case level of Const_Types _ => s = app_op_name | _ => false) then
            []
          else if poly = Mangled_Monomorphic then
            T_args
          else if level = All_Types then
            (case type_enc of
              Guards _ => noninfer_type_args T_args
            | Tags _ => [])
          else if level = Undercover_Types then
            noninfer_type_args T_args
          else if level <> Const_Types Without_Ctr_Optim andalso
                  exists (exists is_always_ctr) ctrss then
            ctr_infer_type_args T_args
          else
            T_args
        end)
  end

fun raw_atp_type_of_typ type_enc =
  let
    fun term (Type (s, Ts)) =
      AType
        ((if s = \<^type_name>\<open>fun\<close> andalso is_type_enc_higher_order type_enc then
            `I tptp_fun_type
          else if s = \<^type_name>\<open>bool\<close> andalso
            (is_type_enc_full_higher_order type_enc orelse is_type_enc_fool type_enc) then
            `I tptp_bool_type
          else
            `make_fixed_type_const s, []), map term Ts)
    | term (TFree (s, _)) = AType ((`make_tfree s, []), [])
    | term (TVar z) = AType ((tvar_name z, []), [])
  in term end

fun atp_term_of_atp_type (AType ((name, _), tys)) = ATerm ((name, []), map atp_term_of_atp_type tys)
  | atp_term_of_atp_type _ = raise Fail "unexpected type"

fun atp_type_of_type_arg type_enc T =
  if T = dummyT then NONE else SOME (raw_atp_type_of_typ type_enc T)

(* This shouldn't clash with anything else. *)
val uncurried_alias_sep = "\000"
val mangled_type_sep = "\001"

val ascii_of_uncurried_alias_sep = ascii_of uncurried_alias_sep

fun generic_mangled_type_name f (AType ((name, _), [])) = f name
  | generic_mangled_type_name f (AType ((name, _), tys)) =
    f name ^ "(" ^ space_implode "," (map (generic_mangled_type_name f) tys) ^ ")"
  | generic_mangled_type_name _ _ = raise Fail "unexpected type"

fun mangled_type type_enc = generic_mangled_type_name fst o raw_atp_type_of_typ type_enc

fun make_native_type s =
  if s = tptp_bool_type orelse s = tptp_fun_type orelse s = tptp_individual_type then s
  else native_type_prefix ^ ascii_of s

fun native_atp_type_of_raw_atp_type type_enc pred_sym ary =
  let
    fun to_mangled_atype ty =
      AType (((make_native_type (generic_mangled_type_name fst ty),
               generic_mangled_type_name snd ty), []), [])
    fun to_poly_atype (AType ((name, clss), tys)) = AType ((name, clss), map to_poly_atype tys)
      | to_poly_atype _ = raise Fail "unexpected type"
    val to_atype =
      if is_type_enc_polymorphic type_enc then to_poly_atype
      else to_mangled_atype
    fun to_afun f1 f2 tys = AFun (f1 (hd tys), f2 (nth tys 1))
    fun to_ho (ty as AType (((s, _), _), tys)) =
        if s = tptp_fun_type then to_afun to_ho to_ho tys else to_atype ty
      | to_ho _ = raise Fail "unexpected type"
    fun to_lfho (ty as AType (((s, _), _), tys)) =
        if s = tptp_fun_type then to_afun to_ho to_lfho tys
        else if pred_sym then bool_atype
        else to_atype ty
      | to_lfho _ = raise Fail "unexpected type"
    fun to_fo 0 ty = if pred_sym then bool_atype else to_atype ty
      | to_fo ary (AType (_, tys)) = to_afun to_atype (to_fo (ary - 1)) tys
      | to_fo _ _ = raise Fail "unexpected type"
  in
    if is_type_enc_full_higher_order type_enc then to_ho
    else if is_type_enc_higher_order type_enc then to_lfho
    else to_fo ary
  end

fun native_atp_type_of_typ type_enc pred_sym ary =
  native_atp_type_of_raw_atp_type type_enc pred_sym ary o raw_atp_type_of_typ type_enc

(* Make atoms for sorted type variables. *)
fun generic_add_sorts_on_type _ [] = I
  | generic_add_sorts_on_type T (s :: ss) =
    generic_add_sorts_on_type T ss
    #> (if s = the_single \<^sort>\<open>type\<close> then I else insert (op =) (s, T))
fun add_sorts_on_tfree (T as TFree (_, S)) = generic_add_sorts_on_type T S
  | add_sorts_on_tfree _ = I
fun add_sorts_on_tvar (T as TVar (_, S)) = generic_add_sorts_on_type T S
  | add_sorts_on_tvar _ = I

fun process_type_args type_enc T_args =
  if is_type_enc_native type_enc then
    (map (native_atp_type_of_typ type_enc false 0) T_args, [])
  else
    ([], map_filter (Option.map atp_term_of_atp_type o atp_type_of_type_arg type_enc) T_args)

fun class_atom type_enc (cl, T) =
  let
    val cl = `make_class cl
    val (ty_args, tm_args) = process_type_args type_enc [T]
    val tm_args =
      tm_args @
      (case type_enc of
        Native (_, _, Raw_Polymorphic Without_Phantom_Type_Vars, _) =>
        [ATerm ((TYPE_name, ty_args), [])]
      | _ => [])
  in AAtom (ATerm ((cl, ty_args), tm_args)) end

fun class_atoms type_enc (cls, T) =
  map (fn cl => class_atom type_enc (cl, T)) cls

fun class_membs_of_types type_enc add_sorts_on_typ Ts =
  [] |> level_of_type_enc type_enc <> No_Types ? fold add_sorts_on_typ Ts

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
  in mk_aquant AForall (rev (add_formula_vars [] phi [])) phi end

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
  (case space_explode uncurried_alias_sep s of
    [_] => (s, s')
  | [s1, s2] => (s1, unsuffix s2 s')
  | _ => raise Fail "ill-formed explicit application alias")

fun raw_mangled_const_name type_name ty_args (s, s') =
  let
    fun type_suffix f g =
      fold_rev (prefix o g o prefix mangled_type_sep o type_name f) ty_args ""
  in (s ^ type_suffix fst ascii_of, s' ^ type_suffix snd I) end
fun mangled_const_name type_enc =
  map_filter (atp_type_of_type_arg type_enc)
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

val unmangled_invert_const = invert_const o hd o unmangled_const_name

fun vars_of_iterm vars (IConst ((s, _), _, _)) = insert (op =) s vars
  | vars_of_iterm vars (IVar ((s, _), _)) = insert (op =) s vars
  | vars_of_iterm vars (IApp (tm1, tm2)) = union (op =) (vars_of_iterm vars tm1) (vars_of_iterm vars tm2)
  | vars_of_iterm vars (IAbs (_, tm)) = vars_of_iterm vars tm

fun generate_unique_name gen unique n =
  let val x = gen n in
    if unique x then x else generate_unique_name gen unique (n + 1)
  end

fun eta_expand_quantifier_body (tm as IAbs _) = tm
  | eta_expand_quantifier_body tm =
    let
      (* We accumulate all variables because E 2.5 does not support variable shadowing. *)
      val vars = vars_of_iterm [] tm
      val x = generate_unique_name
        (fn n => "X" ^ (if n = 0 then "" else string_of_int n))
        (fn name => not (exists (equal name) vars)) 0
        |> `(prefix bound_var_prefix)
      val T = domain_type (ityp_of tm)
    in
      IAbs ((x, T), IApp (tm, IConst (x, T, [])))
    end

fun introduce_builtins_and_proxies_in_iterm type_enc =
  let
    val is_fool = is_type_enc_fool type_enc
    fun tweak_ho_quant ho_quant (T as Type (_, [p_T as Type (_, [x_T, _]), _])) [] =
        (* Eta-expand "!!" and "??", to work around LEO-II, Leo-III, and Satallax parser
           limitations. This works in conjunction with special code in "ATP_Problem" that uses the
           syntactic sugar "!" and "?" whenever possible. *)
        IAbs ((`I "P", p_T),
              IApp (IConst (`I ho_quant, T, []),
                    IAbs ((`I "X", x_T),
                          IApp (IConst (`I "P", p_T, []),
                                IConst (`I "X", x_T, [])))))
      | tweak_ho_quant ho_quant T _ = IConst (`I ho_quant, T, [])
    fun tweak_ho_equal T argc =
      if argc = 2 then
        IConst (`I tptp_equal, T, [])
      else
        (* Eta-expand partially applied THF equality, because the LEO-II and Satallax parsers
           complain about not being able to infer the type of "=". *)
        let val i_T = domain_type T in
          IAbs ((`I "Y", i_T),
                IAbs ((`I "Z", i_T),
                      IApp (IApp (IConst (`I tptp_equal, T, []),
                                  IConst (`I "Y", i_T, [])),
                            IConst (`I "Z", i_T, []))))
        end
    fun intro top_level args (IApp (tm1, tm2)) =
        let
          val tm1' = intro top_level (tm2 :: args) tm1
          val tm2' = intro false [] tm2
          val tm2'' =
            (case tm1' of
              IApp (IConst ((s, _), _, _), _) =>
              if s = tptp_let then
                (case tm2' of
                  IAbs ((name, T), tm) =>
                    let
                      val name' =
                        map_prod (prefix let_bound_var_prefix o unprefix bound_var_prefix) I name
                    in
                      IAbs ((name', T), alpha_rename name name' tm)
                    end
                | _ => error "Function abstraction expected")
              else
                tm2'
            | IConst ((s, _), _, _) =>
              if s = tptp_ho_forall orelse s = tptp_ho_exists then
                eta_expand_quantifier_body tm2'
              else
                tm2'
            | _ => tm2')
        in
          IApp (tm1', tm2'')
        end
      | intro top_level args (IConst (name as (s, _), T, T_args)) =
        let val argc = length args in
          if is_fool andalso s = "c_If" andalso
              (argc = 3 orelse is_type_enc_higher_order type_enc) then
            IConst (`I tptp_ite, T, [])
          else if is_fool andalso s = "c_Let" andalso argc = 2 then
            IConst (`I tptp_let, T, [])
          else
            (case proxify_const s of
              SOME proxy_base =>
              let
                fun plain_const () = IConst (name, T, [])
                fun proxy_const () = IConst (proxy_base |>> prefix const_prefix, T, T_args)
                fun handle_fool card x = if card = argc then x else proxy_const ()
              in
                if top_level then
                  (case s of
                    "c_False" => IConst (`I tptp_false, T, [])
                  | "c_True" => IConst (`I tptp_true, T, [])
                  | _ => plain_const ())
                else if is_type_enc_full_higher_order type_enc then
                  (case s of
                    "c_False" => IConst (`I tptp_false, T, [])
                  | "c_True" => IConst (`I tptp_true, T, [])
                  | "c_Not" => IConst (`I tptp_not, T, [])
                  | "c_conj" => IConst (`I tptp_and, T, [])
                  | "c_disj" => IConst (`I tptp_or, T, [])
                  | "c_implies" => IConst (`I tptp_implies, T, [])
                  | "c_All" => tweak_ho_quant tptp_ho_forall T args
                  | "c_Ex" => tweak_ho_quant tptp_ho_exists T args
                  | s =>
                    if is_tptp_equal s then
                      tweak_ho_equal T argc
                    else
                      plain_const ())
                else if is_fool then
                  (case s of
                    "c_False" => IConst (`I tptp_false, T, [])
                  | "c_True" => IConst (`I tptp_true, T, [])
                  | "c_Not" => handle_fool 1 (IConst (`I tptp_not, T, []))
                  | "c_conj" => handle_fool 2 (IConst (`I tptp_and, T, []))
                  | "c_disj" => handle_fool 2 (IConst (`I tptp_or, T, []))
                  | "c_implies" => handle_fool 2 (IConst (`I tptp_implies, T, []))
                  | "c_All" => handle_fool 1 (tweak_ho_quant tptp_ho_forall T args)
                  | "c_Ex" => handle_fool 1 (tweak_ho_quant tptp_ho_exists T args)
                  | s =>
                    if is_tptp_equal s then
                      handle_fool 2 (IConst (`I tptp_equal, T, []))
                    else
                      plain_const ())
                else
                  proxy_const ()
              end
             | NONE =>
               if s = tptp_choice then
                 tweak_ho_quant tptp_choice T args
               else
                 IConst (name, T, T_args))
        end
      | intro _ _ (IAbs (bound, tm)) = IAbs (bound, intro false [] tm)
      | intro _ _ tm = tm
  in intro true [] end

fun mangle_type_args_in_const type_enc (name as (s, _)) T_args =
  if String.isPrefix const_prefix s andalso is_type_enc_mangling type_enc then
    (mangled_const_name type_enc T_args name, [])
  else
    (name, T_args)
fun mangle_type_args_in_iterm type_enc =
  if is_type_enc_mangling type_enc then
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

fun filter_type_args_in_const _ _ _ _ _ [] = []
  | filter_type_args_in_const thy ctrss type_enc ary s T_args =
    (case unprefix_and_unascii const_prefix s of
      NONE => if level_of_type_enc type_enc = No_Types orelse s = tptp_choice then [] else T_args
    | SOME s'' => filter_type_args thy ctrss type_enc (unmangled_invert_const s'') ary T_args)

fun filter_type_args_in_iterm thy ctrss type_enc =
  let
    fun filt ary (IApp (tm1, tm2)) = IApp (filt (ary + 1) tm1, filt 0 tm2)
      | filt ary (IConst (name as (s, _), T, T_args)) =
        filter_type_args_in_const thy ctrss type_enc ary s T_args
        |> (fn T_args => IConst (name, T, T_args))
      | filt _ (IAbs (bound, tm)) = IAbs (bound, filt 0 tm)
      | filt _ tm = tm
  in filt 0 end

fun iformula_of_prop ctxt type_enc iff_for_eq =
  let
    val thy = Proof_Context.theory_of ctxt
    fun do_term bs t atomic_Ts =
      iterm_of_term thy type_enc bs (Envir.eta_contract t)
      |>> (introduce_builtins_and_proxies_in_iterm type_enc
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
      (case t of
        \<^const>\<open>Trueprop\<close> $ t1 => do_formula bs pos t1
      | \<^const>\<open>Not\<close> $ t1 => do_formula bs (Option.map not pos) t1 #>> mk_anot
      | Const (\<^const_name>\<open>All\<close>, _) $ Abs (s, T, t') => do_quant bs AForall pos s T t'
      | (t0 as Const (\<^const_name>\<open>All\<close>, _)) $ t1 =>
        do_formula bs pos (t0 $ eta_expand (map (snd o snd) bs) t1 1)
      | Const (\<^const_name>\<open>Ex\<close>, _) $ Abs (s, T, t') => do_quant bs AExists pos s T t'
      | (t0 as Const (\<^const_name>\<open>Ex\<close>, _)) $ t1 =>
        do_formula bs pos (t0 $ eta_expand (map (snd o snd) bs) t1 1)
      | \<^const>\<open>HOL.conj\<close> $ t1 $ t2 => do_conn bs AAnd pos t1 pos t2
      | \<^const>\<open>HOL.disj\<close> $ t1 $ t2 => do_conn bs AOr pos t1 pos t2
      | \<^const>\<open>HOL.implies\<close> $ t1 $ t2 => do_conn bs AImplies (Option.map not pos) t1 pos t2
      | Const (\<^const_name>\<open>HOL.eq\<close>, Type (_, [\<^typ>\<open>bool\<close>, _])) $ t1 $ t2 =>
        if iff_for_eq then do_conn bs AIff NONE t1 NONE t2 else do_term bs t
      | _ => do_term bs t)
  in do_formula [] end

fun presimplify_term simp_options ctxt t =
  if exists_Const (member (op =) Meson.presimplified_consts o fst) t then
    t |> Skip_Proof.make_thm (Proof_Context.theory_of ctxt)
      |> Meson.presimplify simp_options ctxt
      |> Thm.prop_of
  else
    t

fun preprocess_abstractions_in_terms trans_lams facts =
  let
    val (facts, lambda_ts) =
      facts |> map (snd o snd) |> trans_lams
            |>> map2 (fn (name, (role, _)) => fn t => (name, (role, t))) facts
    val lam_facts =
      map2 (fn t => fn j =>
               ((lam_fact_prefix ^ Int.toString j,
                 (Global, Non_Rec_Def)), (Axiom, t)))
           lambda_ts (1 upto length lambda_ts)
  in (facts, lam_facts) end

(* Metis's use of "resolve_tac" freezes the schematic variables. We simulate this in Sledgehammer to
   prevent the discovery of unreplayable proofs. *)
fun freeze_term t =
  let
    (* Freshness is desirable for completeness, but not for soundness. *)
    fun indexed_name (s, i) = s ^ "_" ^ string_of_int i ^ atp_weak_suffix
    fun freeze (t $ u) = freeze t $ freeze u
      | freeze (Abs (s, T, t)) = Abs (s, T, freeze t)
      | freeze (Var (x, T)) = Free (indexed_name x, T)
      | freeze t = t
    fun freeze_tvar (x, S) = TFree (indexed_name x, S)
  in
    t |> exists_subterm is_Var t ? freeze
      |> exists_type (exists_subtype is_TVar) t
         ? map_types (map_type_tvar freeze_tvar)
  end

fun presimp_prop simp_options ctxt type_enc t =
  let
    val t =
      t |> Envir.beta_eta_contract
        |> transform_elim_prop
        |> Object_Logic.atomize_term ctxt
    val need_trueprop = (fastype_of t = \<^typ>\<open>bool\<close>)
    val is_ho = is_type_enc_full_higher_order type_enc
  in
    t |> need_trueprop ? HOLogic.mk_Trueprop
      |> (if is_ho then unextensionalize_def
          else cong_extensionalize_term ctxt #> abs_extensionalize_term ctxt)
      |> presimplify_term simp_options ctxt
      |> HOLogic.dest_Trueprop
  end
  handle TERM _ => \<^const>\<open>True\<close>

(* Satallax prefers "=" to "<=>" (for definitions) and Metis (CNF) requires "=" for technical
   reasons. *)
fun should_use_iff_for_eq CNF _ = false
  | should_use_iff_for_eq (THF _) format = not (is_type_enc_full_higher_order format)
  | should_use_iff_for_eq _ _ = true

fun make_formula ctxt format type_enc iff_for_eq name stature role t =
  let
    val iff_for_eq = iff_for_eq andalso should_use_iff_for_eq format type_enc
    val (iformula, atomic_Ts) =
      iformula_of_prop ctxt type_enc iff_for_eq (SOME (role <> Conjecture)) t []
      |>> close_universally add_iterm_vars
  in
    {name = name, stature = stature, role = role, iformula = iformula, atomic_types = atomic_Ts}
  end

fun make_fact ctxt format type_enc iff_for_eq ((name, stature), t) =
  (case make_formula ctxt format type_enc iff_for_eq name stature Axiom t of
    formula as {iformula = AAtom (IConst ((s, _), _, _)), ...} =>
    if s = tptp_true then NONE else SOME formula
  | formula => SOME formula)

fun make_conjecture ctxt format type_enc =
  map (fn ((name, stature), (role, t)) =>
    let val t' = t |> role = Conjecture ? s_not in
      make_formula ctxt format type_enc true name stature role t'
    end)

(** Finite and infinite type inference **)

fun tvar_footprint thy s ary =
  (case unprefix_and_unascii const_prefix s of
    SOME s =>
    let fun tvars_of T = [] |> Term.add_tvarsT T |> map fst in
      s |> unmangled_invert_const |> robust_const_type thy |> chop_fun ary |> fst |> map tvars_of
    end
  | NONE => [])
  handle TYPE _ => []

fun type_arg_cover thy pos s ary =
  if is_tptp_equal s then
    if pos = SOME false then [] else 0 upto ary - 1
  else
    let
      val footprint = tvar_footprint thy s ary
      val eq = (s = \<^const_name>\<open>HOL.eq\<close>)
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
        |> sort (rev_order o list_ord Term_Ord.indexname_ord o apply2 snd)
        |> cover []
    end

type monotonicity_info =
  {maybe_finite_Ts : typ list,
   surely_infinite_Ts : typ list,
   maybe_nonmono_Ts : typ list}

(* These types witness that the type classes they belong to allow infinite
   models and hence that any types with these type classes is monotonic. *)
val known_infinite_types = [\<^typ>\<open>nat\<close>, HOLogic.intT, HOLogic.realT, \<^typ>\<open>nat => bool\<close>]

fun is_type_kind_of_surely_infinite ctxt strictness cached_Ts T =
  strictness <> Strict andalso is_type_surely_infinite ctxt true cached_Ts T

(* Finite types such as "unit", "bool", "bool * bool", and "bool => bool" are
   dangerous because their "exhaust" properties can easily lead to unsound ATP
   proofs. On the other hand, all HOL infinite types can be given the same
   models in first-order logic (via Loewenheim-Skolem). *)

fun should_encode_type ctxt {maybe_finite_Ts, surely_infinite_Ts, maybe_nonmono_Ts}
      (Nonmono_Types (strictness, _)) T =
    let val thy = Proof_Context.theory_of ctxt in
      (exists (type_intersect thy T) maybe_nonmono_Ts andalso
       not (exists (type_instance thy T) surely_infinite_Ts orelse
            (not (member (type_equiv thy) maybe_finite_Ts T) andalso
             is_type_kind_of_surely_infinite ctxt strictness surely_infinite_Ts T)))
    end
  | should_encode_type _ _ level _ = (level = All_Types orelse level = Undercover_Types)

fun should_guard_type ctxt mono (Guards (_, level)) should_guard_var T =
    should_guard_var () andalso should_encode_type ctxt mono level T
  | should_guard_type _ _ _ _ _ = false

fun is_maybe_universal_name s =
  String.isPrefix bound_var_prefix s orelse
  String.isPrefix all_bound_var_prefix s

fun is_maybe_universal_var (IConst ((s, _), _, _)) = is_maybe_universal_name s
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
      (case level of
        Nonmono_Types (_, Non_Uniform) =>
        (case (site, is_maybe_universal_var u) of
          (Eq_Arg pos, true) =>
          (pos <> SOME false orelse tag_neg_vars) andalso should_encode_type ctxt mono level T
        | _ => false)
      | Undercover_Types =>
        (case (site, is_maybe_universal_var u) of
          (Eq_Arg pos, true) => pos <> SOME false
        | (Arg (s, j, ary), true) => member (op =) (type_arg_cover thy NONE s ary) j
        | _ => false)
      | _ => should_encode_type ctxt mono level T)
    end
  | should_tag_with_type _ _ _ _ _ _ = false

(** predicators and application operators **)

type sym_info = {pred_sym : bool, min_ary : int, max_ary : int, types : typ list, in_conj : bool}

fun default_sym_tab_entries type_enc =
  let
    fun mk_sym_info pred n =
      {pred_sym = pred, min_ary = n, max_ary = n, types = [], in_conj = false}
  in
    (make_fixed_const NONE \<^const_name>\<open>undefined\<close>, mk_sym_info false 0) ::
    (map (rpair (mk_sym_info true 0)) [tptp_false, tptp_true]) @
    (map (rpair (mk_sym_info true 1)) tptp_unary_builtins) @
    (map (rpair (mk_sym_info true 2)) (tptp_old_equal :: tptp_binary_builtins)) @
    (map (rpair (mk_sym_info true 3)) tptp_ternary_builtins)
    |> not (is_type_enc_fool type_enc orelse is_type_enc_full_higher_order type_enc)
      ? cons (prefixed_predicator_name, mk_sym_info true 1)
  end

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
          if ary = max_ary orelse type_instance thy var_T T orelse type_instance thy T var_T then
            ary
          else
            iter (ary + 1) (range_type T)
      in iter 0 const_T end
    fun add_universal_var T (accum as ((bool_vars, fun_var_Ts), sym_tab)) =
      if (app_op_level = Sufficient_App_Op andalso can dest_funT T) orelse
         (app_op_level = Sufficient_App_Op_And_Predicator andalso
          (can dest_funT T orelse T = \<^typ>\<open>bool\<close>)) then
        let
          val bool_vars' =
            bool_vars orelse
            (app_op_level = Sufficient_App_Op_And_Predicator andalso body_type T = \<^typ>\<open>bool\<close>)
          fun repair_min_ary {pred_sym, min_ary, max_ary, types, in_conj} =
            {pred_sym = pred_sym andalso not bool_vars',
             min_ary = fold (fn T' => consider_var_ary T' T) types min_ary,
             max_ary = max_ary, types = types, in_conj = in_conj}
          val fun_var_Ts' = fun_var_Ts |> can dest_funT T ? insert_type thy I T
        in
          if bool_vars' = bool_vars andalso fun_var_Ts' = fun_var_Ts then accum
          else ((bool_vars', fun_var_Ts'), Symtab.map (K repair_min_ary) sym_tab)
        end
      else
        accum
    fun add_iterm_syms top_level tm (accum as ((bool_vars, fun_var_Ts), sym_tab)) =
      let val (head, args) = strip_iterm_comb tm in
        (case head of
          IConst ((s, _), T, _) =>
          if is_maybe_universal_name s then
            add_universal_var T accum
          else if String.isPrefix exist_bound_var_prefix s then
            accum
          else
            let val ary = length args in
              ((bool_vars, fun_var_Ts),
               (case Symtab.lookup sym_tab s of
                 SOME {pred_sym, min_ary, max_ary, types, in_conj} =>
                 let
                   val pred_sym = pred_sym andalso top_level andalso not bool_vars
                   val types' = types |> insert_type thy I T
                   val in_conj = in_conj orelse conj_fact
                   val min_ary =
                     if (app_op_level = Sufficient_App_Op orelse
                         app_op_level = Sufficient_App_Op_And_Predicator)
                        andalso types' <> types then
                       fold (consider_var_ary T) fun_var_Ts min_ary
                     else
                       min_ary
                 in
                   Symtab.update (s, {pred_sym = pred_sym, min_ary = Int.min (ary, min_ary),
                     max_ary = Int.max (ary, max_ary), types = types', in_conj = in_conj}) sym_tab
                 end
               | NONE =>
                 let
                   val max_ary =
                     (case unprefix_and_unascii const_prefix s of
                       SOME s =>
                       (if String.isSubstring uncurried_alias_sep s then
                          ary
                        else
                          (case try (ary_of o robust_const_type thy o unmangled_invert_const) s of
                            SOME ary0 => Int.min (ary0, ary)
                          | NONE => ary))
                     | NONE => ary)
                   val pred_sym = top_level andalso max_ary = ary andalso not bool_vars
                   val min_ary =
                     (case app_op_level of
                       Min_App_Op => max_ary
                     | Full_App_Op_And_Predicator => 0
                     | _ => fold (consider_var_ary T) fun_var_Ts max_ary)
                 in
                   Symtab.update_new (s, {pred_sym = pred_sym, min_ary = min_ary, max_ary = max_ary,
                     types = [T], in_conj = conj_fact}) sym_tab
                 end))
            end
        | IVar (_, T) => add_universal_var T accum
        | IAbs ((_, T), tm) => accum |> add_universal_var T |> add_iterm_syms false tm
        | _ => accum)
        |> fold (add_iterm_syms false) args
      end
  in add_iterm_syms end

fun sym_table_of_facts ctxt type_enc app_op_level conjs facts =
  let
    fun add_iterm_syms conj_fact = add_iterm_syms_to_sym_table ctxt app_op_level conj_fact true
    fun add_fact_syms conj_fact = ifact_lift (formula_fold NONE (K (add_iterm_syms conj_fact)))
  in
    ((false, []), Symtab.empty)
    |> fold (add_fact_syms true) conjs
    |> fold (add_fact_syms false) facts
    ||> fold Symtab.update (default_sym_tab_entries type_enc)
  end

fun min_ary_of sym_tab s =
  (case Symtab.lookup sym_tab s of
    SOME ({min_ary, ...} : sym_info) => min_ary
  | NONE =>
    (case unprefix_and_unascii const_prefix s of
      SOME s =>
      let val s = s |> unmangled_invert_const in
        if s = predicator_name then 1
        else if s = app_op_name then 2
        else if s = type_guard_name then 1
        else 0
      end
    | NONE => 0))

(* True if the constant ever appears outside of the top-level position in
   literals, or if it appears with different arities (e.g., because of different
   type instantiations). If false, the constant always receives all of its
   arguments and is used as a predicate. *)
fun is_pred_sym sym_tab s =
  (case Symtab.lookup sym_tab s of
    SOME ({pred_sym, min_ary, max_ary, ...} : sym_info) => pred_sym andalso min_ary = max_ary
  | NONE => false)

val fTrue_iconst = IConst ((const_prefix ^ "fTrue", \<^const_name>\<open>fTrue\<close>), \<^typ>\<open>bool\<close>, [])
val predicator_iconst = IConst (`(make_fixed_const NONE) predicator_name, \<^typ>\<open>bool => bool\<close>, [])

fun predicatify completish tm =
  if completish > 1 then
    IApp (IApp (IConst (`I tptp_equal, \<^typ>\<open>bool => bool => bool\<close>, []), tm), fTrue_iconst)
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

fun firstorderize_fact thy ctrss type_enc uncurried_aliases completish sym_tab =
  let
    fun do_app arg head = mk_app_op type_enc head arg
    fun list_app_ops (head, args) = fold do_app args head
    fun introduce_app_ops tm =
      let val (head, args) = tm |> strip_iterm_comb ||> map introduce_app_ops in
        (case head of
          IConst (name as (s, _), T, T_args) =>
          let
            val min_ary = min_ary_of sym_tab s
            val ary =
              if uncurried_aliases andalso String.isPrefix const_prefix s then
                let
                  val ary = length args
                  (* In polymorphic native type encodings, it is impossible to
                     declare a fully polymorphic symbol that takes more
                     arguments than its signature (even though such concrete
                     instances, where a type variable is instantiated by a
                     function type, are possible.) *)
                  val official_ary =
                    if is_type_enc_polymorphic type_enc then
                      (case unprefix_and_unascii const_prefix s of
                        SOME s' =>
                        (case try (ary_of o robust_const_type thy) (invert_const s') of
                          SOME ary => ary
                        | NONE => min_ary)
                      | NONE => min_ary)
                    else
                      1000000000 (* irrealistically big arity *)
                in Int.min (ary, official_ary) end
              else
                min_ary
            val head =
              if ary = min_ary then head else IConst (aliased_uncurried ary name, T, T_args)
          in
            args |> chop ary |>> list_app head |> list_app_ops
          end
        | IAbs ((name, T), tm) =>
          list_app_ops (IAbs ((name, T), introduce_app_ops tm), args)
        | _ => list_app_ops (head, args))
      end
    fun introduce_predicators tm =
      (case strip_iterm_comb tm of
        (IConst ((s, _), _, _), _) =>
        if is_pred_sym sym_tab s then tm else predicatify completish tm
      | _ => predicatify completish tm)
    val is_ho = is_type_enc_higher_order type_enc
    val is_full_ho = is_type_enc_full_higher_order type_enc
    val is_fool = is_type_enc_fool type_enc
    val do_iterm =
      (not is_ho ? introduce_app_ops)
      #> (not (is_full_ho orelse is_fool) ? introduce_predicators)
      #> filter_type_args_in_iterm thy ctrss type_enc
  in update_iformula (formula_map do_iterm) end

(** Helper facts **)

val not_ffalse = @{lemma "\<not> fFalse" by (unfold fFalse_def) fast}
val ftrue = @{lemma "fTrue" by (unfold fTrue_def) fast}

(* The Boolean indicates that a fairly sound type encoding is needed. *)
fun helper_table with_combs =
  (if with_combs then
    [(("COMBI", false), [(Non_Rec_Def, @{thm Meson.COMBI_def})]),
     (("COMBK", false), [(Non_Rec_Def, @{thm Meson.COMBK_def})]),
     (("COMBB", false), [(Non_Rec_Def, @{thm Meson.COMBB_def})]),
     (("COMBC", false), [(Non_Rec_Def, @{thm Meson.COMBC_def})]),
     (("COMBS", false), [(Non_Rec_Def, @{thm Meson.COMBS_def})])]
   else
     []) @
  [((predicator_name, false), [(General, not_ffalse), (General, ftrue)]),
   (("fFalse", false), [(General, not_ffalse)]),
   (("fFalse", true), [(General, @{thm True_or_False})]),
   (("fTrue", false), [(General, ftrue)]),
   (("fTrue", true), [(General, @{thm True_or_False})]),
   (("If", true),
    [(Non_Rec_Def, @{thm if_True}), (Non_Rec_Def, @{thm if_False}),
     (General, @{thm True_or_False})]),
   (("fNot", false),
    @{thms fNot_def [THEN Meson.iff_to_disjD, THEN conjunct1]
           fNot_def [THEN Meson.iff_to_disjD, THEN conjunct2]}
    |> map (pair Non_Rec_Def)),
   (("fconj", false),
    @{lemma "\<not> P \<or> \<not> Q \<or> fconj P Q" "\<not> fconj P Q \<or> P" "\<not> fconj P Q \<or> Q" by (unfold fconj_def) fast+}
    |> map (pair General)),
   (("fdisj", false),
    @{lemma "\<not> P \<or> fdisj P Q" "\<not> Q \<or> fdisj P Q" "\<not> fdisj P Q \<or> P \<or> Q" by (unfold fdisj_def) fast+}
    |> map (pair General)),
   (("fimplies", false),
    @{lemma "P \<or> fimplies P Q" "\<not> Q \<or> fimplies P Q" "\<not> fimplies P Q \<or> \<not> P \<or> Q"
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
   (("fAll", false), [(General, @{lemma "\<not> fAll P \<or> P x" by (auto simp: fAll_def)})]),
   (("fEx", false), [(General, @{lemma "\<not> P x \<or> fEx P" by (auto simp: fEx_def)})])]
  |> map (apsnd (map (apsnd zero_var_indexes)))

fun completish_helper_table with_combs =
  helper_table with_combs @
  [((predicator_name, true),
    @{thms True_or_False fTrue_ne_fFalse} |> map (pair General)),
   ((app_op_name, true),
    [(General, @{lemma "\<exists>x. \<not> f x = g x \<or> f = g" by blast}),
     (General, @{lemma "\<exists>p. (p x \<longleftrightarrow> p y) \<longrightarrow> x = y" by blast})]),
   (("fconj", false), @{thms fconj_table fconj_laws fdisj_laws} |> map (pair Non_Rec_Def)),
   (("fdisj", false), @{thms fdisj_table fconj_laws fdisj_laws} |> map (pair Non_Rec_Def)),
   (("fimplies", false),
    @{thms fimplies_table fconj_laws fdisj_laws fimplies_laws}
    |> map (pair Non_Rec_Def)),
   (("fequal", false),
    (@{thms fequal_table} |> map (pair Non_Rec_Def)) @
    (@{thms fequal_laws} |> map (pair General))),
   (("fAll", false), @{thms fAll_table fComp_law fAll_law fEx_law} |> map (pair Non_Rec_Def)),
   (("fEx", false), @{thms fEx_table fComp_law fAll_law fEx_law} |> map (pair Non_Rec_Def))]
  |> map (apsnd (map (apsnd zero_var_indexes)))

fun bound_tvars type_enc sorts Ts =
  (case filter is_TVar Ts of
    [] => I
  | Ts =>
    ((sorts andalso polymorphism_of_type_enc type_enc <> Type_Class_Polymorphic)
     ? mk_ahorn (Ts
       |> class_membs_of_types type_enc add_sorts_on_tvar
       |> map (class_atom type_enc)))
    #> (case type_enc of
         Native (_, _, Type_Class_Polymorphic, _) =>
         mk_atyquant AForall (map (fn TVar (z as (_, S)) =>
           (AType ((tvar_name z, []), []), map (`make_class) (normalize_classes S) )) Ts)
       | Native (_, _, Raw_Polymorphic _, _) =>
         mk_atyquant AForall (map (fn TVar (z as _) => (AType ((tvar_name z, []), []), [])) Ts)
       | _ => mk_aquant AForall (map (fn TVar z => (tvar_name z, NONE)) Ts)))

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
  not (is_type_enc_polymorphic type_enc) andalso level_of_type_enc type_enc <> No_Types

fun should_specialize_helper type_enc t =
  could_specialize_helpers type_enc andalso not (null (Term.hidden_polymorphism t))

fun add_helper_facts_of_sym ctxt format type_enc lam_trans completish (s, {types, ...} : sym_info) =
  (case unprefix_and_unascii const_prefix s of
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
          let val tyenv = Sign.typ_match thy (alpha_to_beta, domain_type T) Vartab.empty in
            Envir.subst_term_types tyenv t
          end
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
      val with_combs = lam_trans <> opaque_combsN
    in
      fold (fn ((helper_s, needs_sound), ths) =>
               if (needs_sound andalso not sound) orelse
                  (helper_s <> unmangled_s andalso
                   (completish < 3 orelse could_specialize)) then
                 I
               else
                 ths ~~ (1 upto length ths)
                 |> maps (dub_and_inst needs_sound o apfst (apsnd Thm.prop_of))
                 |> make_facts
                 |> union (op = o apply2 #iformula))
           ((if completish >= 3 then completish_helper_table else helper_table) with_combs)
    end
  | NONE => I)
fun helper_facts_of_sym_table ctxt format type_enc lam_trans completish sym_tab =
  Symtab.fold_rev (add_helper_facts_of_sym ctxt format type_enc lam_trans completish) sym_tab []

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

fun fold_type_ctrs f (Type (s, Ts)) x = fold (fold_type_ctrs f) Ts (f (s, x))
  | fold_type_ctrs _ _ x = x

(* Type constructors used to instantiate overloaded constants are the only ones
   needed. *)
fun add_type_ctrs_in_term thy =
  let
    fun add (Const (\<^const_name>\<open>Meson.skolem\<close>, _) $ _) = I
      | add (t $ u) = add t #> add u
      | add (Const x) =
        x |> robust_const_type_args thy |> fold (fold_type_ctrs set_insert)
      | add (Abs (_, _, u)) = add u
      | add _ = I
  in add end

fun type_ctrs_of_terms thy ts =
  Symtab.keys (fold (add_type_ctrs_in_term thy) ts Symtab.empty)

fun trans_lams_of_string ctxt type_enc lam_trans =
  if lam_trans = no_lamsN then
    rpair []
  else if lam_trans = opaque_liftingN then
    lift_lams ctxt type_enc ##> K []
  else if lam_trans = liftingN then
    lift_lams ctxt type_enc
  else if lam_trans = opaque_combsN orelse lam_trans = combsN then
    map (introduce_combinators ctxt type_enc) #> rpair []
  else if lam_trans = combs_and_liftingN then
    lift_lams_part_1 ctxt type_enc
    ##> maps (fn t => [t, introduce_combinators ctxt type_enc (intentionalize_def t)])
    #> lift_lams_part_2 ctxt type_enc
  else if lam_trans = combs_or_liftingN then
    lift_lams_part_1 ctxt type_enc
    ##> map (fn t => (case head_of (strip_qnt_body \<^const_name>\<open>All\<close> t) of
                       \<^term>\<open>(=) ::bool => bool => bool\<close> => t
                     | _ => introduce_combinators ctxt type_enc (intentionalize_def t)))
    #> lift_lams_part_2 ctxt type_enc
  else if lam_trans = keep_lamsN then
    map (Envir.eta_contract) #> rpair []
  else
    error ("Unknown lambda translation scheme: " ^ quote lam_trans)

val pull_and_reorder_definitions =
  let
    fun add_consts (IApp (t, u)) = fold add_consts [t, u]
      | add_consts (IAbs (_, t)) = add_consts t
      | add_consts (IConst (name, _, _)) = insert (op =) name
      | add_consts (IVar _) = I
    fun consts_of_hs l_or_r ({iformula, ...} : ifact) =
      (case iformula of
        AAtom (IApp (IApp (IConst _, t), u)) => add_consts (l_or_r (t, u)) []
      | _ => [])
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

fun s_not_prop (\<^const>\<open>Trueprop\<close> $ t) = \<^const>\<open>Trueprop\<close> $ s_not t
  | s_not_prop (\<^const>\<open>Pure.imp\<close> $ t $ \<^prop>\<open>False\<close>) = t
  | s_not_prop t = \<^const>\<open>Pure.imp\<close> $ t $ \<^prop>\<open>False\<close>

fun translate_formulas simp_options ctxt prem_role format type_enc lam_trans presimp hyp_ts concl_t
      facts =
  let
    val thy = Proof_Context.theory_of ctxt
    val trans_lams = trans_lams_of_string ctxt type_enc lam_trans
    val fact_ts = facts |> map snd
    (* Remove existing facts from the conjecture, as this can dramatically boost an ATP's
       performance (for some reason). *)
    val hyp_ts = hyp_ts |> map (fn t => if member (op aconv) fact_ts t then \<^prop>\<open>True\<close> else t)

    val hyp_ts = map freeze_term hyp_ts;
    val concl_t = freeze_term concl_t;

    val facts = facts |> map (apsnd (pair Axiom))
    val conjs =
      map (pair prem_role) hyp_ts @ [(Conjecture, s_not_prop concl_t)]
      |> map2 (pair o rpair (Local, General) o string_of_int) (0 upto length hyp_ts)
    val ((conjs, facts), lam_facts) =
      (conjs, facts)
      |> presimp ? apply2 (map (apsnd (apsnd (presimp_prop simp_options ctxt type_enc))))
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
      facts |> map_filter (fn (name, (_, t)) => make_fact ctxt format type_enc true (name, t))
            |> pull_and_reorder_definitions
    val lifted = lam_facts |> map (extract_lambda_def dest_Const o snd o snd)
    val lam_facts = lam_facts |> map_filter (make_fact ctxt format type_enc true o apsnd snd)
    val all_ts = concl_t :: hyp_ts @ fact_ts
    val subs = tfree_classes_of_terms all_ts
    val supers = tvar_classes_of_terms all_ts
    val tycons = type_ctrs_of_terms thy all_ts
    val (supers, tcon_clauses) =
      if level_of_type_enc type_enc = No_Types then ([], [])
      else make_tcon_clauses thy tycons supers
    val subclass_pairs = make_subclass_pairs thy subs supers
  in
    (union (op =) subs supers, conjs, facts @ lam_facts, subclass_pairs, tcon_clauses, lifted)
  end

val type_guard = `(make_fixed_const NONE) type_guard_name

fun type_guard_iterm type_enc T tm =
  IApp (IConst (type_guard, T --> \<^typ>\<open>bool\<close>, [T])
        |> mangle_type_args_in_iterm type_enc, tm)

fun is_var_positively_naked_in_term _ (SOME false) _ accum = accum
  | is_var_positively_naked_in_term name _ (ATerm (((s, _), _), tms)) accum =
    accum orelse (is_tptp_equal s andalso member (op =) tms (ATerm ((name, []), [])))
  | is_var_positively_naked_in_term _ _ _ _ = true

fun is_var_undercover_in_term thy name pos tm accum =
  accum orelse
  let
    val var = ATerm ((name, []), [])
    fun is_undercover (ATerm (_, [])) = false
      | is_undercover (ATerm (((s, _), _), tms)) =
        let
          val ary = length tms
          val cover = type_arg_cover thy pos s ary
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
    | Undercover_Types => formula_fold pos (is_var_undercover_in_term thy name) phi false
    | Nonmono_Types (_, Uniform) => true
    | Nonmono_Types (_, Non_Uniform) =>
      formula_fold pos (is_var_positively_naked_in_term name) phi false
    | _ => false)
  | should_guard_var_in_formula _ _ _ _ _ _ = true

fun always_guard_var_in_formula _ _ _ _ _ _ = true

fun should_generate_tag_bound_decl _ _ _ (SOME true) _ = false
  | should_generate_tag_bound_decl ctxt mono (Tags (_, level)) _ T =
    not (is_type_level_uniform level) andalso should_encode_type ctxt mono level T
  | should_generate_tag_bound_decl _ _ _ _ _ = false

fun mk_aterm type_enc name T_args args =
  let val (ty_args, tm_args) = process_type_args type_enc T_args in
    ATerm ((name, ty_args), tm_args @ args)
  end

fun do_bound_type type_enc =
  (case type_enc of
    Native _ => native_atp_type_of_typ type_enc false 0 #> SOME
  | _ => K NONE)

fun tag_with_type ctxt mono type_enc pos T tm =
  IConst (type_tag, T --> T, [T])
  |> mangle_type_args_in_iterm type_enc
  |> atp_term_of_iterm ctxt mono type_enc pos
  |> (fn ATerm ((s, tys), tms) => ATerm ((s, tys), tms @ [tm])
       | _ => raise Fail "unexpected lambda-abstraction")
and atp_term_of_iterm ctxt mono type_enc pos =
  let
    fun term site u =
      let
        val (head, args) = strip_iterm_comb u
        val pos = (case site of Top_Level pos => pos | Eq_Arg pos => pos | _ => NONE)
        val T = ityp_of u
        val t =
          (case head of
            IConst (name as (s, _), _, T_args) =>
            let
              val ary = length args
              fun arg_site j = if is_tptp_equal s then Eq_Arg pos else Arg (s, j, ary)
            in
              map2 (fn j => term (arg_site j)) (0 upto ary - 1) args
              |> mk_aterm type_enc name T_args
            end
          | IVar (name, _) =>
            map (term Elsewhere) args |> mk_aterm type_enc name []
          | IAbs ((name, T), tm) =>
            if is_type_enc_higher_order type_enc orelse is_type_enc_fool type_enc then
              AAbs (((name, native_atp_type_of_typ type_enc false 0 T), term Elsewhere tm),
                map (term Elsewhere) args)
            else
              raise Fail "unexpected lambda-abstraction"
          | IApp _ => raise Fail "impossible \"IApp\"")
        val tag = should_tag_with_type ctxt mono type_enc site u T
      in t |> tag ? tag_with_type ctxt mono type_enc pos T end
  in term (Top_Level pos) end
and formula_of_iformula ctxt mono type_enc should_guard_var =
  let
    val thy = Proof_Context.theory_of ctxt
    val level = level_of_type_enc type_enc
    val do_term = atp_term_of_iterm ctxt mono type_enc
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
        ATyQuant (q, map (apfst (native_atp_type_of_typ type_enc false 0)) xs, do_formula pos phi)
      | do_formula pos (AQuant (q, xs, phi)) =
        let
          val phi = phi |> do_formula pos
          val universal = Option.map (q = AExists ? not) pos
        in
          AQuant (q, xs |> map (apsnd (fn NONE => NONE
                                        | SOME T => do_bound_type type_enc T)),
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

fun string_of_status General = ""
  | string_of_status Induction = inductionN
  | string_of_status Intro = introN
  | string_of_status Inductive = inductiveN
  | string_of_status Elim = elimN
  | string_of_status Simp = simpN
  | string_of_status Non_Rec_Def = non_rec_defN
  | string_of_status Rec_Def = rec_defN

(* Each fact is given a unique fact number to avoid name clashes (e.g., because
   of monomorphization). The TPTP forbids name clashes, and some of the remote
   provers might care. *)
fun line_of_fact ctxt generate_info prefix encode alt freshen pos mono type_enc rank
        (j, {name, stature = (_, status), role, iformula, atomic_types}) =
  Formula ((prefix ^ (if freshen then string_of_int j ^ "_" else "") ^
            encode name, alt name),
           role,
           iformula
           |> formula_of_iformula ctxt mono type_enc
                  should_guard_var_in_formula (if pos then SOME true else NONE)
           |> close_formula_universally
           |> bound_tvars type_enc true atomic_types,
           NONE, isabelle_info generate_info (string_of_status status) (rank j))

fun lines_of_subclass generate_info type_enc sub super =
  Formula ((subclass_prefix ^ ascii_of sub ^ "___" ^ ascii_of super, ""), Axiom,
           AConn (AImplies,
                  [sub, super] |> map (fn s => class_atom type_enc (s, tvar_a)))
           |> bound_tvars type_enc false [tvar_a],
           NONE, isabelle_info generate_info inductiveN helper_rank)

fun lines_of_subclass_pair generate_info type_enc (sub, supers) =
  if polymorphism_of_type_enc type_enc = Type_Class_Polymorphic then
    [Class_Decl (class_decl_prefix ^ ascii_of sub, `make_class sub, map (`make_class) supers)]
  else
    map (lines_of_subclass generate_info type_enc sub) supers

fun line_of_tcon_clause generate_info type_enc (name, prems, (cl, T)) =
  if polymorphism_of_type_enc type_enc = Type_Class_Polymorphic then
    Class_Memb (class_memb_prefix ^ name,
      map (fn (cls, T) => (T |> dest_TVar |> tvar_name, map (`make_class) cls)) prems,
      native_atp_type_of_typ type_enc false 0 T, `make_class cl)
  else
    Formula ((tcon_clause_prefix ^ name, ""), Axiom,
             mk_ahorn (maps (class_atoms type_enc) prems)
                      (class_atom type_enc (cl, T))
             |> bound_tvars type_enc true (snd (dest_Type T)),
             NONE, isabelle_info generate_info inductiveN helper_rank)

fun line_of_conjecture ctxt mono type_enc ({name, role, iformula, atomic_types, ...} : ifact) =
  Formula ((conjecture_prefix ^ name, ""), role,
           iformula
           |> formula_of_iformula ctxt mono type_enc should_guard_var_in_formula (SOME false)
           |> close_formula_universally
           |> bound_tvars type_enc true atomic_types, NONE, [])

fun lines_of_free_types type_enc (facts : ifact list) =
  if is_type_enc_polymorphic type_enc then
    let
      val type_classes = (polymorphism_of_type_enc type_enc = Type_Class_Polymorphic)
      fun line j (cl, T) =
        if type_classes then
          Class_Memb (class_memb_prefix ^ string_of_int j, [],
            native_atp_type_of_typ type_enc false 0 T, `make_class cl)
        else
          Formula ((tfree_clause_prefix ^ string_of_int j, ""), Hypothesis,
            class_atom type_enc (cl, T), NONE, [])
      val membs =
        fold (union (op =)) (map #atomic_types facts) []
        |> class_membs_of_types type_enc add_sorts_on_tfree
    in
      map2 line (0 upto length membs - 1) membs
    end
  else
    []

(** Symbol declarations **)

fun decl_line_of_class phantoms s =
  let val name as (s, _) = `make_class s in
    Sym_Decl (sym_decl_prefix ^ s, name,
              APi ([tvar_a_name],
                   if phantoms = Without_Phantom_Type_Vars then
                     AFun (a_itself_atype, bool_atype)
                   else
                     bool_atype))
  end

fun decl_lines_of_classes type_enc =
  (case type_enc of
    Native (_, _, Raw_Polymorphic phantoms, _) => map (decl_line_of_class phantoms)
  | _ => K [])

fun sym_decl_table_of_facts thy type_enc sym_tab (conjs, facts, extra_tms) =
  let
    fun add_iterm_syms tm =
      let val (head, args) = strip_iterm_comb tm in
        (case head of
          IConst ((s, s'), T, T_args) =>
          let
            val (pred_sym, in_conj) =
              (case Symtab.lookup sym_tab s of
                SOME ({pred_sym, in_conj, ...} : sym_info) => (pred_sym, in_conj)
              | NONE => (false, false))
            val decl_sym =
              (case type_enc of Guards _ => not pred_sym | _ => true) andalso is_tptp_user_symbol s
          in
            if decl_sym then
              Symtab.map_default (s, [])
                (insert_type thy #3 (s', T_args, T, pred_sym, length args, in_conj))
            else
              I
          end
        | IAbs (_, tm) => add_iterm_syms tm
        | _ => I)
        #> fold add_iterm_syms args
      end
    val add_fact_syms = ifact_lift (formula_fold NONE (K add_iterm_syms))
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
        (* FIXME: make sure type arguments are filtered / clean up code *)
        val (s, s') =
          `(make_fixed_const NONE) \<^const_name>\<open>undefined\<close>
          |> (is_type_enc_mangling type_enc ? mangled_const_name type_enc [T])
      in
        Symtab.map_default (s, [])
                           (insert_type thy #3 (s', [T], T, false, 0, false))
      end
    fun add_TYPE_const () =
      let val (s, s') = TYPE_name in
        Symtab.map_default (s, [])
            (insert_type thy #3
                         (s', [tvar_a], \<^typ>\<open>'a itself\<close>, false, 0, false))
      end
  in
    Symtab.empty
    |> is_type_enc_sound type_enc
       ? (fold (fold add_fact_syms) [conjs, facts]
          #> fold add_iterm_syms extra_tms
          #> (case type_enc of
                Native (_, _, Raw_Polymorphic phantoms, _) =>
                phantoms = Without_Phantom_Type_Vars ? add_TYPE_const ()
              | Native _ => I
              | _ => fold add_undefined_const (var_types ())))
  end

(* We add "bool" in case the helper "True_or_False" is included later. *)
fun default_mono level completish =
  {maybe_finite_Ts = [\<^typ>\<open>bool\<close>],
   surely_infinite_Ts = (case level of Nonmono_Types (Strict, _) => [] | _ => known_infinite_types),
   maybe_nonmono_Ts = [if completish >= 3 then tvar_a else \<^typ>\<open>bool\<close>]}

(* This inference is described in section 4 of Blanchette et al., "Encoding
   monomorphic and polymorphic types", TACAS 2013. *)
fun add_iterm_mononotonicity_info ctxt level polarity tm
      (mono as {maybe_finite_Ts, surely_infinite_Ts, maybe_nonmono_Ts}) =
  let
    val thy = Proof_Context.theory_of ctxt

    fun update_mono T mono =
      (case level of
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
      | _ => mono)

    fun update_mono_rec (IConst ((_, s'), Type (_, [T, _]), _)) =
        if String.isPrefix \<^const_name>\<open>fequal\<close> s' then update_mono T else I
      | update_mono_rec (IApp (tm1, tm2)) = fold update_mono_rec [tm1, tm2]
      | update_mono_rec (IAbs (_, tm)) = update_mono_rec tm
      | update_mono_rec _ = I
  in
    mono |>
    (case tm of
      IApp (IApp (IConst ((s, _), Type (_, [T, _]), _), tm1), tm2) =>
      ((polarity <> SOME false andalso is_tptp_equal s
          andalso exists is_maybe_universal_var [tm1, tm2])
         ? update_mono T)
      #> fold update_mono_rec [tm1, tm2]
    | _ => update_mono_rec tm)
  end
fun add_fact_mononotonicity_info ctxt level ({role, iformula, ...} : ifact) =
  formula_fold (SOME (role <> Conjecture)) (add_iterm_mononotonicity_info ctxt level) iformula
fun mononotonicity_info_of_facts ctxt type_enc completish facts =
  let val level = level_of_type_enc type_enc in
    default_mono level completish
    |> is_type_level_monotonicity_based level
       ? fold (add_fact_mononotonicity_info ctxt level) facts
  end

fun fold_arg_types f (IApp (tm1, tm2)) =
    fold_arg_types f tm1 #> fold_term_types f tm2
  | fold_arg_types _ _ = I
and fold_term_types f tm = f (ityp_of tm) #> fold_arg_types f tm

fun add_iformula_monotonic_types ctxt mono type_enc =
  let
    val thy = Proof_Context.theory_of ctxt
    val level = level_of_type_enc type_enc
    val should_encode = should_encode_type ctxt mono level
    fun add_type T = not (should_encode T) ? insert_type thy I T
  in formula_fold NONE (K (fold_term_types add_type)) end

fun add_fact_monotonic_types ctxt mono type_enc =
  ifact_lift (add_iformula_monotonic_types ctxt mono type_enc)

fun monotonic_types_of_facts ctxt mono type_enc facts =
  let val level = level_of_type_enc type_enc in
    [] |> (is_type_enc_polymorphic type_enc andalso
           is_type_level_monotonicity_based level)
          ? fold (add_fact_monotonic_types ctxt mono type_enc) facts
  end

fun line_of_guards_mono_type ctxt generate_info mono type_enc T =
  Formula ((guards_sym_formula_prefix ^ ascii_of (mangled_type type_enc T), ""),
           Axiom,
           IConst (`make_bound_var "X", T, [])
           |> type_guard_iterm type_enc T
           |> AAtom
           |> formula_of_iformula ctxt mono type_enc always_guard_var_in_formula
                                  (SOME true)
           |> close_formula_universally
           |> bound_tvars type_enc true (atomic_types_of T),
           NONE, isabelle_info generate_info inductiveN helper_rank)

fun line_of_tags_mono_type ctxt generate_info mono type_enc T =
  let val x_var = ATerm ((`make_bound_var "X", []), []) in
    Formula ((tags_sym_formula_prefix ^ ascii_of (mangled_type type_enc T), ""), Axiom,
             eq_formula type_enc (atomic_types_of T) [] false
                  (tag_with_type ctxt mono type_enc NONE T x_var) x_var,
             NONE, isabelle_info generate_info non_rec_defN helper_rank)
  end

fun lines_of_mono_types ctxt generate_info mono type_enc =
  (case type_enc of
    Native _ => K []
  | Guards _ => map (line_of_guards_mono_type ctxt generate_info mono type_enc)
  | Tags _ => map (line_of_tags_mono_type ctxt generate_info mono type_enc))

fun decl_line_of_sym ctxt type_enc s (s', T_args, T, pred_sym, ary, _) =
  let
    val thy = Proof_Context.theory_of ctxt
    val (T, T_args) =
      if null T_args then
        (T, [])
      else
        (case unprefix_and_unascii const_prefix s of
          SOME s' =>
          let
            val s' = s' |> unmangled_invert_const
            val T = s' |> robust_const_type thy
          in (T, robust_const_type_args thy (s', T)) end
        | NONE => raise Fail "unexpected type arguments")
  in
    Sym_Decl (sym_decl_prefix ^ s, (s, s'),
      T |> native_atp_type_of_typ type_enc pred_sym ary
        |> not (null T_args) ? curry APi (map (tvar_name o dest_TVar) T_args))
  end

fun honor_conj_sym_role in_conj = (if in_conj then Hypothesis else Axiom, I)

fun line_of_guards_sym_decl ctxt generate_info mono type_enc n s j
    (s', T_args, T, _, ary, in_conj) =
  let
    val thy = Proof_Context.theory_of ctxt
    val (role, maybe_negate) = honor_conj_sym_role in_conj
    val (arg_Ts, res_T) = chop_fun ary T
    val bound_names = 1 upto ary |> map (`I o make_bound_var o string_of_int)
    val bounds =
      bound_names ~~ arg_Ts |> map (fn (name, T) => IConst (name, T, []))
    val bound_Ts =
      (case level_of_type_enc type_enc of
        All_Types => if null T_args then replicate ary NONE else map SOME arg_Ts
      | Undercover_Types =>
        let val cover = type_arg_cover thy NONE s ary in
          map2 (fn j => if member (op =) cover j then SOME else K NONE) (0 upto ary - 1) arg_Ts
        end
      | _ => replicate ary NONE)
  in
    Formula ((guards_sym_formula_prefix ^ s ^
              (if n > 1 then "_" ^ string_of_int j else ""), ""),
             role,
             IConst ((s, s'), T, T_args)
             |> fold (curry (IApp o swap)) bounds
             |> type_guard_iterm type_enc res_T
             |> AAtom |> mk_aquant AForall (bound_names ~~ bound_Ts)
             |> formula_of_iformula ctxt mono type_enc
                                    always_guard_var_in_formula (SOME true)
             |> close_formula_universally
             |> bound_tvars type_enc (n > 1) (atomic_types_of T)
             |> maybe_negate,
             NONE, isabelle_info generate_info inductiveN helper_rank)
  end

fun lines_of_tags_sym_decl ctxt generate_info mono type_enc n s
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
    val tag_with = tag_with_type ctxt mono type_enc NONE
    fun formula c =
      [Formula ((ident, ""), role, eq (tag_with res_T c) c, NONE,
                isabelle_info generate_info non_rec_defN helper_rank)]
  in
    if pred_sym orelse not (should_encode_type ctxt mono level res_T) then
      []
    else if level = Undercover_Types then
      let
        val cover = type_arg_cover thy NONE s ary
        fun maybe_tag (j, arg_T) = member (op =) cover j ? tag_with arg_T
        val bounds = bounds |> map2 maybe_tag (0 upto ary - 1 ~~ arg_Ts)
      in formula (cst bounds) end
    else
      formula (cst bounds)
  end

fun result_type_of_decl (_, _, T, _, ary, _) = chop_fun ary T |> snd

fun rationalize_decls thy (decls as decl :: (decls' as _ :: _)) =
    let
      val T = result_type_of_decl decl |> map_type_tvar (fn (z, _) => TVar (z, \<^sort>\<open>type\<close>))
    in
      if forall (type_generalization thy T o result_type_of_decl) decls' then [decl]
      else decls
    end
  | rationalize_decls _ decls = decls

fun lines_of_sym_decls ctxt generate_info mono type_enc (s, decls) =
  (case type_enc of
    Native _ => [decl_line_of_sym ctxt type_enc s (hd decls)]
  | Guards (_, level) =>
    let
      val thy = Proof_Context.theory_of ctxt
      val decls = decls |> rationalize_decls thy
      val n = length decls
      val decls = decls |> filter (should_encode_type ctxt mono level o result_type_of_decl)
    in
      (0 upto length decls - 1, decls)
      |-> map2 (line_of_guards_sym_decl ctxt generate_info mono type_enc n s)
    end
  | Tags (_, level) =>
    if is_type_level_uniform level then
      []
    else
      let val n = length decls in
        (0 upto n - 1 ~~ decls)
        |> maps (lines_of_tags_sym_decl ctxt generate_info mono type_enc n s)
      end)

fun lines_of_sym_decl_table ctxt generate_info mono type_enc mono_Ts sym_decl_tab =
  let
    val syms = sym_decl_tab |> Symtab.dest |> sort_by fst
    val mono_lines = lines_of_mono_types ctxt generate_info mono type_enc mono_Ts
    val decl_lines = maps (lines_of_sym_decls ctxt generate_info mono type_enc) syms
  in mono_lines @ decl_lines end

fun datatypes_of_sym_table ctxt ctrss (DFG Polymorphic) (type_enc as Native _) uncurried_aliases
      sym_tab =
    if is_type_enc_polymorphic type_enc then
      let
        val thy = Proof_Context.theory_of ctxt

        fun do_ctr (s, T) =
          let
            val s' = make_fixed_const (SOME type_enc) s
            val ary = ary_of T
            fun mk name = SOME (mk_aterm type_enc name (robust_const_type_args thy (s, T)) [])
          in
            if T = HOLogic.boolT then
              (case proxify_const s' of
                SOME proxy_base => mk (proxy_base |>> prefix const_prefix)
              | NONE => NONE)
            else
              (case Symtab.lookup sym_tab s' of
                NONE => NONE
              | SOME ({min_ary, ...} : sym_info) =>
                if ary = min_ary then mk (s', s)
                else if uncurried_aliases then mk (aliased_uncurried ary (s', s))
                else NONE)
          end

        fun datatype_of_ctrs (ctrs as (_, T1) :: _) =
          let val ctrs' = map do_ctr ctrs in
            (native_atp_type_of_typ type_enc false 0 (body_type T1), map_filter I ctrs',
             forall is_some ctrs')
          end
      in
        ctrss |> map datatype_of_ctrs |> filter #3
      end
    else
      []
  | datatypes_of_sym_table _ _ _ _ _ _ = []

fun decl_line_of_datatype (ty as AType (((_, s'), _), ty_args), ctrs, exhaust) =
  let val xs = map (fn AType ((name, _), []) => name) ty_args in
    Datatype_Decl (datatype_decl_prefix ^ ascii_of s', map (rpair []) xs, ty, ctrs, exhaust)
  end

fun pair_append (xs1, xs2) (ys1, ys2) = (xs1 @ ys1, xs2 @ ys2)

fun do_uncurried_alias_lines_of_sym ctxt generate_info ctrss mono type_enc sym_tab0 sym_tab base_s0
    types in_conj =
  let
    fun do_alias ary =
      let
        val thy = Proof_Context.theory_of ctxt
        val (role, maybe_negate) = honor_conj_sym_role in_conj
        val base_name = base_s0 |> `(make_fixed_const (SOME type_enc))
        val T = (case types of [T] => T | _ => robust_const_type thy base_s0)
        val T_args = robust_const_type_args thy (base_s0, T)
        val (base_name as (base_s, _), T_args) =
          mangle_type_args_in_const type_enc base_name T_args
        val base_ary = min_ary_of sym_tab0 base_s
        fun do_const name = IConst (name, T, T_args)
        val filter_ty_args = filter_type_args_in_iterm thy ctrss type_enc
        val atp_term_of = atp_term_of_iterm ctxt mono type_enc (SOME true)
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
        val eq =
          eq_formula type_enc (atomic_types_of T)
            (map (apsnd (do_bound_type type_enc)) bounds) false (atp_term_of tm1) (atp_term_of tm2)
      in
        ([tm1, tm2],
         [Formula ((uncurried_alias_eq_prefix ^ s2, ""), role, eq |> maybe_negate, NONE,
            isabelle_info generate_info non_rec_defN helper_rank)])
        |> (if ary - 1 = base_ary orelse Symtab.defined sym_tab s1 then I
            else pair_append (do_alias (ary - 1)))
      end
  in do_alias end

fun uncurried_alias_lines_of_sym ctxt generate_info ctrss mono type_enc sym_tab0 sym_tab
        (s, {min_ary, types, in_conj, ...} : sym_info) =
  (case unprefix_and_unascii const_prefix s of
    SOME mangled_s =>
    if String.isSubstring uncurried_alias_sep mangled_s then
      let val base_s0 = mangled_s |> unmangled_invert_const in
        do_uncurried_alias_lines_of_sym ctxt generate_info ctrss mono type_enc sym_tab0 sym_tab
          base_s0 types in_conj min_ary
      end
    else
      ([], [])
  | NONE => ([], []))

fun uncurried_alias_lines_of_sym_table ctxt generate_info ctrss mono type_enc uncurried_aliases
    sym_tab0 sym_tab =
  ([], [])
  |> uncurried_aliases
    ? Symtab.fold_rev (pair_append
        o uncurried_alias_lines_of_sym ctxt generate_info ctrss mono type_enc sym_tab0 sym_tab)
      sym_tab

val implicit_declsN = "Could-be-implicit typings"
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
    val do_bound_tvars = fold do_class o snd
    fun do_type (AType ((name, _), tys)) =
        apfst (apsnd (do_sym name (length tys))) #> fold do_type tys
      | do_type (AFun (ty1, ty2)) = do_type ty1 #> do_type ty2
      | do_type (APi (_, ty)) = do_type ty
    fun do_term pred_sym (ATerm ((name, tys), tms)) =
        apsnd (do_sym name (fn _ => default_type pred_sym (length tys) (length tms)))
        #> fold do_type tys #> fold (do_term false) tms
      | do_term _ (AAbs (((_, ty), tm), args)) =
        do_type ty #> do_term false tm #> fold (do_term false) args
    fun do_formula (ATyQuant (_, xs, phi)) =
        fold (do_type o fst) xs #> fold (fold do_class o snd) xs #> do_formula phi
      | do_formula (AQuant (_, xs, phi)) = fold do_type (map_filter snd xs) #> do_formula phi
      | do_formula (AConn (_, phis)) = fold do_formula phis
      | do_formula (AAtom tm) = do_term true tm
    fun do_line (Class_Decl (_, _, cls)) = fold do_class cls
      | do_line (Type_Decl _) = I
      | do_line (Sym_Decl (_, _, ty)) = do_type ty
      | do_line (Datatype_Decl (_, xs, ty, tms, _)) =
        fold do_bound_tvars xs #> do_type ty #> fold (do_term false) tms
      | do_line (Class_Memb (_, xs, ty, cl)) = fold do_bound_tvars xs #> do_type ty #> do_class cl
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
                    | (s, (cls, ())) => cons (Class_Decl (class_decl_prefix ^ s, cls, []))) cls [] @
      Symtab.fold (fn (_, (("", ""), _)) => I (* already declared *)
                    | (s, (ty, ary)) => cons (Type_Decl (type_decl_prefix ^ s, ty, ary))) tys [] @
      Symtab.fold (fn (_, (("", ""), _)) => I (* already declared *)
                    | (s, (sym, ty)) => cons (Sym_Decl (sym_decl_prefix ^ s, sym, ty ()))) syms []
  in (heading, decls) :: problem end

val all_ctrss_of_datatypes = map (map_filter (try dest_Const) o #ctrs) o Ctr_Sugar.ctr_sugars_of

val app_op_and_predicator_threshold = 45

fun generate_atp_problem ctxt generate_info format prem_role type_enc mode lam_trans
    uncurried_aliases readable_names presimp hyp_ts concl_t facts =
  let
    val thy = Proof_Context.theory_of ctxt
    val type_enc = type_enc |> adjust_type_enc format
    val completish = (case mode of Sledgehammer_Completish k => k | _ => 0)
    (* Forcing explicit applications is expensive for polymorphic encodings,
       because it takes only one existential variable ranging over "'a => 'b" to
       ruin everything. Hence we do it only if there are few facts (which is
       normally the case for "metis" and the minimizer). *)
    val app_op_level =
      if completish > 0 then
        Full_App_Op_And_Predicator
      else if length facts + length hyp_ts >= app_op_and_predicator_threshold then
        if is_type_enc_polymorphic type_enc then Min_App_Op else Sufficient_App_Op
      else
        Sufficient_App_Op_And_Predicator
    val lam_trans =
      if lam_trans = keep_lamsN andalso not (is_type_enc_full_higher_order type_enc) then liftingN
      else lam_trans
    val simp_options =
      let val simp = not (is_type_enc_fool type_enc) in
        {if_simps = simp, let_simps = simp}
      end
    val (classes, conjs, facts, subclass_pairs, tcon_clauses, lifted) =
      translate_formulas simp_options ctxt prem_role format type_enc lam_trans presimp hyp_ts
        concl_t facts
    val (_, sym_tab0) = sym_table_of_facts ctxt type_enc app_op_level conjs facts
    val mono = conjs @ facts |> mononotonicity_info_of_facts ctxt type_enc completish
    val ctrss = all_ctrss_of_datatypes ctxt
    fun firstorderize in_helper =
      firstorderize_fact thy ctrss type_enc (uncurried_aliases andalso not in_helper) completish
        sym_tab0
    val (conjs, facts) = (conjs, facts) |> apply2 (map (firstorderize false))
    val (ho_stuff, sym_tab) =
      sym_table_of_facts ctxt type_enc Min_App_Op conjs facts
    val (uncurried_alias_eq_tms, uncurried_alias_eq_lines) =
      uncurried_alias_lines_of_sym_table ctxt generate_info ctrss mono type_enc uncurried_aliases
        sym_tab0 sym_tab
    val (_, sym_tab) =
      (ho_stuff, sym_tab)
      |> fold (add_iterm_syms_to_sym_table ctxt Min_App_Op false false)
              uncurried_alias_eq_tms
    val helpers =
      sym_tab |> helper_facts_of_sym_table ctxt format type_enc lam_trans completish
              |> map (firstorderize true)
    val all_facts = helpers @ conjs @ facts
    val mono_Ts = monotonic_types_of_facts ctxt mono type_enc all_facts
    val datatypes = datatypes_of_sym_table ctxt ctrss format type_enc uncurried_aliases sym_tab
    val class_decl_lines = decl_lines_of_classes type_enc classes
    val sym_decl_lines =
      (conjs, helpers @ facts, uncurried_alias_eq_tms)
      |> sym_decl_table_of_facts thy type_enc sym_tab
      |> lines_of_sym_decl_table ctxt generate_info mono type_enc mono_Ts
    val datatype_decl_lines = map decl_line_of_datatype datatypes
    val decl_lines = class_decl_lines @ sym_decl_lines @ datatype_decl_lines
    val num_facts = length facts
    val freshen = mode <> Exporter andalso mode <> Translator
    val pos = mode <> Exporter
    val rank_of = rank_of_fact_num num_facts
    val fact_lines =
      map (line_of_fact ctxt generate_info fact_prefix ascii_of I freshen pos mono type_enc rank_of)
        (0 upto num_facts - 1 ~~ facts)
    val subclass_lines = maps (lines_of_subclass_pair generate_info type_enc) subclass_pairs
    val tcon_lines = map (line_of_tcon_clause generate_info type_enc) tcon_clauses
    val helper_lines =
      0 upto length helpers - 1 ~~ helpers
      |> map (line_of_fact ctxt generate_info helper_prefix I (K "") false true mono type_enc
        (K default_rank))
    val free_type_lines = lines_of_free_types type_enc (facts @ conjs)
    val conj_lines = map (line_of_conjecture ctxt mono type_enc) conjs
    (* Reordering these might confuse the proof reconstruction code. *)
    val problem =
      [(explicit_declsN, decl_lines),
       (uncurried_alias_eqsN, uncurried_alias_eq_lines),
       (factsN, fact_lines),
       (subclassesN, subclass_lines),
       (tconsN, tcon_lines),
       (helpersN, helper_lines),
       (free_typesN, free_type_lines),
       (conjsN, conj_lines)]
    val problem =
      problem
      |> (case format of
           CNF => ensure_cnf_problem
         | CNF_UEQ => filter_cnf_ueq_problem
         | FOF => I
         | _ => declare_undeclared_in_problem implicit_declsN)
    val (problem, pool) = problem |> nice_atp_problem readable_names format
    fun add_sym_ary (s, {min_ary, ...} : sym_info) = min_ary > 0 ? Symtab.insert (op =) (s, min_ary)
  in
    (problem, Option.map snd pool |> the_default Symtab.empty, lifted,
     Symtab.fold add_sym_ary sym_tab Symtab.empty)
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
        is_tptp_user_symbol s ? Symtab.default (s, weight) #> fold (add_term_weights weight) tms
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
    |> sort (prod_ord Real.compare string_ord o apply2 swap)
  end

(* Ugly hack: may make innocent victims (collateral damage) *)
fun may_be_app s args = String.isPrefix app_op_name s andalso length args = 2
fun may_be_predicator s =
  member (op =) [predicator_name, prefixed_predicator_name] s

fun strip_predicator (tm as ATerm ((s, _), [tm'])) = if may_be_predicator s then tm' else tm
  | strip_predicator tm = tm

fun make_head_roll (ATerm ((s, _), tms)) =
    if may_be_app s tms then make_head_roll (hd tms) ||> append (tl tms) else (s, tms)
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
  | strip_iff_etc (AConn (AIff, [phi1, phi2])) = apply2 strip_up_to_predicator (phi1, phi2)
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
            (case make_head_roll concl of
              (head, args as _ :: _) => fold (add_term_deps head) (hyps @ args)
            | _ => I)
          end
        else
          I
      | add_intro_deps _ _ = I
    fun add_atom_eq_deps (SOME true) (ATerm ((s, _), [lhs as _, rhs])) =
        if is_tptp_equal s then
          (case make_head_roll lhs of
            (head, args as _ :: _) => fold (add_term_deps head) (rhs :: args)
          | _ => I)
        else
          I
      | add_atom_eq_deps _ _ = I
    fun add_eq_deps pred (Formula (_, role, phi, _, info)) =
        if pred (role, info) then
          (case strip_iff_etc phi of
            ([lhs], rhs) =>
            (case make_head_roll lhs of
              (head, args as _ :: _) => fold (add_term_deps head) (rhs @ args)
            | _ => I)
          | _ => formula_fold (SOME (role <> Conjecture)) add_atom_eq_deps phi)
        else
          I
      | add_eq_deps _ _ = I
    fun has_status status (_, info) = extract_isabelle_status info = SOME status
    fun is_conj (role, _) = (role = Conjecture orelse role = Hypothesis)
    val graph =
      Graph.empty
      |> fold (fold (add_eq_deps (has_status non_rec_defN)) o snd) problem
      |> fold (fold (add_eq_deps (has_status rec_defN orf has_status simpN
                                  orf is_conj)) o snd) problem
      |> fold (fold (add_intro_deps (has_status inductiveN)) o snd) problem
      |> fold (fold (add_intro_deps (has_status introN)) o snd) problem
    fun next_weight w = if w + w <= max_term_order_weight then w + w else w + 1
    fun add_weights _ [] = I
      | add_weights weight syms =
        fold (AList.update (op =) o rpair weight) syms
        #> add_weights (next_weight weight)
               (fold (union (op =) o Graph.immediate_succs graph) syms [])
  in
    (* Sorting is not just for aesthetics: It specifies the precedence order for
       the term ordering (KBO or LPO), from smaller to larger values. *)
    [] |> add_weights 1 (Graph.minimals graph) |> sort (int_ord o apply2 snd)
  end

end;

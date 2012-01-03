(*  Title:      HOL/Tools/ATP/atp_translate.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Translation of HOL to FOL for Metis and Sledgehammer.
*)

signature ATP_TRANSLATE =
sig
  type ('a, 'b) ho_term = ('a, 'b) ATP_Problem.ho_term
  type connective = ATP_Problem.connective
  type ('a, 'b, 'c) formula = ('a, 'b, 'c) ATP_Problem.formula
  type atp_format = ATP_Problem.atp_format
  type formula_kind = ATP_Problem.formula_kind
  type 'a problem = 'a ATP_Problem.problem

  datatype locality =
    General | Helper | Induction | Intro | Elim | Simp | Local | Assum | Chained

  datatype polymorphism = Polymorphic | Raw_Monomorphic | Mangled_Monomorphic
  datatype soundness = Sound_Modulo_Infinity | Sound
  datatype granularity = All_Vars | Positively_Naked_Vars | Ghost_Type_Arg_Vars
  datatype type_level =
    All_Types |
    Noninf_Nonmono_Types of soundness * granularity |
    Fin_Nonmono_Types of granularity |
    Const_Arg_Types |
    No_Types
  type type_enc

  val type_tag_idempotence : bool Config.T
  val type_tag_arguments : bool Config.T
  val no_lamsN : string
  val hide_lamsN : string
  val lam_liftingN : string
  val combinatorsN : string
  val hybrid_lamsN : string
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
  val type_decl_prefix : string
  val sym_decl_prefix : string
  val guards_sym_formula_prefix : string
  val tags_sym_formula_prefix : string
  val fact_prefix : string
  val conjecture_prefix : string
  val helper_prefix : string
  val class_rel_clause_prefix : string
  val arity_clause_prefix : string
  val tfree_clause_prefix : string
  val lam_fact_prefix : string
  val typed_helper_suffix : string
  val untyped_helper_suffix : string
  val type_tag_idempotence_helper_name : string
  val predicator_name : string
  val app_op_name : string
  val type_guard_name : string
  val type_tag_name : string
  val simple_type_prefix : string
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
  val polymorphism_of_type_enc : type_enc -> polymorphism
  val level_of_type_enc : type_enc -> type_level
  val is_type_enc_quasi_sound : type_enc -> bool
  val is_type_enc_fairly_sound : type_enc -> bool
  val type_enc_from_string : soundness -> string -> type_enc
  val adjust_type_enc : atp_format -> type_enc -> type_enc
  val mk_aconns :
    connective -> ('a, 'b, 'c) formula list -> ('a, 'b, 'c) formula
  val unmangled_const : string -> string * (string, 'b) ho_term list
  val unmangled_const_name : string -> string
  val helper_table : ((string * bool) * thm list) list
  val trans_lams_from_string :
    Proof.context -> type_enc -> string -> term list -> term list * term list
  val factsN : string
  val prepare_atp_problem :
    Proof.context -> atp_format -> formula_kind -> formula_kind -> type_enc
    -> bool -> string -> bool -> bool -> term list -> term
    -> ((string * locality) * term) list
    -> string problem * string Symtab.table * (string * locality) list vector
       * (string * term) list * int Symtab.table
  val atp_problem_weights : string problem -> (string * real) list
end;

structure ATP_Translate : ATP_TRANSLATE =
struct

open ATP_Util
open ATP_Problem

type name = string * string

val type_tag_idempotence =
  Attrib.setup_config_bool @{binding atp_type_tag_idempotence} (K false)
val type_tag_arguments =
  Attrib.setup_config_bool @{binding atp_type_tag_arguments} (K false)

val no_lamsN = "no_lams" (* used internally; undocumented *)
val hide_lamsN = "hide_lams"
val lam_liftingN = "lam_lifting"
val combinatorsN = "combinators"
val hybrid_lamsN = "hybrid_lams"
val keep_lamsN = "keep_lams"

(* It's still unclear whether all TFF1 implementations will support type
   signatures such as "!>[A : $tType] : $o", with ghost type variables. *)
val avoid_first_order_ghost_type_vars = false

val bound_var_prefix = "B_"
val all_bound_var_prefix = "BA_"
val exist_bound_var_prefix = "BE_"
val schematic_var_prefix = "V_"
val fixed_var_prefix = "v_"
val tvar_prefix = "T_"
val tfree_prefix = "t_"
val const_prefix = "c_"
val type_const_prefix = "tc_"
val simple_type_prefix = "s_"
val class_prefix = "cl_"

(* Freshness almost guaranteed! *)
val atp_weak_prefix = "ATP:"

val lam_lifted_prefix = atp_weak_prefix ^ "Lam"
val lam_lifted_mono_prefix = lam_lifted_prefix ^ "m"
val lam_lifted_poly_prefix = lam_lifted_prefix ^ "p"

val skolem_const_prefix = "ATP" ^ Long_Name.separator ^ "Sko"
val old_skolem_const_prefix = skolem_const_prefix ^ "o"
val new_skolem_const_prefix = skolem_const_prefix ^ "n"

val combinator_prefix = "COMB"

val type_decl_prefix = "ty_"
val sym_decl_prefix = "sy_"
val guards_sym_formula_prefix = "gsy_"
val tags_sym_formula_prefix = "tsy_"
val fact_prefix = "fact_"
val conjecture_prefix = "conj_"
val helper_prefix = "help_"
val class_rel_clause_prefix = "clar_"
val arity_clause_prefix = "arity_"
val tfree_clause_prefix = "tfree_"

val lam_fact_prefix = "ATP.lambda_"
val typed_helper_suffix = "_T"
val untyped_helper_suffix = "_U"
val type_tag_idempotence_helper_name = helper_prefix ^ "ti_idem"

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
    fun un rcs [] = String.implode(rev rcs)
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

fun make_schematic_type_var (x, i) =
  tvar_prefix ^ (ascii_of_indexname (unprefix "'" x, i))
fun make_fixed_type_var x = tfree_prefix ^ (ascii_of (unprefix "'" x))

(* "HOL.eq" and choice are mapped to the ATP's equivalents *)
local
  val choice_const = (fst o dest_Const o HOLogic.choice_const) Term.dummyT
  fun default c = const_prefix ^ lookup_const c
in
  fun make_fixed_const _ @{const_name HOL.eq} = tptp_old_equal
    | make_fixed_const (SOME (THF (_, _, THF_With_Choice))) c =
      if c = choice_const then tptp_choice else default c
    | make_fixed_const _ c = default c
end

fun make_fixed_type_const c = type_const_prefix ^ lookup_const c

fun make_type_class clas = class_prefix ^ ascii_of clas

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

(** Definitions and functions for FOL clauses and formulas for TPTP **)

(** Isabelle arities **)

type arity_atom = name * name * name list

val type_class = the_single @{sort type}

type arity_clause =
  {name : string,
   prem_atoms : arity_atom list,
   concl_atom : arity_atom}

fun add_prem_atom tvar =
  fold (fn s => s <> type_class ? cons (`make_type_class s, `I tvar, []))

(* Arity of type constructor "tcon :: (arg1, ..., argN) res" *)
fun make_axiom_arity_clause (tcons, name, (cls, args)) =
  let
    val tvars = map (prefix tvar_prefix o string_of_int) (1 upto length args)
    val tvars_srts = ListPair.zip (tvars, args)
  in
    {name = name,
     prem_atoms = [] |> fold (uncurry add_prem_atom) tvars_srts,
     concl_atom = (`make_type_class cls, `make_fixed_type_const tcons,
                   tvars ~~ tvars)}
  end

fun arity_clause _ _ (_, []) = []
  | arity_clause seen n (tcons, ("HOL.type", _) :: ars) =  (* ignore *)
    arity_clause seen n (tcons, ars)
  | arity_clause seen n (tcons, (ar as (class, _)) :: ars) =
    if member (op =) seen class then
      (* multiple arities for the same (tycon, class) pair *)
      make_axiom_arity_clause (tcons,
          lookup_const tcons ^ "___" ^ ascii_of class ^ "_" ^ string_of_int n,
          ar) ::
      arity_clause seen (n + 1) (tcons, ars)
    else
      make_axiom_arity_clause (tcons, lookup_const tcons ^ "___" ^
                               ascii_of class, ar) ::
      arity_clause (class :: seen) n (tcons, ars)

fun multi_arity_clause [] = []
  | multi_arity_clause ((tcons, ars) :: tc_arlists) =
    arity_clause [] 1 (tcons, ars) @ multi_arity_clause tc_arlists

(* Generate all pairs (tycon, class, sorts) such that tycon belongs to class in
   theory thy provided its arguments have the corresponding sorts. *)
fun type_class_pairs thy tycons classes =
  let
    val alg = Sign.classes_of thy
    fun domain_sorts tycon = Sorts.mg_domain alg tycon o single
    fun add_class tycon class =
      cons (class, domain_sorts tycon class)
      handle Sorts.CLASS_ERROR _ => I
    fun try_classes tycon = (tycon, fold (add_class tycon) classes [])
  in map try_classes tycons end

(*Proving one (tycon, class) membership may require proving others, so iterate.*)
fun iter_type_class_pairs _ _ [] = ([], [])
  | iter_type_class_pairs thy tycons classes =
      let
        fun maybe_insert_class s =
          (s <> type_class andalso not (member (op =) classes s))
          ? insert (op =) s
        val cpairs = type_class_pairs thy tycons classes
        val newclasses =
          [] |> fold (fold (fold (fold maybe_insert_class) o snd) o snd) cpairs
        val (classes', cpairs') = iter_type_class_pairs thy tycons newclasses
      in (classes' @ classes, union (op =) cpairs' cpairs) end

fun make_arity_clauses thy tycons =
  iter_type_class_pairs thy tycons ##> multi_arity_clause


(** Isabelle class relations **)

type class_rel_clause =
  {name : string,
   subclass : name,
   superclass : name}

(* Generate all pairs (sub, super) such that sub is a proper subclass of super
   in theory "thy". *)
fun class_pairs _ [] _ = []
  | class_pairs thy subs supers =
      let
        val class_less = Sorts.class_less (Sign.classes_of thy)
        fun add_super sub super = class_less (sub, super) ? cons (sub, super)
        fun add_supers sub = fold (add_super sub) supers
      in fold add_supers subs [] end

fun make_class_rel_clause (sub, super) =
  {name = sub ^ "_" ^ super, subclass = `make_type_class sub,
   superclass = `make_type_class super}

fun make_class_rel_clauses thy subs supers =
  map make_class_rel_clause (class_pairs thy subs supers)

(* intermediate terms *)
datatype iterm =
  IConst of name * typ * typ list |
  IVar of name * typ |
  IApp of iterm * iterm |
  IAbs of (name * typ) * iterm

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

val tvar_a_str = "'a"
val tvar_a = TVar ((tvar_a_str, 0), HOLogic.typeS)
val tvar_a_name = (make_schematic_type_var (tvar_a_str, 0), tvar_a_str)
val itself_name = `make_fixed_type_const @{type_name itself}
val TYPE_name = `(make_fixed_const NONE) @{const_name TYPE}
val tvar_a_atype = AType (tvar_a_name, [])
val a_itself_atype = AType (itself_name, [tvar_a_atype])

fun new_skolem_const_name s num_T_args =
  [new_skolem_const_prefix, s, string_of_int num_T_args]
  |> space_implode Long_Name.separator

fun robust_const_type thy s =
  if s = app_op_name then
    Logic.varifyT_global @{typ "('a => 'b) => 'a => 'b"}
  else if String.isPrefix lam_lifted_prefix s then
    Logic.varifyT_global @{typ "'a => 'b"}
  else
    (* Old Skolems throw a "TYPE" exception here, which will be caught. *)
    s |> Sign.the_const_type thy

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
fun iterm_from_term thy format bs (P $ Q) =
    let
      val (P', P_atomics_Ts) = iterm_from_term thy format bs P
      val (Q', Q_atomics_Ts) = iterm_from_term thy format bs Q
    in (IApp (P', Q'), union (op =) P_atomics_Ts Q_atomics_Ts) end
  | iterm_from_term thy format _ (Const (c, T)) =
    (IConst (`(make_fixed_const (SOME format)) c, T,
             robust_const_typargs thy (c, T)),
     atomic_types_of T)
  | iterm_from_term _ _ _ (Free (s, T)) =
    (IConst (`make_fixed_var s, T, []), atomic_types_of T)
  | iterm_from_term _ format _ (Var (v as (s, _), T)) =
    (if String.isPrefix Meson_Clausify.new_skolem_var_prefix s then
       let
         val Ts = T |> strip_type |> swap |> op ::
         val s' = new_skolem_const_name s (length Ts)
       in IConst (`(make_fixed_const (SOME format)) s', T, Ts) end
     else
       IVar ((make_schematic_var v, s), T), atomic_types_of T)
  | iterm_from_term _ _ bs (Bound j) =
    nth bs j |> (fn (_, (name, T)) => (IConst (name, T, []), atomic_types_of T))
  | iterm_from_term thy format bs (Abs (s, T, t)) =
    let
      fun vary s = s |> AList.defined (op =) bs s ? vary o Symbol.bump_string
      val s = vary s
      val name = `make_bound_var s
      val (tm, atomic_Ts) = iterm_from_term thy format ((s, (name, T)) :: bs) t
    in (IAbs ((name, T), tm), union (op =) atomic_Ts (atomic_types_of T)) end

datatype locality =
  General | Helper | Induction | Intro | Elim | Simp | Local | Assum | Chained

datatype order = First_Order | Higher_Order
datatype polymorphism = Polymorphic | Raw_Monomorphic | Mangled_Monomorphic
datatype soundness = Sound_Modulo_Infinity | Sound
datatype granularity = All_Vars | Positively_Naked_Vars | Ghost_Type_Arg_Vars
datatype type_level =
  All_Types |
  Noninf_Nonmono_Types of soundness * granularity |
  Fin_Nonmono_Types of granularity |
  Const_Arg_Types |
  No_Types

datatype type_enc =
  Simple_Types of order * polymorphism * type_level |
  Guards of polymorphism * type_level |
  Tags of polymorphism * type_level

fun is_type_enc_higher_order (Simple_Types (Higher_Order, _, _)) = true
  | is_type_enc_higher_order _ = false

fun polymorphism_of_type_enc (Simple_Types (_, poly, _)) = poly
  | polymorphism_of_type_enc (Guards (poly, _)) = poly
  | polymorphism_of_type_enc (Tags (poly, _)) = poly

fun level_of_type_enc (Simple_Types (_, _, level)) = level
  | level_of_type_enc (Guards (_, level)) = level
  | level_of_type_enc (Tags (_, level)) = level

fun granularity_of_type_level (Noninf_Nonmono_Types (_, grain)) = grain
  | granularity_of_type_level (Fin_Nonmono_Types grain) = grain
  | granularity_of_type_level _ = All_Vars

fun is_type_level_quasi_sound All_Types = true
  | is_type_level_quasi_sound (Noninf_Nonmono_Types _) = true
  | is_type_level_quasi_sound _ = false
val is_type_enc_quasi_sound = is_type_level_quasi_sound o level_of_type_enc

fun is_type_level_fairly_sound (Fin_Nonmono_Types _) = true
  | is_type_level_fairly_sound level = is_type_level_quasi_sound level
val is_type_enc_fairly_sound = is_type_level_fairly_sound o level_of_type_enc

fun is_type_level_monotonicity_based (Noninf_Nonmono_Types _) = true
  | is_type_level_monotonicity_based (Fin_Nonmono_Types _) = true
  | is_type_level_monotonicity_based _ = false

(* "_query", "_bang", and "_at" are for the ASCII-challenged Metis and
   Mirabelle. *)
val queries = ["?", "_query"]
val bangs = ["!", "_bang"]
val ats = ["@", "_at"]

fun try_unsuffixes ss s =
  fold (fn s' => fn NONE => try (unsuffix s') s | some => some) ss NONE

fun try_nonmono constr suffixes fallback s =
  case try_unsuffixes suffixes s of
    SOME s =>
    (case try_unsuffixes suffixes s of
       SOME s => (constr Positively_Naked_Vars, s)
     | NONE =>
       case try_unsuffixes ats s of
         SOME s => (constr Ghost_Type_Arg_Vars, s)
       | NONE => (constr All_Vars, s))
  | NONE => fallback s

fun type_enc_from_string soundness s =
  (case try (unprefix "poly_") s of
     SOME s => (SOME Polymorphic, s)
   | NONE =>
     case try (unprefix "raw_mono_") s of
       SOME s => (SOME Raw_Monomorphic, s)
     | NONE =>
       case try (unprefix "mono_") s of
         SOME s => (SOME Mangled_Monomorphic, s)
       | NONE => (NONE, s))
  ||> (pair All_Types
       |> try_nonmono Fin_Nonmono_Types bangs
       |> try_nonmono (curry Noninf_Nonmono_Types soundness) queries)
  |> (fn (poly, (level, core)) =>
         case (core, (poly, level)) of
           ("simple", (SOME poly, _)) =>
           (case (poly, level) of
              (Polymorphic, All_Types) =>
              Simple_Types (First_Order, Polymorphic, All_Types)
            | (Mangled_Monomorphic, _) =>
              if granularity_of_type_level level = All_Vars then
                Simple_Types (First_Order, Mangled_Monomorphic, level)
              else
                raise Same.SAME
            | _ => raise Same.SAME)
         | ("simple_higher", (SOME poly, _)) =>
           (case (poly, level) of
              (Polymorphic, All_Types) =>
              Simple_Types (Higher_Order, Polymorphic, All_Types)
            | (_, Noninf_Nonmono_Types _) => raise Same.SAME
            | (Mangled_Monomorphic, _) =>
              if granularity_of_type_level level = All_Vars then
                Simple_Types (Higher_Order, Mangled_Monomorphic, level)
              else
                raise Same.SAME
            | _ => raise Same.SAME)
         | ("guards", (SOME poly, _)) =>
           if poly = Mangled_Monomorphic andalso
              granularity_of_type_level level = Ghost_Type_Arg_Vars then
             raise Same.SAME
           else
             Guards (poly, level)
         | ("tags", (SOME poly, _)) =>
           if granularity_of_type_level level = Ghost_Type_Arg_Vars then
             raise Same.SAME
           else
             Tags (poly, level)
         | ("args", (SOME poly, All_Types (* naja *))) =>
           Guards (poly, Const_Arg_Types)
         | ("erased", (NONE, All_Types (* naja *))) =>
           Guards (Polymorphic, No_Types)
         | _ => raise Same.SAME)
  handle Same.SAME => error ("Unknown type encoding: " ^ quote s ^ ".")

fun adjust_type_enc (THF (TPTP_Monomorphic, _, _))
                    (Simple_Types (order, _, level)) =
    Simple_Types (order, Mangled_Monomorphic, level)
  | adjust_type_enc (THF _) type_enc = type_enc
  | adjust_type_enc (TFF (TPTP_Monomorphic, _)) (Simple_Types (_, _, level)) =
    Simple_Types (First_Order, Mangled_Monomorphic, level)
  | adjust_type_enc (DFG DFG_Sorted) (Simple_Types (_, _, level)) =
    Simple_Types (First_Order, Mangled_Monomorphic, level)
  | adjust_type_enc (TFF _) (Simple_Types (_, poly, level)) =
    Simple_Types (First_Order, poly, level)
  | adjust_type_enc format (Simple_Types (_, poly, level)) =
    adjust_type_enc format (Guards (poly, level))
  | adjust_type_enc CNF_UEQ (type_enc as Guards stuff) =
    (if is_type_enc_fairly_sound type_enc then Tags else Guards) stuff
  | adjust_type_enc _ type_enc = type_enc

fun constify_lifted (t $ u) = constify_lifted t $ constify_lifted u
  | constify_lifted (Abs (s, T, t)) = Abs (s, T, constify_lifted t)
  | constify_lifted (Free (x as (s, _))) =
    (if String.isPrefix lam_lifted_prefix s then Const else Free) x
  | constify_lifted t = t

(* Requires bound variables not to clash with any schematic variables (as should
   be the case right after lambda-lifting). *)
fun open_form (Const (@{const_name All}, _) $ Abs (s, T, t)) =
    let
      val names = Name.make_context (map fst (Term.add_var_names t []))
      val (s, _) = Name.variant s names
    in open_form (subst_bound (Var ((s, 0), T), t)) end
  | open_form t = t

fun lift_lams_part_1 ctxt type_enc =
  map close_form #> rpair ctxt
  #-> Lambda_Lifting.lift_lambdas
          (SOME ((if polymorphism_of_type_enc type_enc = Polymorphic then
                    lam_lifted_poly_prefix
                  else
                    lam_lifted_mono_prefix) ^ "_a"))
          Lambda_Lifting.is_quantifier
  #> fst
val lift_lams_part_2 = pairself (map (open_form o constify_lifted))
val lift_lams = lift_lams_part_2 ooo lift_lams_part_1

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

type translated_formula =
  {name : string,
   locality : locality,
   kind : formula_kind,
   iformula : (name, typ, iterm) formula,
   atomic_types : typ list}

fun update_iformula f ({name, locality, kind, iformula, atomic_types}
                       : translated_formula) =
  {name = name, locality = locality, kind = kind, iformula = f iformula,
   atomic_types = atomic_types} : translated_formula

fun fact_lift f ({iformula, ...} : translated_formula) = f iformula

fun insert_type ctxt get_T x xs =
  let val T = get_T x in
    if exists (type_instance ctxt T o get_T) xs then xs
    else x :: filter_out (type_generalization ctxt T o get_T) xs
  end

(* The Booleans indicate whether all type arguments should be kept. *)
datatype type_arg_policy =
  Explicit_Type_Args of bool (* infer_from_term_args *) |
  Mangled_Type_Args |
  No_Type_Args

fun type_arg_policy monom_constrs type_enc s =
  let val poly = polymorphism_of_type_enc type_enc in
    if s = type_tag_name then
      if poly = Mangled_Monomorphic then Mangled_Type_Args
      else Explicit_Type_Args false
    else case type_enc of
      Simple_Types (_, Polymorphic, _) => Explicit_Type_Args false
    | Tags (_, All_Types) => No_Type_Args
    | _ =>
      let val level = level_of_type_enc type_enc in
        if level = No_Types orelse s = @{const_name HOL.eq} orelse
           (s = app_op_name andalso level = Const_Arg_Types) then
          No_Type_Args
        else if poly = Mangled_Monomorphic then
          Mangled_Type_Args
        else if member (op =) monom_constrs s andalso
                granularity_of_type_level level = Positively_Naked_Vars then
          No_Type_Args
        else
          Explicit_Type_Args
              (level = All_Types orelse
               granularity_of_type_level level = Ghost_Type_Arg_Vars)
      end
  end

(* Make atoms for sorted type variables. *)
fun generic_add_sorts_on_type (_, []) = I
  | generic_add_sorts_on_type ((x, i), s :: ss) =
    generic_add_sorts_on_type ((x, i), ss)
    #> (if s = the_single @{sort HOL.type} then
          I
        else if i = ~1 then
          insert (op =) (`make_type_class s, `make_fixed_type_var x)
        else
          insert (op =) (`make_type_class s,
                         (make_schematic_type_var (x, i), x)))
fun add_sorts_on_tfree (TFree (s, S)) = generic_add_sorts_on_type ((s, ~1), S)
  | add_sorts_on_tfree _ = I
fun add_sorts_on_tvar (TVar z) = generic_add_sorts_on_type z
  | add_sorts_on_tvar _ = I

fun type_class_formula type_enc class arg =
  AAtom (ATerm (class, arg ::
      (case type_enc of
         Simple_Types (First_Order, Polymorphic, _) =>
         if avoid_first_order_ghost_type_vars then [ATerm (TYPE_name, [arg])]
         else []
       | _ => [])))
fun formulas_for_types type_enc add_sorts_on_typ Ts =
  [] |> level_of_type_enc type_enc <> No_Types ? fold add_sorts_on_typ Ts
     |> map (fn (class, name) =>
                type_class_formula type_enc class (ATerm (name, [])))

fun mk_aconns c phis =
  let val (phis', phi') = split_last phis in
    fold_rev (mk_aconn c) phis' phi'
  end
fun mk_ahorn [] phi = phi
  | mk_ahorn phis psi = AConn (AImplies, [mk_aconns AAnd phis, psi])
fun mk_aquant _ [] phi = phi
  | mk_aquant q xs (phi as AQuant (q', xs', phi')) =
    if q = q' then AQuant (q, xs @ xs', phi') else AQuant (q, xs, phi)
  | mk_aquant q xs phi = AQuant (q, xs, phi)

fun close_universally add_term_vars phi =
  let
    fun add_formula_vars bounds (AQuant (_, xs, phi)) =
        add_formula_vars (map fst xs @ bounds) phi
      | add_formula_vars bounds (AConn (_, phis)) =
        fold (add_formula_vars bounds) phis
      | add_formula_vars bounds (AAtom tm) = add_term_vars bounds tm
  in mk_aquant AForall (add_formula_vars [] phi []) phi end

fun add_term_vars bounds (ATerm (name as (s, _), tms)) =
    (if is_tptp_variable s andalso
        not (String.isPrefix tvar_prefix s) andalso
        not (member (op =) bounds name) then
       insert (op =) (name, NONE)
     else
       I)
    #> fold (add_term_vars bounds) tms
  | add_term_vars bounds (AAbs ((name, _), tm)) =
    add_term_vars (name :: bounds) tm
fun close_formula_universally phi = close_universally add_term_vars phi

fun add_iterm_vars bounds (IApp (tm1, tm2)) =
    fold (add_iterm_vars bounds) [tm1, tm2]
  | add_iterm_vars _ (IConst _) = I
  | add_iterm_vars bounds (IVar (name, T)) =
    not (member (op =) bounds name) ? insert (op =) (name, SOME T)
  | add_iterm_vars bounds (IAbs (_, tm)) = add_iterm_vars bounds tm
fun close_iformula_universally phi = close_universally add_iterm_vars phi

val fused_infinite_type_name = @{type_name ind} (* any infinite type *)
val fused_infinite_type = Type (fused_infinite_type_name, [])

fun tvar_name (x as (s, _)) = (make_schematic_type_var x, s)

fun ho_term_from_typ format type_enc =
  let
    fun term (Type (s, Ts)) =
      ATerm (case (is_type_enc_higher_order type_enc, s) of
               (true, @{type_name bool}) => `I tptp_bool_type
             | (true, @{type_name fun}) => `I tptp_fun_type
             | _ => if s = fused_infinite_type_name andalso
                       is_format_typed format then
                      `I tptp_individual_type
                    else
                      `make_fixed_type_const s,
             map term Ts)
    | term (TFree (s, _)) = ATerm (`make_fixed_type_var s, [])
    | term (TVar (x, _)) = ATerm (tvar_name x, [])
  in term end

fun ho_term_for_type_arg format type_enc T =
  if T = dummyT then NONE else SOME (ho_term_from_typ format type_enc T)

(* This shouldn't clash with anything else. *)
val mangled_type_sep = "\000"

fun generic_mangled_type_name f (ATerm (name, [])) = f name
  | generic_mangled_type_name f (ATerm (name, tys)) =
    f name ^ "(" ^ space_implode "," (map (generic_mangled_type_name f) tys)
    ^ ")"
  | generic_mangled_type_name _ _ = raise Fail "unexpected type abstraction"

fun mangled_type format type_enc =
  generic_mangled_type_name fst o ho_term_from_typ format type_enc

fun make_simple_type s =
  if s = tptp_bool_type orelse s = tptp_fun_type orelse
     s = tptp_individual_type then
    s
  else
    simple_type_prefix ^ ascii_of s

fun ho_type_from_ho_term type_enc pred_sym ary =
  let
    fun to_mangled_atype ty =
      AType ((make_simple_type (generic_mangled_type_name fst ty),
              generic_mangled_type_name snd ty), [])
    fun to_poly_atype (ATerm (name, tys)) = AType (name, map to_poly_atype tys)
      | to_poly_atype _ = raise Fail "unexpected type abstraction"
    val to_atype =
      if polymorphism_of_type_enc type_enc = Polymorphic then to_poly_atype
      else to_mangled_atype
    fun to_afun f1 f2 tys = AFun (f1 (hd tys), f2 (nth tys 1))
    fun to_fo 0 ty = if pred_sym then bool_atype else to_atype ty
      | to_fo ary (ATerm (_, tys)) = to_afun to_atype (to_fo (ary - 1)) tys
      | to_fo _ _ = raise Fail "unexpected type abstraction"
    fun to_ho (ty as ATerm ((s, _), tys)) =
        if s = tptp_fun_type then to_afun to_ho to_ho tys else to_atype ty
      | to_ho _ = raise Fail "unexpected type abstraction"
  in if is_type_enc_higher_order type_enc then to_ho else to_fo ary end

fun ho_type_from_typ format type_enc pred_sym ary =
  ho_type_from_ho_term type_enc pred_sym ary
  o ho_term_from_typ format type_enc

fun mangled_const_name format type_enc T_args (s, s') =
  let
    val ty_args = T_args |> map_filter (ho_term_for_type_arg format type_enc)
    fun type_suffix f g =
      fold_rev (curry (op ^) o g o prefix mangled_type_sep
                o generic_mangled_type_name f) ty_args ""
  in (s ^ type_suffix fst ascii_of, s' ^ type_suffix snd I) end

val parse_mangled_ident =
  Scan.many1 (not o member (op =) ["(", ")", ","]) >> implode

fun parse_mangled_type x =
  (parse_mangled_ident
   -- Scan.optional ($$ "(" |-- Scan.optional parse_mangled_types [] --| $$ ")")
                    [] >> ATerm) x
and parse_mangled_types x =
  (parse_mangled_type ::: Scan.repeat ($$ "," |-- parse_mangled_type)) x

fun unmangled_type s =
  s |> suffix ")" |> raw_explode
    |> Scan.finite Symbol.stopper
           (Scan.error (!! (fn _ => raise Fail ("unrecognized mangled type " ^
                                                quote s)) parse_mangled_type))
    |> fst

val unmangled_const_name = space_explode mangled_type_sep #> hd
fun unmangled_const s =
  let val ss = space_explode mangled_type_sep s in
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
               if is_tptp_equal s andalso length args = 2 then
                 IConst (`I tptp_equal, T, [])
               else
                 (* Use a proxy even for partially applied THF0 equality,
                    because the LEO-II and Satallax parsers complain about not
                    being able to infer the type of "=". *)
                 IConst (proxy_base |>> prefix const_prefix, T, T_args)
             | _ => IConst (name, T, [])
           else
             IConst (proxy_base |>> prefix const_prefix, T, T_args)
          | NONE => if s = tptp_choice then tweak_ho_quant tptp_choice T args
                    else IConst (name, T, T_args))
      | intro _ _ (IAbs (bound, tm)) = IAbs (bound, intro false [] tm)
      | intro _ _ tm = tm
  in intro true [] end

fun mangle_type_args_in_iterm format type_enc =
  if polymorphism_of_type_enc type_enc = Mangled_Monomorphic then
    let
      fun mangle (IApp (tm1, tm2)) = IApp (mangle tm1, mangle tm2)
        | mangle (tm as IConst (_, _, [])) = tm
        | mangle (tm as IConst (name as (s, _), T, T_args)) =
          (case unprefix_and_unascii const_prefix s of
             NONE => tm
           | SOME s'' =>
             case type_arg_policy [] type_enc (invert_const s'') of
               Mangled_Type_Args =>
               IConst (mangled_const_name format type_enc T_args name, T, [])
             | _ => tm)
        | mangle (IAbs (bound, tm)) = IAbs (bound, mangle tm)
        | mangle tm = tm
    in mangle end
  else
    I

fun chop_fun 0 T = ([], T)
  | chop_fun n (Type (@{type_name fun}, [dom_T, ran_T])) =
    chop_fun (n - 1) ran_T |>> cons dom_T
  | chop_fun _ T = ([], T)

fun filter_const_type_args _ _ _ [] = []
  | filter_const_type_args thy s ary T_args =
    let
      val U = robust_const_type thy s
      val arg_U_vars = fold Term.add_tvarsT (U |> chop_fun ary |> fst) []
      val U_args = (s, U) |> robust_const_typargs thy
    in
      U_args ~~ T_args
      |> map (fn (U, T) =>
                 if member (op =) arg_U_vars (dest_TVar U) then dummyT else T)
    end
    handle TYPE _ => T_args

fun filter_type_args_in_iterm thy monom_constrs type_enc =
  let
    fun filt ary (IApp (tm1, tm2)) = IApp (filt (ary + 1) tm1, filt 0 tm2)
      | filt _ (tm as IConst (_, _, [])) = tm
      | filt ary (IConst (name as (s, _), T, T_args)) =
        (case unprefix_and_unascii const_prefix s of
           NONE =>
           (name,
            if level_of_type_enc type_enc = No_Types orelse s = tptp_choice then
              []
            else
              T_args)
         | SOME s'' =>
           let
             val s'' = invert_const s''
             fun filter_T_args false = T_args
               | filter_T_args true = filter_const_type_args thy s'' ary T_args
           in
             case type_arg_policy monom_constrs type_enc s'' of
               Explicit_Type_Args infer_from_term_args =>
               (name, filter_T_args infer_from_term_args)
             | No_Type_Args => (name, [])
             | Mangled_Type_Args => raise Fail "unexpected (un)mangled symbol"
           end)
        |> (fn (name, T_args) => IConst (name, T, T_args))
      | filt _ (IAbs (bound, tm)) = IAbs (bound, filt 0 tm)
      | filt _ tm = tm
  in filt 0 end

fun iformula_from_prop ctxt format type_enc eq_as_iff =
  let
    val thy = Proof_Context.theory_of ctxt
    fun do_term bs t atomic_Ts =
      iterm_from_term thy format bs (Envir.eta_contract t)
      |>> (introduce_proxies_in_iterm type_enc
           #> mangle_type_args_in_iterm format type_enc
           #> AAtom)
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
        if eq_as_iff then do_conn bs AIff NONE t1 NONE t2 else do_term bs t
      | _ => do_term bs t
  in do_formula [] end

fun presimplify_term ctxt t =
  t |> exists_Const (member (op =) Meson.presimplified_consts o fst) t
       ? (Skip_Proof.make_thm (Proof_Context.theory_of ctxt)
          #> Meson.presimplify
          #> prop_of)

fun concealed_bound_name j = atp_weak_prefix ^ string_of_int j
fun conceal_bounds Ts t =
  subst_bounds (map (Free o apfst concealed_bound_name)
                    (0 upto length Ts - 1 ~~ Ts), t)
fun reveal_bounds Ts =
  subst_atomic (map (fn (j, T) => (Free (concealed_bound_name j, T), Bound j))
                    (0 upto length Ts - 1 ~~ Ts))

fun is_fun_equality (@{const_name HOL.eq},
                     Type (_, [Type (@{type_name fun}, _), _])) = true
  | is_fun_equality _ = false

fun extensionalize_term ctxt t =
  if exists_Const is_fun_equality t then
    let val thy = Proof_Context.theory_of ctxt in
      t |> cterm_of thy |> Meson.extensionalize_conv ctxt
        |> prop_of |> Logic.dest_equals |> snd
    end
  else
    t

fun simple_translate_lambdas do_lambdas ctxt t =
  let val thy = Proof_Context.theory_of ctxt in
    if Meson.is_fol_term thy t then
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
  end

fun do_cheaply_conceal_lambdas Ts (t1 $ t2) =
    do_cheaply_conceal_lambdas Ts t1
    $ do_cheaply_conceal_lambdas Ts t2
  | do_cheaply_conceal_lambdas Ts (Abs (_, T, t)) =
    Const (lam_lifted_poly_prefix ^ serial_string (),
           T --> fastype_of1 (T :: Ts, t))
  | do_cheaply_conceal_lambdas _ t = t

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

fun preprocess_abstractions_in_terms trans_lams facts =
  let
    val (facts, lambda_ts) =
      facts |> map (snd o snd) |> trans_lams
            |>> map2 (fn (name, (kind, _)) => fn t => (name, (kind, t))) facts
    val lam_facts =
      map2 (fn t => fn j =>
               ((lam_fact_prefix ^ Int.toString j, Helper), (Axiom, t)))
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

fun presimp_prop ctxt role t =
  (let
     val thy = Proof_Context.theory_of ctxt
     val t = t |> Envir.beta_eta_contract
               |> transform_elim_prop
               |> Object_Logic.atomize_term thy
     val need_trueprop = (fastype_of t = @{typ bool})
   in
     t |> need_trueprop ? HOLogic.mk_Trueprop
       |> extensionalize_term ctxt
       |> presimplify_term ctxt
       |> HOLogic.dest_Trueprop
   end
   handle TERM _ => if role = Conjecture then @{term False} else @{term True})
  |> pair role

fun make_formula ctxt format type_enc eq_as_iff name loc kind t =
  let
    val (iformula, atomic_Ts) =
      iformula_from_prop ctxt format type_enc eq_as_iff
                         (SOME (kind <> Conjecture)) t []
      |>> close_iformula_universally
  in
    {name = name, locality = loc, kind = kind, iformula = iformula,
     atomic_types = atomic_Ts}
  end

fun make_fact ctxt format type_enc eq_as_iff ((name, loc), t) =
  case t |> make_formula ctxt format type_enc (eq_as_iff andalso format <> CNF)
                         name loc Axiom of
    formula as {iformula = AAtom (IConst ((s, _), _, _)), ...} =>
    if s = tptp_true then NONE else SOME formula
  | formula => SOME formula

fun s_not_trueprop (@{const Trueprop} $ t) = @{const Trueprop} $ s_not t
  | s_not_trueprop t =
    if fastype_of t = @{typ bool} then s_not t else @{prop False} (* too meta *)

fun make_conjecture ctxt format type_enc =
  map (fn ((name, loc), (kind, t)) =>
          t |> kind = Conjecture ? s_not_trueprop
            |> make_formula ctxt format type_enc (format <> CNF) name loc kind)

(** Finite and infinite type inference **)

fun tvar_footprint thy s ary =
  (case unprefix_and_unascii const_prefix s of
     SOME s =>
     s |> invert_const |> robust_const_type thy |> chop_fun ary |> fst
       |> map (fn T => Term.add_tvarsT T [] |> map fst)
   | NONE => [])
  handle TYPE _ => []

fun ghost_type_args thy s ary =
  if is_tptp_equal s then
    0 upto ary - 1
  else
    let
      val footprint = tvar_footprint thy s ary
      val eq = (s = @{const_name HOL.eq})
      fun ghosts _ [] = []
        | ghosts seen ((i, tvars) :: args) =
          ghosts (union (op =) seen tvars) args
          |> (eq orelse exists (fn tvar => not (member (op =) seen tvar)) tvars)
             ? cons i
    in
      if forall null footprint then
        []
      else
        0 upto length footprint - 1 ~~ footprint
        |> sort (rev_order o list_ord Term_Ord.indexname_ord o pairself snd)
        |> ghosts []
    end

type monotonicity_info =
  {maybe_finite_Ts : typ list,
   surely_finite_Ts : typ list,
   maybe_infinite_Ts : typ list,
   surely_infinite_Ts : typ list,
   maybe_nonmono_Ts : typ list}

(* These types witness that the type classes they belong to allow infinite
   models and hence that any types with these type classes is monotonic. *)
val known_infinite_types =
  [@{typ nat}, HOLogic.intT, HOLogic.realT, @{typ "nat => bool"}]

fun is_type_kind_of_surely_infinite ctxt soundness cached_Ts T =
  soundness <> Sound andalso is_type_surely_infinite ctxt true cached_Ts T

(* Finite types such as "unit", "bool", "bool * bool", and "bool => bool" are
   dangerous because their "exhaust" properties can easily lead to unsound ATP
   proofs. On the other hand, all HOL infinite types can be given the same
   models in first-order logic (via Löwenheim-Skolem). *)

fun should_encode_type _ (_ : monotonicity_info) All_Types _ = true
  | should_encode_type ctxt {maybe_finite_Ts, surely_infinite_Ts,
                             maybe_nonmono_Ts, ...}
                       (Noninf_Nonmono_Types (soundness, grain)) T =
    grain = Ghost_Type_Arg_Vars orelse
    (exists (type_intersect ctxt T) maybe_nonmono_Ts andalso
     not (exists (type_instance ctxt T) surely_infinite_Ts orelse
          (not (member (type_equiv ctxt) maybe_finite_Ts T) andalso
           is_type_kind_of_surely_infinite ctxt soundness surely_infinite_Ts
                                           T)))
  | should_encode_type ctxt {surely_finite_Ts, maybe_infinite_Ts,
                             maybe_nonmono_Ts, ...}
                       (Fin_Nonmono_Types grain) T =
    grain = Ghost_Type_Arg_Vars orelse
    (exists (type_intersect ctxt T) maybe_nonmono_Ts andalso
     (exists (type_generalization ctxt T) surely_finite_Ts orelse
      (not (member (type_equiv ctxt) maybe_infinite_Ts T) andalso
       is_type_surely_finite ctxt T)))
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
  Elsewhere

fun should_tag_with_type _ _ _ (Top_Level _) _ _ = false
  | should_tag_with_type ctxt mono (Tags (_, level)) site u T =
    if granularity_of_type_level level = All_Vars then
      should_encode_type ctxt mono level T
    else
      (case (site, is_maybe_universal_var u) of
         (Eq_Arg _, true) => should_encode_type ctxt mono level T
       | _ => false)
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

fun sym_table_for_facts ctxt type_enc explicit_apply conjs facts =
  let
    fun consider_var_ary const_T var_T max_ary =
      let
        fun iter ary T =
          if ary = max_ary orelse type_instance ctxt var_T T orelse
             type_instance ctxt T var_T then
            ary
          else
            iter (ary + 1) (range_type T)
      in iter 0 const_T end
    fun add_universal_var T (accum as ((bool_vars, fun_var_Ts), sym_tab)) =
      if explicit_apply = NONE andalso
         (can dest_funT T orelse T = @{typ bool}) then
        let
          val bool_vars' = bool_vars orelse body_type T = @{typ bool}
          fun repair_min_ary {pred_sym, min_ary, max_ary, types, in_conj} =
            {pred_sym = pred_sym andalso not bool_vars',
             min_ary = fold (fn T' => consider_var_ary T' T) types min_ary,
             max_ary = max_ary, types = types, in_conj = in_conj}
          val fun_var_Ts' =
            fun_var_Ts |> can dest_funT T ? insert_type ctxt I T
        in
          if bool_vars' = bool_vars andalso
             pointer_eq (fun_var_Ts', fun_var_Ts) then
            accum
          else
            ((bool_vars', fun_var_Ts'), Symtab.map (K repair_min_ary) sym_tab)
        end
      else
        accum
    fun add_fact_syms conj_fact =
      let
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
                        val types' = types |> insert_type ctxt I T
                        val in_conj = in_conj orelse conj_fact
                        val min_ary =
                          if is_some explicit_apply orelse
                             pointer_eq (types', types) then
                            min_ary
                          else
                            fold (consider_var_ary T) fun_var_Ts min_ary
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
                        val min_ary =
                          case explicit_apply of
                            SOME true => 0
                          | SOME false => ary
                          | NONE => fold (consider_var_ary T) fun_var_Ts ary
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
      in K (add_iterm_syms true) |> formula_fold NONE |> fact_lift end
  in
    ((false, []), Symtab.empty)
    |> fold (add_fact_syms true) conjs
    |> fold (add_fact_syms false) facts
    |> snd
    |> fold Symtab.update (default_sym_tab_entries type_enc)
  end

fun min_ary_of sym_tab s =
  case Symtab.lookup sym_tab s of
    SOME ({min_ary, ...} : sym_info) => min_ary
  | NONE =>
    case unprefix_and_unascii const_prefix s of
      SOME s =>
      let val s = s |> unmangled_const_name |> invert_const in
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

val app_op = `(make_fixed_const NONE) app_op_name
val predicator_combconst =
  IConst (`(make_fixed_const NONE) predicator_name, @{typ "bool => bool"}, [])

fun list_app head args = fold (curry (IApp o swap)) args head
fun predicator tm = IApp (predicator_combconst, tm)

fun firstorderize_fact thy monom_constrs format type_enc sym_tab =
  let
    fun do_app arg head =
      let
        val head_T = ityp_of head
        val (arg_T, res_T) = dest_funT head_T
        val app =
          IConst (app_op, head_T --> head_T, [arg_T, res_T])
          |> mangle_type_args_in_iterm format type_enc
      in list_app app [head, arg] end
    fun list_app_ops head args = fold do_app args head
    fun introduce_app_ops tm =
      case strip_iterm_comb tm of
        (head as IConst ((s, _), _, _), args) =>
        args |> map introduce_app_ops
             |> chop (min_ary_of sym_tab s)
             |>> list_app head
             |-> list_app_ops
      | (head, args) => list_app_ops head (map introduce_app_ops args)
    fun introduce_predicators tm =
      case strip_iterm_comb tm of
        (IConst ((s, _), _, _), _) =>
        if is_pred_sym sym_tab s then tm else predicator tm
      | _ => predicator tm
    val do_iterm =
      not (is_type_enc_higher_order type_enc)
      ? (introduce_app_ops #> introduce_predicators)
      #> filter_type_args_in_iterm thy monom_constrs type_enc
  in update_iformula (formula_map do_iterm) end

(** Helper facts **)

val not_ffalse = @{lemma "~ fFalse" by (unfold fFalse_def) fast}
val ftrue = @{lemma "fTrue" by (unfold fTrue_def) fast}

(* The Boolean indicates that a fairly sound type encoding is needed. *)
val helper_table =
  [(("COMBI", false), @{thms Meson.COMBI_def}),
   (("COMBK", false), @{thms Meson.COMBK_def}),
   (("COMBB", false), @{thms Meson.COMBB_def}),
   (("COMBC", false), @{thms Meson.COMBC_def}),
   (("COMBS", false), @{thms Meson.COMBS_def}),
   ((predicator_name, false), [not_ffalse, ftrue]),
   (("fFalse", false), [not_ffalse]),
   (("fFalse", true), @{thms True_or_False}),
   (("fTrue", false), [ftrue]),
   (("fTrue", true), @{thms True_or_False}),
   (("fNot", false),
    @{thms fNot_def [THEN Meson.iff_to_disjD, THEN conjunct1]
           fNot_def [THEN Meson.iff_to_disjD, THEN conjunct2]}),
   (("fconj", false),
    @{lemma "~ P | ~ Q | fconj P Q" "~ fconj P Q | P" "~ fconj P Q | Q"
        by (unfold fconj_def) fast+}),
   (("fdisj", false),
    @{lemma "~ P | fdisj P Q" "~ Q | fdisj P Q" "~ fdisj P Q | P | Q"
        by (unfold fdisj_def) fast+}),
   (("fimplies", false),
    @{lemma "P | fimplies P Q" "~ Q | fimplies P Q" "~ fimplies P Q | ~ P | Q"
        by (unfold fimplies_def) fast+}),
   (("fequal", true),
    (* This is a lie: Higher-order equality doesn't need a sound type encoding.
       However, this is done so for backward compatibility: Including the
       equality helpers by default in Metis breaks a few existing proofs. *)
    @{thms fequal_def [THEN Meson.iff_to_disjD, THEN conjunct1]
           fequal_def [THEN Meson.iff_to_disjD, THEN conjunct2]}),
   (* Partial characterization of "fAll" and "fEx". A complete characterization
      would require the axiom of choice for replay with Metis. *)
   (("fAll", false), [@{lemma "~ fAll P | P x" by (auto simp: fAll_def)}]),
   (("fEx", false), [@{lemma "~ P x | fEx P" by (auto simp: fEx_def)}]),
   (("If", true), @{thms if_True if_False True_or_False})]
  |> map (apsnd (map zero_var_indexes))

fun atype_of_type_vars (Simple_Types (_, Polymorphic, _)) = SOME atype_of_types
  | atype_of_type_vars _ = NONE

fun bound_tvars type_enc sorts Ts =
  (sorts ? mk_ahorn (formulas_for_types type_enc add_sorts_on_tvar Ts))
  #> mk_aquant AForall
        (map_filter (fn TVar (x as (s, _), _) =>
                        SOME ((make_schematic_type_var x, s),
                              atype_of_type_vars type_enc)
                      | _ => NONE) Ts)

fun eq_formula type_enc atomic_Ts pred_sym tm1 tm2 =
  (if pred_sym then AConn (AIff, [AAtom tm1, AAtom tm2])
   else AAtom (ATerm (`I tptp_equal, [tm1, tm2])))
  |> close_formula_universally
  |> bound_tvars type_enc true atomic_Ts

val type_tag = `(make_fixed_const NONE) type_tag_name

fun type_tag_idempotence_fact format type_enc =
  let
    fun var s = ATerm (`I s, [])
    fun tag tm = ATerm (type_tag, [var "A", tm])
    val tagged_var = tag (var "X")
  in
    Formula (type_tag_idempotence_helper_name, Axiom,
             eq_formula type_enc [] false (tag tagged_var) tagged_var,
             isabelle_info format simpN, NONE)
  end

fun should_specialize_helper type_enc t =
  polymorphism_of_type_enc type_enc <> Polymorphic andalso
  level_of_type_enc type_enc <> No_Types andalso
  not (null (Term.hidden_polymorphism t))

fun helper_facts_for_sym ctxt format type_enc (s, {types, ...} : sym_info) =
  case unprefix_and_unascii const_prefix s of
    SOME mangled_s =>
    let
      val thy = Proof_Context.theory_of ctxt
      val unmangled_s = mangled_s |> unmangled_const_name
      fun dub needs_fairly_sound j k =
        (unmangled_s ^ "_" ^ string_of_int j ^ "_" ^ string_of_int k ^
         (if mangled_s = unmangled_s then "" else "_" ^ ascii_of mangled_s) ^
         (if needs_fairly_sound then typed_helper_suffix
          else untyped_helper_suffix),
         Helper)
      fun dub_and_inst needs_fairly_sound (th, j) =
        let val t = prop_of th in
          if should_specialize_helper type_enc t then
            map (fn T => specialize_type thy (invert_const unmangled_s, T) t)
                types
          else
            [t]
        end
        |> map (fn (k, t) => (dub needs_fairly_sound j k, t)) o tag_list 1
      val make_facts = map_filter (make_fact ctxt format type_enc false)
      val fairly_sound = is_type_enc_fairly_sound type_enc
    in
      helper_table
      |> maps (fn ((helper_s, needs_fairly_sound), ths) =>
                  if helper_s <> unmangled_s orelse
                     (needs_fairly_sound andalso not fairly_sound) then
                    []
                  else
                    ths ~~ (1 upto length ths)
                    |> maps (dub_and_inst needs_fairly_sound)
                    |> make_facts)
    end
  | NONE => []
fun helper_facts_for_sym_table ctxt format type_enc sym_tab =
  Symtab.fold_rev (append o helper_facts_for_sym ctxt format type_enc) sym_tab
                  []

(***************************************************************)
(* Type Classes Present in the Axiom or Conjecture Clauses     *)
(***************************************************************)

fun set_insert (x, s) = Symtab.update (x, ()) s

fun add_classes (sorts, cset) = List.foldl set_insert cset (flat sorts)

(* Remove this trivial type class (FIXME: similar code elsewhere) *)
fun delete_type cset = Symtab.delete_safe (the_single @{sort HOL.type}) cset

fun classes_of_terms get_Ts =
  map (map snd o get_Ts)
  #> List.foldl add_classes Symtab.empty
  #> delete_type #> Symtab.keys

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
                  | _ => raise Fail "expected Var") args u)
    end
  | extract_lambda_def _ = raise Fail "malformed lifted lambda"

fun trans_lams_from_string ctxt type_enc lam_trans =
  if lam_trans = no_lamsN then
    rpair []
  else if lam_trans = hide_lamsN then
    lift_lams ctxt type_enc ##> K []
  else if lam_trans = lam_liftingN then
    lift_lams ctxt type_enc
  else if lam_trans = combinatorsN then
    map (introduce_combinators ctxt) #> rpair []
  else if lam_trans = hybrid_lamsN then
    lift_lams_part_1 ctxt type_enc
    ##> maps (fn t => [t, introduce_combinators ctxt (intentionalize_def t)])
    #> lift_lams_part_2
  else if lam_trans = keep_lamsN then
    map (Envir.eta_contract) #> rpair []
  else
    error ("Unknown lambda translation scheme: " ^ quote lam_trans ^ ".")

fun translate_formulas ctxt format prem_kind type_enc lam_trans presimp hyp_ts
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
      map (pair prem_kind) hyp_ts @ [(Conjecture, s_not_trueprop concl_t)]
      |> map (apsnd freeze_term)
      |> map2 (pair o rpair Local o string_of_int) (0 upto length hyp_ts)
    val ((conjs, facts), lam_facts) =
      (conjs, facts)
      |> presimp ? pairself (map (apsnd (uncurry (presimp_prop ctxt))))
      |> (if lam_trans = no_lamsN then
            rpair []
          else
            op @
            #> preprocess_abstractions_in_terms trans_lams
            #>> chop (length conjs))
    val conjs = conjs |> make_conjecture ctxt format type_enc
    val (fact_names, facts) =
      facts
      |> map_filter (fn (name, (_, t)) =>
                        make_fact ctxt format type_enc true (name, t)
                        |> Option.map (pair name))
      |> ListPair.unzip
    val lifted = lam_facts |> map (extract_lambda_def o snd o snd)
    val lam_facts =
      lam_facts |> map_filter (make_fact ctxt format type_enc true o apsnd snd)
    val all_ts = concl_t :: hyp_ts @ fact_ts
    val subs = tfree_classes_of_terms all_ts
    val supers = tvar_classes_of_terms all_ts
    val tycons = type_constrs_of_terms thy all_ts
    val (supers, arity_clauses) =
      if level_of_type_enc type_enc = No_Types then ([], [])
      else make_arity_clauses thy tycons supers
    val class_rel_clauses = make_class_rel_clauses thy subs supers
  in
    (fact_names |> map single, union (op =) subs supers, conjs,
     facts @ lam_facts, class_rel_clauses, arity_clauses, lifted)
  end

val type_guard = `(make_fixed_const NONE) type_guard_name

fun type_guard_iterm format type_enc T tm =
  IApp (IConst (type_guard, T --> @{typ bool}, [T])
        |> mangle_type_args_in_iterm format type_enc, tm)

fun is_var_positively_naked_in_term _ (SOME false) _ accum = accum
  | is_var_positively_naked_in_term name _ (ATerm ((s, _), tms)) accum =
    accum orelse (is_tptp_equal s andalso member (op =) tms (ATerm (name, [])))
  | is_var_positively_naked_in_term _ _ _ _ = true

fun is_var_ghost_type_arg_in_term thy polym_constrs name pos tm accum =
  is_var_positively_naked_in_term name pos tm accum orelse
  let
    val var = ATerm (name, [])
    fun is_nasty_in_term (ATerm (_, [])) = false
      | is_nasty_in_term (ATerm ((s, _), tms)) =
        let
          val ary = length tms
          val polym_constr = member (op =) polym_constrs s
          val ghosts = ghost_type_args thy s ary
        in
          exists (fn (j, tm) =>
                     if polym_constr then
                       member (op =) ghosts j andalso
                       (tm = var orelse is_nasty_in_term tm)
                     else
                       tm = var andalso member (op =) ghosts j)
                 (0 upto ary - 1 ~~ tms)
          orelse (not polym_constr andalso exists is_nasty_in_term tms)
        end
      | is_nasty_in_term _ = true
  in is_nasty_in_term tm end

fun should_guard_var_in_formula thy polym_constrs level pos phi (SOME true)
                                name =
    (case granularity_of_type_level level of
       All_Vars => true
     | Positively_Naked_Vars =>
       formula_fold pos (is_var_positively_naked_in_term name) phi false
     | Ghost_Type_Arg_Vars =>
       formula_fold pos (is_var_ghost_type_arg_in_term thy polym_constrs name)
                    phi false)
  | should_guard_var_in_formula _ _ _ _ _ _ _ = true

fun always_guard_var_in_formula _ _ _ _ _ _ _ = true

fun should_generate_tag_bound_decl _ _ _ (SOME true) _ = false
  | should_generate_tag_bound_decl ctxt mono (Tags (_, level)) _ T =
    granularity_of_type_level level <> All_Vars andalso
    should_encode_type ctxt mono level T
  | should_generate_tag_bound_decl _ _ _ _ _ = false

fun mk_aterm format type_enc name T_args args =
  ATerm (name, map_filter (ho_term_for_type_arg format type_enc) T_args @ args)

fun tag_with_type ctxt format mono type_enc pos T tm =
  IConst (type_tag, T --> T, [T])
  |> mangle_type_args_in_iterm format type_enc
  |> ho_term_from_iterm ctxt format mono type_enc pos
  |> (fn ATerm (s, tms) => ATerm (s, tms @ [tm])
       | _ => raise Fail "unexpected lambda-abstraction")
and ho_term_from_iterm ctxt format mono type_enc =
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
              val arg_site = if is_tptp_equal s then Eq_Arg pos else Elsewhere
            in
              map (term arg_site) args |> mk_aterm format type_enc name T_args
            end
          | IVar (name, _) =>
            map (term Elsewhere) args |> mk_aterm format type_enc name []
          | IAbs ((name, T), tm) =>
            AAbs ((name, ho_type_from_typ format type_enc true 0 T),
                  term Elsewhere tm)
          | IApp _ => raise Fail "impossible \"IApp\""
        val T = ityp_of u
      in
        if should_tag_with_type ctxt mono type_enc site u T then
          tag_with_type ctxt format mono type_enc pos T t
        else
          t
      end
  in term o Top_Level end
and formula_from_iformula ctxt polym_constrs format mono type_enc
                          should_guard_var =
  let
    val thy = Proof_Context.theory_of ctxt
    val level = level_of_type_enc type_enc
    val do_term = ho_term_from_iterm ctxt format mono type_enc
    val do_bound_type =
      case type_enc of
        Simple_Types _ => fused_type ctxt mono level 0
        #> ho_type_from_typ format type_enc false 0 #> SOME
      | _ => K NONE
    fun do_out_of_bound_type pos phi universal (name, T) =
      if should_guard_type ctxt mono type_enc
             (fn () => should_guard_var thy polym_constrs level pos phi
                                        universal name) T then
        IVar (name, T)
        |> type_guard_iterm format type_enc T
        |> do_term pos |> AAtom |> SOME
      else if should_generate_tag_bound_decl ctxt mono type_enc universal T then
        let
          val var = ATerm (name, [])
          val tagged_var = tag_with_type ctxt format mono type_enc pos T var
        in SOME (AAtom (ATerm (`I tptp_equal, [tagged_var, var]))) end
      else
        NONE
    fun do_formula pos (AQuant (q, xs, phi)) =
        let
          val phi = phi |> do_formula pos
          val universal = Option.map (q = AExists ? not) pos
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
fun formula_line_for_fact ctxt polym_constrs format prefix encode freshen pos
        mono type_enc (j, {name, locality, kind, iformula, atomic_types}) =
  (prefix ^ (if freshen then string_of_int j ^ "_" else "") ^ encode name, kind,
   iformula
   |> formula_from_iformula ctxt polym_constrs format mono type_enc
          should_guard_var_in_formula (if pos then SOME true else NONE)
   |> close_formula_universally
   |> bound_tvars type_enc true atomic_types,
   NONE,
   case locality of
     Intro => isabelle_info format introN
   | Elim => isabelle_info format elimN
   | Simp => isabelle_info format simpN
   | _ => NONE)
  |> Formula

fun formula_line_for_class_rel_clause format type_enc
        ({name, subclass, superclass, ...} : class_rel_clause) =
  let val ty_arg = ATerm (tvar_a_name, []) in
    Formula (class_rel_clause_prefix ^ ascii_of name, Axiom,
             AConn (AImplies,
                    [type_class_formula type_enc subclass ty_arg,
                     type_class_formula type_enc superclass ty_arg])
             |> mk_aquant AForall
                          [(tvar_a_name, atype_of_type_vars type_enc)],
             isabelle_info format introN, NONE)
  end

fun formula_from_arity_atom type_enc (class, t, args) =
  ATerm (t, map (fn arg => ATerm (arg, [])) args)
  |> type_class_formula type_enc class

fun formula_line_for_arity_clause format type_enc
        ({name, prem_atoms, concl_atom} : arity_clause) =
  Formula (arity_clause_prefix ^ name, Axiom,
           mk_ahorn (map (formula_from_arity_atom type_enc) prem_atoms)
                    (formula_from_arity_atom type_enc concl_atom)
           |> mk_aquant AForall
                  (map (rpair (atype_of_type_vars type_enc)) (#3 concl_atom)),
           isabelle_info format introN, NONE)

fun formula_line_for_conjecture ctxt polym_constrs format mono type_enc
        ({name, kind, iformula, atomic_types, ...} : translated_formula) =
  Formula (conjecture_prefix ^ name, kind,
           iformula
           |> formula_from_iformula ctxt polym_constrs format mono type_enc
                  should_guard_var_in_formula (SOME false)
           |> close_formula_universally
           |> bound_tvars type_enc true atomic_types, NONE, NONE)

fun formula_line_for_free_type j phi =
  Formula (tfree_clause_prefix ^ string_of_int j, Hypothesis, phi, NONE, NONE)
fun formula_lines_for_free_types type_enc (facts : translated_formula list) =
  let
    val phis =
      fold (union (op =)) (map #atomic_types facts) []
      |> formulas_for_types type_enc add_sorts_on_tfree
  in map2 formula_line_for_free_type (0 upto length phis - 1) phis end

(** Symbol declarations **)

fun decl_line_for_class order s =
  let val name as (s, _) = `make_type_class s in
    Decl (sym_decl_prefix ^ s, name,
          if order = First_Order then
            ATyAbs ([tvar_a_name],
                    if avoid_first_order_ghost_type_vars then
                      AFun (a_itself_atype, bool_atype)
                    else
                      bool_atype)
          else
            AFun (atype_of_types, bool_atype))
  end

fun decl_lines_for_classes type_enc classes =
  case type_enc of
    Simple_Types (order, Polymorphic, _) =>
    map (decl_line_for_class order) classes
  | _ => []

fun sym_decl_table_for_facts ctxt format type_enc sym_tab (conjs, facts) =
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
                   (insert_type ctxt #3 (s', T_args, T, pred_sym, length args,
                                         in_conj))
             else
               I
           end
         | IAbs (_, tm) => add_iterm_syms tm
         | _ => I)
        #> fold add_iterm_syms args
      end
    val add_fact_syms = K add_iterm_syms |> formula_fold NONE |> fact_lift
    fun add_formula_var_types (AQuant (_, xs, phi)) =
        fold (fn (_, SOME T) => insert_type ctxt I T | _ => I) xs
        #> add_formula_var_types phi
      | add_formula_var_types (AConn (_, phis)) =
        fold add_formula_var_types phis
      | add_formula_var_types _ = I
    fun var_types () =
      if polymorphism_of_type_enc type_enc = Polymorphic then [tvar_a]
      else fold (fact_lift add_formula_var_types) (conjs @ facts) []
    fun add_undefined_const T =
      let
        val (s, s') =
          `(make_fixed_const NONE) @{const_name undefined}
          |> (case type_arg_policy [] type_enc @{const_name undefined} of
                Mangled_Type_Args => mangled_const_name format type_enc [T]
              | _ => I)
      in
        Symtab.map_default (s, [])
                           (insert_type ctxt #3 (s', [T], T, false, 0, false))
      end
    fun add_TYPE_const () =
      let val (s, s') = TYPE_name in
        Symtab.map_default (s, [])
            (insert_type ctxt #3
                         (s', [tvar_a], @{typ "'a itself"}, false, 0, false))
      end
  in
    Symtab.empty
    |> is_type_enc_fairly_sound type_enc
       ? (fold (fold add_fact_syms) [conjs, facts]
          #> (case type_enc of
                Simple_Types (First_Order, Polymorphic, _) =>
                if avoid_first_order_ghost_type_vars then add_TYPE_const ()
                else I
              | Simple_Types _ => I
              | _ => fold add_undefined_const (var_types ())))
  end

(* We add "bool" in case the helper "True_or_False" is included later. *)
fun default_mono level =
  {maybe_finite_Ts = [@{typ bool}],
   surely_finite_Ts = [@{typ bool}],
   maybe_infinite_Ts = known_infinite_types,
   surely_infinite_Ts =
     case level of
       Noninf_Nonmono_Types (Sound, _) => []
     | _ => known_infinite_types,
   maybe_nonmono_Ts = [@{typ bool}]}

(* This inference is described in section 2.3 of Claessen et al.'s "Sorting it
   out with monotonicity" paper presented at CADE 2011. *)
fun add_iterm_mononotonicity_info _ _ (SOME false) _ mono = mono
  | add_iterm_mononotonicity_info ctxt level _
        (IApp (IApp (IConst ((s, _), Type (_, [T, _]), _), tm1), tm2))
        (mono as {maybe_finite_Ts, surely_finite_Ts, maybe_infinite_Ts,
                  surely_infinite_Ts, maybe_nonmono_Ts}) =
    if is_tptp_equal s andalso exists is_maybe_universal_var [tm1, tm2] then
      case level of
        Noninf_Nonmono_Types (soundness, _) =>
        if exists (type_instance ctxt T) surely_infinite_Ts orelse
           member (type_equiv ctxt) maybe_finite_Ts T then
          mono
        else if is_type_kind_of_surely_infinite ctxt soundness
                                                surely_infinite_Ts T then
          {maybe_finite_Ts = maybe_finite_Ts,
           surely_finite_Ts = surely_finite_Ts,
           maybe_infinite_Ts = maybe_infinite_Ts,
           surely_infinite_Ts = surely_infinite_Ts |> insert_type ctxt I T,
           maybe_nonmono_Ts = maybe_nonmono_Ts}
        else
          {maybe_finite_Ts = maybe_finite_Ts |> insert (type_equiv ctxt) T,
           surely_finite_Ts = surely_finite_Ts,
           maybe_infinite_Ts = maybe_infinite_Ts,
           surely_infinite_Ts = surely_infinite_Ts,
           maybe_nonmono_Ts = maybe_nonmono_Ts |> insert_type ctxt I T}
      | Fin_Nonmono_Types _ =>
        if exists (type_instance ctxt T) surely_finite_Ts orelse
           member (type_equiv ctxt) maybe_infinite_Ts T then
          mono
        else if is_type_surely_finite ctxt T then
          {maybe_finite_Ts = maybe_finite_Ts,
           surely_finite_Ts = surely_finite_Ts |> insert_type ctxt I T,
           maybe_infinite_Ts = maybe_infinite_Ts,
           surely_infinite_Ts = surely_infinite_Ts,
           maybe_nonmono_Ts = maybe_nonmono_Ts |> insert_type ctxt I T}
        else
          {maybe_finite_Ts = maybe_finite_Ts,
           surely_finite_Ts = surely_finite_Ts,
           maybe_infinite_Ts = maybe_infinite_Ts |> insert (type_equiv ctxt) T,
           surely_infinite_Ts = surely_infinite_Ts,
           maybe_nonmono_Ts = maybe_nonmono_Ts}
      | _ => mono
    else
      mono
  | add_iterm_mononotonicity_info _ _ _ _ mono = mono
fun add_fact_mononotonicity_info ctxt level
        ({kind, iformula, ...} : translated_formula) =
  formula_fold (SOME (kind <> Conjecture))
               (add_iterm_mononotonicity_info ctxt level) iformula
fun mononotonicity_info_for_facts ctxt type_enc facts =
  let val level = level_of_type_enc type_enc in
    default_mono level
    |> is_type_level_monotonicity_based level
       ? fold (add_fact_mononotonicity_info ctxt level) facts
  end

fun add_iformula_monotonic_types ctxt mono type_enc =
  let
    val level = level_of_type_enc type_enc
    val should_encode = should_encode_type ctxt mono level
    fun add_type T = not (should_encode T) ? insert_type ctxt I T
    fun add_args (IApp (tm1, tm2)) = add_args tm1 #> add_term tm2
      | add_args _ = I
    and add_term tm = add_type (ityp_of tm) #> add_args tm
  in formula_fold NONE (K add_term) end
fun add_fact_monotonic_types ctxt mono type_enc =
  add_iformula_monotonic_types ctxt mono type_enc |> fact_lift
fun monotonic_types_for_facts ctxt mono type_enc facts =
  let val level = level_of_type_enc type_enc in
    [] |> (polymorphism_of_type_enc type_enc = Polymorphic andalso
           is_type_level_monotonicity_based level andalso
           granularity_of_type_level level <> Ghost_Type_Arg_Vars)
          ? fold (add_fact_monotonic_types ctxt mono type_enc) facts
  end

fun formula_line_for_guards_mono_type ctxt format mono type_enc T =
  Formula (guards_sym_formula_prefix ^
           ascii_of (mangled_type format type_enc T),
           Axiom,
           IConst (`make_bound_var "X", T, [])
           |> type_guard_iterm format type_enc T
           |> AAtom
           |> formula_from_iformula ctxt [] format mono type_enc
                                    always_guard_var_in_formula (SOME true)
           |> close_formula_universally
           |> bound_tvars type_enc true (atomic_types_of T),
           isabelle_info format introN, NONE)

fun formula_line_for_tags_mono_type ctxt format mono type_enc T =
  let val x_var = ATerm (`make_bound_var "X", []) in
    Formula (tags_sym_formula_prefix ^
             ascii_of (mangled_type format type_enc T),
             Axiom,
             eq_formula type_enc (atomic_types_of T) false
                  (tag_with_type ctxt format mono type_enc NONE T x_var) x_var,
             isabelle_info format simpN, NONE)
  end

fun problem_lines_for_mono_types ctxt format mono type_enc Ts =
  case type_enc of
    Simple_Types _ => []
  | Guards _ =>
    map (formula_line_for_guards_mono_type ctxt format mono type_enc) Ts
  | Tags _ => map (formula_line_for_tags_mono_type ctxt format mono type_enc) Ts

fun decl_line_for_sym ctxt format mono type_enc s
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
    Decl (sym_decl_prefix ^ s, (s, s'),
          T |> fused_type ctxt mono (level_of_type_enc type_enc) ary
            |> ho_type_from_typ format type_enc pred_sym ary
            |> not (null T_args)
               ? curry ATyAbs (map (tvar_name o fst o dest_TVar) T_args))
  end

fun formula_line_for_guards_sym_decl ctxt format conj_sym_kind mono type_enc n s
                                     j (s', T_args, T, _, ary, in_conj) =
  let
    val thy = Proof_Context.theory_of ctxt
    val (kind, maybe_negate) =
      if in_conj then (conj_sym_kind, conj_sym_kind = Conjecture ? mk_anot)
      else (Axiom, I)
    val (arg_Ts, res_T) = chop_fun ary T
    val bound_names = 1 upto ary |> map (`I o make_bound_var o string_of_int)
    val bounds =
      bound_names ~~ arg_Ts |> map (fn (name, T) => IConst (name, T, []))
    val bound_Ts =
      if exists (curry (op =) dummyT) T_args then
        case level_of_type_enc type_enc of
          All_Types => map SOME arg_Ts
        | level =>
          if granularity_of_type_level level = Ghost_Type_Arg_Vars then
            let val ghosts = ghost_type_args thy s ary in
              map2 (fn j => if member (op =) ghosts j then SOME else K NONE)
                   (0 upto ary - 1) arg_Ts
            end
          else
            replicate ary NONE
      else
        replicate ary NONE
  in
    Formula (guards_sym_formula_prefix ^ s ^
             (if n > 1 then "_" ^ string_of_int j else ""), kind,
             IConst ((s, s'), T, T_args)
             |> fold (curry (IApp o swap)) bounds
             |> type_guard_iterm format type_enc res_T
             |> AAtom |> mk_aquant AForall (bound_names ~~ bound_Ts)
             |> formula_from_iformula ctxt [] format mono type_enc
                                      always_guard_var_in_formula (SOME true)
             |> close_formula_universally
             |> bound_tvars type_enc (n > 1) (atomic_types_of T)
             |> maybe_negate,
             isabelle_info format introN, NONE)
  end

fun formula_lines_for_tags_sym_decl ctxt format conj_sym_kind mono type_enc n s
        (j, (s', T_args, T, pred_sym, ary, in_conj)) =
  let
    val thy = Proof_Context.theory_of ctxt
    val level = level_of_type_enc type_enc
    val grain = granularity_of_type_level level
    val ident_base =
      tags_sym_formula_prefix ^ s ^
      (if n > 1 then "_" ^ string_of_int j else "")
    val (kind, maybe_negate) =
      if in_conj then (conj_sym_kind, conj_sym_kind = Conjecture ? mk_anot)
      else (Axiom, I)
    val (arg_Ts, res_T) = chop_fun ary T
    val bound_names = 1 upto ary |> map (`I o make_bound_var o string_of_int)
    val bounds = bound_names |> map (fn name => ATerm (name, []))
    val cst = mk_aterm format type_enc (s, s') T_args
    val eq = maybe_negate oo eq_formula type_enc (atomic_types_of T) pred_sym
    val should_encode = should_encode_type ctxt mono level
    val tag_with = tag_with_type ctxt format mono type_enc NONE
    val add_formula_for_res =
      if should_encode res_T then
        let
          val tagged_bounds =
            if grain = Ghost_Type_Arg_Vars then
              let val ghosts = ghost_type_args thy s ary in
                map2 (fn (j, arg_T) => member (op =) ghosts j ? tag_with arg_T)
                     (0 upto ary - 1 ~~ arg_Ts) bounds
              end
            else
              bounds
        in
          cons (Formula (ident_base ^ "_res", kind,
                         eq (tag_with res_T (cst bounds)) (cst tagged_bounds),
                         isabelle_info format simpN, NONE))
        end
      else
        I
    fun add_formula_for_arg k =
      let val arg_T = nth arg_Ts k in
        if should_encode arg_T then
          case chop k bounds of
            (bounds1, bound :: bounds2) =>
            cons (Formula (ident_base ^ "_arg" ^ string_of_int (k + 1), kind,
                           eq (cst (bounds1 @ tag_with arg_T bound :: bounds2))
                              (cst bounds),
                           isabelle_info format simpN, NONE))
          | _ => raise Fail "expected nonempty tail"
        else
          I
      end
  in
    [] |> not pred_sym ? add_formula_for_res
       |> (Config.get ctxt type_tag_arguments andalso
           grain = Positively_Naked_Vars)
          ? fold add_formula_for_arg (ary - 1 downto 0)
  end

fun result_type_of_decl (_, _, T, _, ary, _) = chop_fun ary T |> snd

fun rationalize_decls ctxt (decls as decl :: (decls' as _ :: _)) =
    let
      val T = result_type_of_decl decl
              |> map_type_tvar (fn (z, _) => TVar (z, HOLogic.typeS))
    in
      if forall (type_generalization ctxt T o result_type_of_decl) decls' then
        [decl]
      else
        decls
    end
  | rationalize_decls _ decls = decls

fun problem_lines_for_sym_decls ctxt format conj_sym_kind mono type_enc
                                (s, decls) =
  case type_enc of
    Simple_Types _ => [decl_line_for_sym ctxt format mono type_enc s (hd decls)]
  | Guards (_, level) =>
    let
      val decls = decls |> rationalize_decls ctxt
      val n = length decls
      val decls =
        decls |> filter (should_encode_type ctxt mono level
                         o result_type_of_decl)
    in
      (0 upto length decls - 1, decls)
      |-> map2 (formula_line_for_guards_sym_decl ctxt format conj_sym_kind mono
                                                 type_enc n s)
    end
  | Tags (_, level) =>
    if granularity_of_type_level level = All_Vars then
      []
    else
      let val n = length decls in
        (0 upto n - 1 ~~ decls)
        |> maps (formula_lines_for_tags_sym_decl ctxt format conj_sym_kind mono
                                                 type_enc n s)
      end

fun problem_lines_for_sym_decl_table ctxt format conj_sym_kind mono type_enc
                                     mono_Ts sym_decl_tab =
  let
    val syms = sym_decl_tab |> Symtab.dest |> sort_wrt fst
    val mono_lines =
      problem_lines_for_mono_types ctxt format mono type_enc mono_Ts
    val decl_lines =
      fold_rev (append o problem_lines_for_sym_decls ctxt format conj_sym_kind
                             mono type_enc)
               syms []
  in mono_lines @ decl_lines end

fun needs_type_tag_idempotence ctxt (Tags (poly, level)) =
    Config.get ctxt type_tag_idempotence andalso
    is_type_level_monotonicity_based level andalso
    poly <> Mangled_Monomorphic
  | needs_type_tag_idempotence _ _ = false

val implicit_declsN = "Should-be-implicit typings"
val explicit_declsN = "Explicit typings"
val factsN = "Relevant facts"
val class_relsN = "Class relationships"
val aritiesN = "Arities"
val helpersN = "Helper facts"
val conjsN = "Conjectures"
val free_typesN = "Type variables"

(* TFF allows implicit declarations of types, function symbols, and predicate
   symbols (with "$i" as the type of individuals), but some provers (e.g.,
   SNARK) require explicit declarations. The situation is similar for THF. *)

fun default_type type_enc pred_sym s =
  let
    val ind =
      case type_enc of
        Simple_Types _ =>
        if String.isPrefix type_const_prefix s then atype_of_types
        else individual_atype
      | _ => individual_atype
    fun typ 0 = if pred_sym then bool_atype else ind
      | typ ary = AFun (ind, typ (ary - 1))
  in typ end

fun nary_type_constr_type n =
  funpow n (curry AFun atype_of_types) atype_of_types

fun undeclared_syms_in_problem type_enc problem =
  let
    val declared = declared_syms_in_problem problem
    fun do_sym name ty =
      if member (op =) declared name then I else AList.default (op =) (name, ty)
    fun do_type (AType (name as (s, _), tys)) =
        is_tptp_user_symbol s
        ? do_sym name (fn () => nary_type_constr_type (length tys))
        #> fold do_type tys
      | do_type (AFun (ty1, ty2)) = do_type ty1 #> do_type ty2
      | do_type (ATyAbs (_, ty)) = do_type ty
    fun do_term pred_sym (ATerm (name as (s, _), tms)) =
        is_tptp_user_symbol s
        ? do_sym name (fn _ => default_type type_enc pred_sym s (length tms))
        #> fold (do_term false) tms
      | do_term _ (AAbs ((_, ty), tm)) = do_type ty #> do_term false tm
    fun do_formula (AQuant (_, xs, phi)) =
        fold do_type (map_filter snd xs) #> do_formula phi
      | do_formula (AConn (_, phis)) = fold do_formula phis
      | do_formula (AAtom tm) = do_term true tm
    fun do_problem_line (Decl (_, _, ty)) = do_type ty
      | do_problem_line (Formula (_, _, phi, _, _)) = do_formula phi
  in
    fold (fold do_problem_line o snd) problem []
    |> filter_out (is_built_in_tptp_symbol o fst o fst)
  end

fun declare_undeclared_syms_in_atp_problem type_enc problem =
  let
    val decls =
      problem
      |> undeclared_syms_in_problem type_enc
      |> sort_wrt (fst o fst)
      |> map (fn (x as (s, _), ty) => Decl (type_decl_prefix ^ s, x, ty ()))
  in (implicit_declsN, decls) :: problem end

fun exists_subdtype P =
  let
    fun ex U = P U orelse
      (case U of Datatype.DtType (_, Us) => exists ex Us | _ => false)
  in ex end

fun is_poly_constr (_, Us) =
  exists (exists_subdtype (fn Datatype.DtTFree _ => true | _ => false)) Us

fun all_constrs_of_polymorphic_datatypes thy =
  Symtab.fold (snd
               #> #descr
               #> maps (snd #> #3)
               #> (fn cs => exists is_poly_constr cs ? append cs))
              (Datatype.get_all thy) []
  |> List.partition is_poly_constr
  |> pairself (map fst)

(* Forcing explicit applications is expensive for polymorphic encodings, because
   it takes only one existential variable ranging over "'a => 'b" to ruin
   everything. Hence we do it only if there are few facts (is normally the case
   for "metis" and the minimizer. *)
val explicit_apply_threshold = 50

fun prepare_atp_problem ctxt format conj_sym_kind prem_kind type_enc exporter
                        lam_trans readable_names preproc hyp_ts concl_t facts =
  let
    val thy = Proof_Context.theory_of ctxt
    val type_enc = type_enc |> adjust_type_enc format
    val explicit_apply =
      if polymorphism_of_type_enc type_enc <> Polymorphic orelse
         length facts <= explicit_apply_threshold then
        NONE
      else
        SOME false
    val lam_trans =
      if lam_trans = keep_lamsN andalso
         not (is_type_enc_higher_order type_enc) then
        error ("Lambda translation scheme incompatible with first-order \
               \encoding.")
      else
        lam_trans
    val (fact_names, classes, conjs, facts, class_rel_clauses, arity_clauses,
         lifted) =
      translate_formulas ctxt format prem_kind type_enc lam_trans preproc hyp_ts
                         concl_t facts
    val sym_tab = sym_table_for_facts ctxt type_enc explicit_apply conjs facts
    val mono = conjs @ facts |> mononotonicity_info_for_facts ctxt type_enc
    val (polym_constrs, monom_constrs) =
      all_constrs_of_polymorphic_datatypes thy
      |>> map (make_fixed_const (SOME format))
    val firstorderize =
      firstorderize_fact thy monom_constrs format type_enc sym_tab
    val (conjs, facts) = (conjs, facts) |> pairself (map firstorderize)
    val sym_tab = sym_table_for_facts ctxt type_enc (SOME false) conjs facts
    val helpers =
      sym_tab |> helper_facts_for_sym_table ctxt format type_enc
              |> map firstorderize
    val mono_Ts =
      helpers @ conjs @ facts |> monotonic_types_for_facts ctxt mono type_enc
    val class_decl_lines = decl_lines_for_classes type_enc classes
    val sym_decl_lines =
      (conjs, helpers @ facts)
      |> sym_decl_table_for_facts ctxt format type_enc sym_tab
      |> problem_lines_for_sym_decl_table ctxt format conj_sym_kind mono
                                               type_enc mono_Ts
    val helper_lines =
      0 upto length helpers - 1 ~~ helpers
      |> map (formula_line_for_fact ctxt polym_constrs format helper_prefix I
                                    false true mono type_enc)
      |> (if needs_type_tag_idempotence ctxt type_enc then
            cons (type_tag_idempotence_fact format type_enc)
          else
            I)
    (* Reordering these might confuse the proof reconstruction code or the SPASS
       FLOTTER hack. *)
    val problem =
      [(explicit_declsN, class_decl_lines @ sym_decl_lines),
       (factsN,
        map (formula_line_for_fact ctxt polym_constrs format fact_prefix
                 ascii_of (not exporter) (not exporter) mono type_enc)
            (0 upto length facts - 1 ~~ facts)),
       (class_relsN,
        map (formula_line_for_class_rel_clause format type_enc)
            class_rel_clauses),
       (aritiesN,
        map (formula_line_for_arity_clause format type_enc) arity_clauses),
       (helpersN, helper_lines),
       (conjsN,
        map (formula_line_for_conjecture ctxt polym_constrs format mono
                                         type_enc) conjs),
       (free_typesN, formula_lines_for_free_types type_enc (facts @ conjs))]
    val problem =
      problem
      |> (case format of
            CNF => ensure_cnf_problem
          | CNF_UEQ => filter_cnf_ueq_problem
          | FOF => I
          | TFF (_, TPTP_Implicit) => I
          | THF (_, TPTP_Implicit, _) => I
          | _ => declare_undeclared_syms_in_atp_problem type_enc)
    val (problem, pool) = problem |> nice_atp_problem readable_names format
    fun add_sym_ary (s, {min_ary, ...} : sym_info) =
      min_ary > 0 ? Symtab.insert (op =) (s, min_ary)
  in
    (problem,
     case pool of SOME the_pool => snd the_pool | NONE => Symtab.empty,
     fact_names |> Vector.fromList,
     lifted,
     Symtab.empty |> Symtab.fold add_sym_ary sym_tab)
  end

(* FUDGE *)
val conj_weight = 0.0
val hyp_weight = 0.1
val fact_min_weight = 0.2
val fact_max_weight = 1.0
val type_info_default_weight = 0.8

fun add_term_weights weight (ATerm (s, tms)) =
    is_tptp_user_symbol s ? Symtab.default (s, weight)
    #> fold (add_term_weights weight) tms
  | add_term_weights weight (AAbs (_, tm)) = add_term_weights weight tm
fun add_problem_line_weights weight (Formula (_, _, phi, _, _)) =
    formula_fold NONE (K (add_term_weights weight)) phi
  | add_problem_line_weights _ _ = I

fun add_conjectures_weights [] = I
  | add_conjectures_weights conjs =
    let val (hyps, conj) = split_last conjs in
      add_problem_line_weights conj_weight conj
      #> fold (add_problem_line_weights hyp_weight) hyps
    end

fun add_facts_weights facts =
  let
    val num_facts = length facts
    fun weight_of j =
      fact_min_weight + (fact_max_weight - fact_min_weight) * Real.fromInt j
                        / Real.fromInt num_facts
  in
    map weight_of (0 upto num_facts - 1) ~~ facts
    |> fold (uncurry add_problem_line_weights)
  end

(* Weights are from 0.0 (most important) to 1.0 (least important). *)
fun atp_problem_weights problem =
  let val get = these o AList.lookup (op =) problem in
    Symtab.empty
    |> add_conjectures_weights (get free_typesN @ get conjsN)
    |> add_facts_weights (get factsN)
    |> fold (fold (add_problem_line_weights type_info_default_weight) o get)
            [explicit_declsN, class_relsN, aritiesN]
    |> Symtab.dest
    |> sort (prod_ord Real.compare string_ord o pairself swap)
  end

end;

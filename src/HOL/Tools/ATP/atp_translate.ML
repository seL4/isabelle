(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_atp_translate.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Translation of HOL to FOL for Sledgehammer.
*)

signature ATP_TRANSLATE =
sig
  type 'a fo_term = 'a ATP_Problem.fo_term
  type connective = ATP_Problem.connective
  type ('a, 'b, 'c) formula = ('a, 'b, 'c) ATP_Problem.formula
  type format = ATP_Problem.format
  type formula_kind = ATP_Problem.formula_kind
  type 'a problem = 'a ATP_Problem.problem

  type name = string * string

  datatype type_literal =
    TyLitVar of name * name |
    TyLitFree of name * name

  datatype arity_literal =
    TConsLit of name * name * name list |
    TVarLit of name * name

  type arity_clause =
    {name: string,
     prem_lits: arity_literal list,
     concl_lits: arity_literal}

  type class_rel_clause =
    {name: string,
     subclass: name,
     superclass: name}

  datatype combterm =
    CombConst of name * typ * typ list |
    CombVar of name * typ |
    CombApp of combterm * combterm

  datatype locality = General | Intro | Elim | Simp | Local | Assum | Chained

  datatype polymorphism = Polymorphic | Monomorphic | Mangled_Monomorphic
  datatype type_level =
    All_Types | Nonmonotonic_Types | Finite_Types | Const_Arg_Types | No_Types
  datatype type_heaviness = Heavyweight | Lightweight

  datatype type_sys =
    Simple_Types of type_level |
    Preds of polymorphism * type_level * type_heaviness |
    Tags of polymorphism * type_level * type_heaviness

  val bound_var_prefix : string
  val schematic_var_prefix: string
  val fixed_var_prefix: string
  val tvar_prefix: string
  val tfree_prefix: string
  val const_prefix: string
  val type_const_prefix: string
  val class_prefix: string
  val skolem_const_prefix : string
  val old_skolem_const_prefix : string
  val new_skolem_const_prefix : string
  val type_decl_prefix : string
  val sym_decl_prefix : string
  val preds_sym_formula_prefix : string
  val lightweight_tags_sym_formula_prefix : string
  val fact_prefix : string
  val conjecture_prefix : string
  val helper_prefix : string
  val class_rel_clause_prefix : string
  val arity_clause_prefix : string
  val tfree_clause_prefix : string
  val typed_helper_suffix : string
  val untyped_helper_suffix : string
  val type_tag_idempotence_helper_name : string
  val predicator_name : string
  val app_op_name : string
  val type_tag_name : string
  val type_pred_name : string
  val simple_type_prefix : string
  val prefixed_predicator_name : string
  val prefixed_app_op_name : string
  val prefixed_type_tag_name : string
  val ascii_of: string -> string
  val unascii_of: string -> string
  val strip_prefix_and_unascii : string -> string -> string option
  val proxy_table : (string * (string * (thm * (string * string)))) list
  val proxify_const : string -> (string * string) option
  val invert_const: string -> string
  val unproxify_const: string -> string
  val make_bound_var : string -> string
  val make_schematic_var : string * int -> string
  val make_fixed_var : string -> string
  val make_schematic_type_var : string * int -> string
  val make_fixed_type_var : string -> string
  val make_fixed_const : string -> string
  val make_fixed_type_const : string -> string
  val make_type_class : string -> string
  val new_skolem_var_name_from_const : string -> string
  val num_type_args : theory -> string -> int
  val atp_irrelevant_consts : string list
  val atp_schematic_consts_of : term -> typ list Symtab.table
  val make_arity_clauses :
    theory -> string list -> class list -> class list * arity_clause list
  val make_class_rel_clauses :
    theory -> class list -> class list -> class_rel_clause list
  val combtyp_of : combterm -> typ
  val strip_combterm_comb : combterm -> combterm * combterm list
  val atyps_of : typ -> typ list
  val combterm_from_term :
    theory -> (string * typ) list -> term -> combterm * typ list
  val is_locality_global : locality -> bool
  val type_sys_from_string : string -> type_sys
  val polymorphism_of_type_sys : type_sys -> polymorphism
  val level_of_type_sys : type_sys -> type_level
  val is_type_sys_virtually_sound : type_sys -> bool
  val is_type_sys_fairly_sound : type_sys -> bool
  val choose_format : format list -> type_sys -> format * type_sys
  val mk_aconns :
    connective -> ('a, 'b, 'c) formula list -> ('a, 'b, 'c) formula
  val unmangled_const_name : string -> string
  val unmangled_const : string -> string * string fo_term list
  val helper_table : ((string * bool) * thm list) list
  val should_specialize_helper : type_sys -> term -> bool
  val tfree_classes_of_terms : term list -> string list
  val tvar_classes_of_terms : term list -> string list
  val type_constrs_of_terms : theory -> term list -> string list
  val prepare_atp_problem :
    Proof.context -> format -> formula_kind -> formula_kind -> type_sys
    -> bool -> bool -> term list -> term -> ((string * locality) * term) list
    -> string problem * string Symtab.table * int * int
       * (string * locality) list vector * int list * int Symtab.table
  val atp_problem_weights : string problem -> (string * real) list
end;

structure ATP_Translate : ATP_TRANSLATE =
struct

open ATP_Util
open ATP_Problem

type name = string * string

(* experimental *)
val generate_useful_info = false

fun useful_isabelle_info s =
  if generate_useful_info then
    SOME (ATerm ("[]", [ATerm ("isabelle_" ^ s, [])]))
  else
    NONE

val intro_info = useful_isabelle_info "intro"
val elim_info = useful_isabelle_info "elim"
val simp_info = useful_isabelle_info "simp"

val bound_var_prefix = "B_"
val schematic_var_prefix = "V_"
val fixed_var_prefix = "v_"

val tvar_prefix = "T_"
val tfree_prefix = "t_"

val const_prefix = "c_"
val type_const_prefix = "tc_"
val class_prefix = "cl_"

val skolem_const_prefix = "Sledgehammer" ^ Long_Name.separator ^ "Sko"
val old_skolem_const_prefix = skolem_const_prefix ^ "o"
val new_skolem_const_prefix = skolem_const_prefix ^ "n"

val type_decl_prefix = "ty_"
val sym_decl_prefix = "sy_"
val preds_sym_formula_prefix = "psy_"
val lightweight_tags_sym_formula_prefix = "tsy_"
val fact_prefix = "fact_"
val conjecture_prefix = "conj_"
val helper_prefix = "help_"
val class_rel_clause_prefix = "clar_"
val arity_clause_prefix = "arity_"
val tfree_clause_prefix = "tfree_"

val typed_helper_suffix = "_T"
val untyped_helper_suffix = "_U"
val type_tag_idempotence_helper_name = helper_prefix ^ "ti_idem"

val predicator_name = "hBOOL"
val app_op_name = "hAPP"
val type_tag_name = "ti"
val type_pred_name = "is"
val simple_type_prefix = "ty_"

val prefixed_predicator_name = const_prefix ^ predicator_name
val prefixed_app_op_name = const_prefix ^ app_op_name
val prefixed_type_tag_name = const_prefix ^ type_tag_name

(* Freshness almost guaranteed! *)
val sledgehammer_weak_prefix = "Sledgehammer:"

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
      | un rcs (#"_" :: #"_" :: cs) = un (#"_"::rcs) cs
      | un rcs (#"_" :: c :: cs) =
        if #"A" <= c andalso c<= #"P" then
          (* translation of #" " to #"/" *)
          un (Char.chr (Char.ord c - upper_a_minus_space) :: rcs) cs
        else
          let val digits = List.take (c::cs, 3) handle Subscript => [] in
            case Int.fromString (String.implode digits) of
              SOME n => un (Char.chr n :: rcs) (List.drop (cs, 2))
            | NONE => un (c:: #"_"::rcs) cs (* ERROR *)
          end
      | un rcs (c :: cs) = un (c :: rcs) cs
  in un [] o String.explode end

(* If string s has the prefix s1, return the result of deleting it,
   un-ASCII'd. *)
fun strip_prefix_and_unascii s1 s =
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
       ("fequal", @{const_name ATP.fequal}))))]

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
   (@{const_name If}, "If"),
   (@{const_name Set.member}, "member"),
   (@{const_name Meson.COMBI}, "COMBI"),
   (@{const_name Meson.COMBK}, "COMBK"),
   (@{const_name Meson.COMBB}, "COMBB"),
   (@{const_name Meson.COMBC}, "COMBC"),
   (@{const_name Meson.COMBS}, "COMBS")]
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

(*Remove the initial ' character from a type variable, if it is present*)
fun trim_type_var s =
  if s <> "" andalso String.sub(s,0) = #"'" then String.extract(s,1,NONE)
  else raise Fail ("trim_type: Malformed type variable encountered: " ^ s)

fun ascii_of_indexname (v,0) = ascii_of v
  | ascii_of_indexname (v,i) = ascii_of v ^ "_" ^ string_of_int i

fun make_bound_var x = bound_var_prefix ^ ascii_of x
fun make_schematic_var v = schematic_var_prefix ^ ascii_of_indexname v
fun make_fixed_var x = fixed_var_prefix ^ ascii_of x

fun make_schematic_type_var (x,i) =
      tvar_prefix ^ (ascii_of_indexname (trim_type_var x, i))
fun make_fixed_type_var x = tfree_prefix ^ (ascii_of (trim_type_var x))

(* HOL.eq MUST BE "equal" because it's built into ATPs. *)
fun make_fixed_const @{const_name HOL.eq} = "equal"
  | make_fixed_const c = const_prefix ^ lookup_const c

fun make_fixed_type_const c = type_const_prefix ^ lookup_const c

fun make_type_class clas = class_prefix ^ ascii_of clas

fun new_skolem_var_name_from_const s =
  let val ss = s |> space_explode Long_Name.separator in
    nth ss (length ss - 2)
  end

(* The number of type arguments of a constant, zero if it's monomorphic. For
   (instances of) Skolem pseudoconstants, this information is encoded in the
   constant name. *)
fun num_type_args thy s =
  if String.isPrefix skolem_const_prefix s then
    s |> space_explode Long_Name.separator |> List.last |> Int.fromString |> the
  else
    (s, Sign.the_const_type thy s) |> Sign.const_typargs thy |> length

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

(* The first component is the type class; the second is a "TVar" or "TFree". *)
datatype type_literal =
  TyLitVar of name * name |
  TyLitFree of name * name


(** Isabelle arities **)

datatype arity_literal =
  TConsLit of name * name * name list |
  TVarLit of name * name

fun gen_TVars 0 = []
  | gen_TVars n = ("T_" ^ string_of_int n) :: gen_TVars (n-1)

val type_class = the_single @{sort type}

fun add_packed_sort tvar =
  fold (fn s => s <> type_class ? cons (`make_type_class s, `I tvar))

type arity_clause =
  {name: string,
   prem_lits: arity_literal list,
   concl_lits: arity_literal}

(* Arity of type constructor "tcon :: (arg1, ..., argN) res" *)
fun make_axiom_arity_clause (tcons, name, (cls, args)) =
  let
    val tvars = gen_TVars (length args)
    val tvars_srts = ListPair.zip (tvars, args)
  in
    {name = name,
     prem_lits = [] |> fold (uncurry add_packed_sort) tvars_srts |> map TVarLit,
     concl_lits = TConsLit (`make_type_class cls,
                            `make_fixed_type_const tcons,
                            tvars ~~ tvars)}
  end

fun arity_clause _ _ (_, []) = []
  | arity_clause seen n (tcons, ("HOL.type",_)::ars) =  (*ignore*)
      arity_clause seen n (tcons,ars)
  | arity_clause seen n (tcons, (ar as (class,_)) :: ars) =
      if member (op =) seen class then (*multiple arities for the same tycon, class pair*)
          make_axiom_arity_clause (tcons, lookup_const tcons ^ "_" ^ class ^ "_" ^ string_of_int n, ar) ::
          arity_clause seen (n+1) (tcons,ars)
      else
          make_axiom_arity_clause (tcons, lookup_const tcons ^ "_" ^ class, ar) ::
          arity_clause (class::seen) n (tcons,ars)

fun multi_arity_clause [] = []
  | multi_arity_clause ((tcons, ars) :: tc_arlists) =
      arity_clause [] 1 (tcons, ars) @ multi_arity_clause tc_arlists

(*Generate all pairs (tycon,class,sorts) such that tycon belongs to class in theory thy
  provided its arguments have the corresponding sorts.*)
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
      in (union (op =) classes' classes, union (op =) cpairs' cpairs) end

fun make_arity_clauses thy tycons =
  iter_type_class_pairs thy tycons ##> multi_arity_clause


(** Isabelle class relations **)

type class_rel_clause =
  {name: string,
   subclass: name,
   superclass: name}

(*Generate all pairs (sub,super) such that sub is a proper subclass of super in theory thy.*)
fun class_pairs _ [] _ = []
  | class_pairs thy subs supers =
      let
        val class_less = Sorts.class_less (Sign.classes_of thy)
        fun add_super sub super = class_less (sub, super) ? cons (sub, super)
        fun add_supers sub = fold (add_super sub) supers
      in fold add_supers subs [] end

fun make_class_rel_clause (sub,super) =
  {name = sub ^ "_" ^ super,
   subclass = `make_type_class sub,
   superclass = `make_type_class super}

fun make_class_rel_clauses thy subs supers =
  map make_class_rel_clause (class_pairs thy subs supers)

datatype combterm =
  CombConst of name * typ * typ list |
  CombVar of name * typ |
  CombApp of combterm * combterm

fun combtyp_of (CombConst (_, T, _)) = T
  | combtyp_of (CombVar (_, T)) = T
  | combtyp_of (CombApp (t1, _)) = snd (dest_funT (combtyp_of t1))

(*gets the head of a combinator application, along with the list of arguments*)
fun strip_combterm_comb u =
    let fun stripc (CombApp(t,u), ts) = stripc (t, u::ts)
        |   stripc  x =  x
    in stripc(u,[]) end

fun atyps_of T = fold_atyps (insert (op =)) T []

fun new_skolem_const_name s num_T_args =
  [new_skolem_const_prefix, s, string_of_int num_T_args]
  |> space_implode Long_Name.separator

(* Converts a term (with combinators) into a combterm. Also accumulates sort
   infomation. *)
fun combterm_from_term thy bs (P $ Q) =
    let
      val (P', P_atomics_Ts) = combterm_from_term thy bs P
      val (Q', Q_atomics_Ts) = combterm_from_term thy bs Q
    in (CombApp (P', Q'), union (op =) P_atomics_Ts Q_atomics_Ts) end
  | combterm_from_term thy _ (Const (c, T)) =
    let
      val tvar_list =
        (if String.isPrefix old_skolem_const_prefix c then
           [] |> Term.add_tvarsT T |> map TVar
         else
           (c, T) |> Sign.const_typargs thy)
      val c' = CombConst (`make_fixed_const c, T, tvar_list)
    in (c', atyps_of T) end
  | combterm_from_term _ _ (Free (v, T)) =
    (CombConst (`make_fixed_var v, T, []), atyps_of T)
  | combterm_from_term _ _ (Var (v as (s, _), T)) =
    (if String.isPrefix Meson_Clausify.new_skolem_var_prefix s then
       let
         val Ts = T |> strip_type |> swap |> op ::
         val s' = new_skolem_const_name s (length Ts)
       in CombConst (`make_fixed_const s', T, Ts) end
     else
       CombVar ((make_schematic_var v, s), T), atyps_of T)
  | combterm_from_term _ bs (Bound j) =
    nth bs j
    |> (fn (s, T) => (CombConst (`make_bound_var s, T, []), atyps_of T))
  | combterm_from_term _ _ (Abs _) = raise Fail "HOL clause: Abs"

datatype locality = General | Intro | Elim | Simp | Local | Assum | Chained

(* (quasi-)underapproximation of the truth *)
fun is_locality_global Local = false
  | is_locality_global Assum = false
  | is_locality_global Chained = false
  | is_locality_global _ = true

datatype polymorphism = Polymorphic | Monomorphic | Mangled_Monomorphic
datatype type_level =
  All_Types | Nonmonotonic_Types | Finite_Types | Const_Arg_Types | No_Types
datatype type_heaviness = Heavyweight | Lightweight

datatype type_sys =
  Simple_Types of type_level |
  Preds of polymorphism * type_level * type_heaviness |
  Tags of polymorphism * type_level * type_heaviness

fun try_unsuffixes ss s =
  fold (fn s' => fn NONE => try (unsuffix s') s | some => some) ss NONE

fun type_sys_from_string s =
  (case try (unprefix "poly_") s of
     SOME s => (SOME Polymorphic, s)
   | NONE =>
     case try (unprefix "mono_") s of
       SOME s => (SOME Monomorphic, s)
     | NONE =>
       case try (unprefix "mangled_") s of
         SOME s => (SOME Mangled_Monomorphic, s)
       | NONE => (NONE, s))
  ||> (fn s =>
          (* "_query" and "_bang" are for the ASCII-challenged Mirabelle. *)
          case try_unsuffixes ["?", "_query"] s of
            SOME s => (Nonmonotonic_Types, s)
          | NONE =>
            case try_unsuffixes ["!", "_bang"] s of
              SOME s => (Finite_Types, s)
            | NONE => (All_Types, s))
  ||> apsnd (fn s =>
                case try (unsuffix "_heavy") s of
                  SOME s => (Heavyweight, s)
                | NONE => (Lightweight, s))
  |> (fn (poly, (level, (heaviness, core))) =>
         case (core, (poly, level, heaviness)) of
           ("simple", (NONE, _, Lightweight)) => Simple_Types level
         | ("preds", (SOME poly, _, _)) => Preds (poly, level, heaviness)
         | ("tags", (SOME Polymorphic, All_Types, _)) =>
           Tags (Polymorphic, All_Types, heaviness)
         | ("tags", (SOME Polymorphic, _, _)) =>
           (* The actual light encoding is very unsound. *)
           Tags (Polymorphic, level, Heavyweight)
         | ("tags", (SOME poly, _, _)) => Tags (poly, level, heaviness)
         | ("args", (SOME poly, All_Types (* naja *), Lightweight)) =>
           Preds (poly, Const_Arg_Types, Lightweight)
         | ("erased", (NONE, All_Types (* naja *), Lightweight)) =>
           Preds (Polymorphic, No_Types, Lightweight)
         | _ => raise Same.SAME)
  handle Same.SAME => error ("Unknown type system: " ^ quote s ^ ".")

fun polymorphism_of_type_sys (Simple_Types _) = Mangled_Monomorphic
  | polymorphism_of_type_sys (Preds (poly, _, _)) = poly
  | polymorphism_of_type_sys (Tags (poly, _, _)) = poly

fun level_of_type_sys (Simple_Types level) = level
  | level_of_type_sys (Preds (_, level, _)) = level
  | level_of_type_sys (Tags (_, level, _)) = level

fun heaviness_of_type_sys (Simple_Types _) = Heavyweight
  | heaviness_of_type_sys (Preds (_, _, heaviness)) = heaviness
  | heaviness_of_type_sys (Tags (_, _, heaviness)) = heaviness

fun is_type_level_virtually_sound level =
  level = All_Types orelse level = Nonmonotonic_Types
val is_type_sys_virtually_sound =
  is_type_level_virtually_sound o level_of_type_sys

fun is_type_level_fairly_sound level =
  is_type_level_virtually_sound level orelse level = Finite_Types
val is_type_sys_fairly_sound = is_type_level_fairly_sound o level_of_type_sys

fun is_setting_higher_order THF (Simple_Types _) = true
  | is_setting_higher_order _ _ = false

fun choose_format formats (Simple_Types level) =
    if member (op =) formats THF then (THF, Simple_Types level)
    else if member (op =) formats TFF then (TFF, Simple_Types level)
    else choose_format formats (Preds (Mangled_Monomorphic, level, Heavyweight))
  | choose_format formats type_sys =
    (case hd formats of
       CNF_UEQ =>
       (CNF_UEQ, case type_sys of
                   Preds stuff =>
                   (if is_type_sys_fairly_sound type_sys then Preds else Tags)
                       stuff
                 | _ => type_sys)
     | format => (format, type_sys))

type translated_formula =
  {name: string,
   locality: locality,
   kind: formula_kind,
   combformula: (name, typ, combterm) formula,
   atomic_types: typ list}

fun update_combformula f ({name, locality, kind, combformula, atomic_types}
                          : translated_formula) =
  {name = name, locality = locality, kind = kind, combformula = f combformula,
   atomic_types = atomic_types} : translated_formula

fun fact_lift f ({combformula, ...} : translated_formula) = f combformula

val type_instance = Sign.typ_instance o Proof_Context.theory_of

fun insert_type ctxt get_T x xs =
  let val T = get_T x in
    if exists (curry (type_instance ctxt) T o get_T) xs then xs
    else x :: filter_out (curry (type_instance ctxt o swap) T o get_T) xs
  end

(* The Booleans indicate whether all type arguments should be kept. *)
datatype type_arg_policy =
  Explicit_Type_Args of bool |
  Mangled_Type_Args of bool |
  No_Type_Args

fun should_drop_arg_type_args (Simple_Types _) =
    false (* since TFF doesn't support overloading *)
  | should_drop_arg_type_args type_sys =
    level_of_type_sys type_sys = All_Types andalso
    heaviness_of_type_sys type_sys = Heavyweight

fun general_type_arg_policy (Tags (_, All_Types, Heavyweight)) = No_Type_Args
  | general_type_arg_policy type_sys =
    if level_of_type_sys type_sys = No_Types then
      No_Type_Args
    else if polymorphism_of_type_sys type_sys = Mangled_Monomorphic then
      Mangled_Type_Args (should_drop_arg_type_args type_sys)
    else
      Explicit_Type_Args (should_drop_arg_type_args type_sys)

fun type_arg_policy type_sys s =
  if s = @{const_name HOL.eq} orelse
     (s = app_op_name andalso level_of_type_sys type_sys = Const_Arg_Types) then
    No_Type_Args
  else if s = type_tag_name then
    Explicit_Type_Args false
  else
    general_type_arg_policy type_sys

(*Make literals for sorted type variables*)
fun generic_add_sorts_on_type (_, []) = I
  | generic_add_sorts_on_type ((x, i), s :: ss) =
    generic_add_sorts_on_type ((x, i), ss)
    #> (if s = the_single @{sort HOL.type} then
          I
        else if i = ~1 then
          insert (op =) (TyLitFree (`make_type_class s, `make_fixed_type_var x))
        else
          insert (op =) (TyLitVar (`make_type_class s,
                                   (make_schematic_type_var (x, i), x))))
fun add_sorts_on_tfree (TFree (s, S)) = generic_add_sorts_on_type ((s, ~1), S)
  | add_sorts_on_tfree _ = I
fun add_sorts_on_tvar (TVar z) = generic_add_sorts_on_type z
  | add_sorts_on_tvar _ = I

fun type_literals_for_types type_sys add_sorts_on_typ Ts =
  [] |> level_of_type_sys type_sys <> No_Types ? fold add_sorts_on_typ Ts

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

fun close_universally atom_vars phi =
  let
    fun formula_vars bounds (AQuant (_, xs, phi)) =
        formula_vars (map fst xs @ bounds) phi
      | formula_vars bounds (AConn (_, phis)) = fold (formula_vars bounds) phis
      | formula_vars bounds (AAtom tm) =
        union (op =) (atom_vars tm []
                      |> filter_out (member (op =) bounds o fst))
  in mk_aquant AForall (formula_vars [] phi []) phi end

fun combterm_vars (CombApp (tm1, tm2)) = fold combterm_vars [tm1, tm2]
  | combterm_vars (CombConst _) = I
  | combterm_vars (CombVar (name, T)) = insert (op =) (name, SOME T)
fun close_combformula_universally phi = close_universally combterm_vars phi

fun term_vars (ATerm (name as (s, _), tms)) =
  is_tptp_variable s ? insert (op =) (name, NONE) #> fold term_vars tms
fun close_formula_universally phi = close_universally term_vars phi

val homo_infinite_type_name = @{type_name ind} (* any infinite type *)
val homo_infinite_type = Type (homo_infinite_type_name, [])

fun fo_term_from_typ format type_sys =
  let
    fun term (Type (s, Ts)) =
      ATerm (case (is_setting_higher_order format type_sys, s) of
               (true, @{type_name bool}) => `I tptp_bool_type
             | (true, @{type_name fun}) => `I tptp_fun_type
             | _ => if s = homo_infinite_type_name andalso
                       (format = TFF orelse format = THF) then
                      `I tptp_individual_type
                    else
                      `make_fixed_type_const s,
             map term Ts)
    | term (TFree (s, _)) = ATerm (`make_fixed_type_var s, [])
    | term (TVar ((x as (s, _)), _)) =
      ATerm ((make_schematic_type_var x, s), [])
  in term end

(* This shouldn't clash with anything else. *)
val mangled_type_sep = "\000"

fun generic_mangled_type_name f (ATerm (name, [])) = f name
  | generic_mangled_type_name f (ATerm (name, tys)) =
    f name ^ "(" ^ space_implode "," (map (generic_mangled_type_name f) tys)
    ^ ")"

val bool_atype = AType (`I tptp_bool_type)

fun make_simple_type s =
  if s = tptp_bool_type orelse s = tptp_fun_type orelse
     s = tptp_individual_type then
    s
  else
    simple_type_prefix ^ ascii_of s

fun ho_type_from_fo_term format type_sys pred_sym ary =
  let
    fun to_atype ty =
      AType ((make_simple_type (generic_mangled_type_name fst ty),
              generic_mangled_type_name snd ty))
    fun to_afun f1 f2 tys = AFun (f1 (hd tys), f2 (nth tys 1))
    fun to_fo 0 ty = if pred_sym then bool_atype else to_atype ty
      | to_fo ary (ATerm (_, tys)) = to_afun to_atype (to_fo (ary - 1)) tys
    fun to_ho (ty as ATerm ((s, _), tys)) =
      if s = tptp_fun_type then to_afun to_ho to_ho tys else to_atype ty
  in if is_setting_higher_order format type_sys then to_ho else to_fo ary end

fun mangled_type format type_sys pred_sym ary =
  ho_type_from_fo_term format type_sys pred_sym ary
  o fo_term_from_typ format type_sys

fun mangled_const_name format type_sys T_args (s, s') =
  let
    val ty_args = map (fo_term_from_typ format type_sys) T_args
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

fun introduce_proxies format type_sys =
  let
    fun intro top_level (CombApp (tm1, tm2)) =
        CombApp (intro top_level tm1, intro false tm2)
      | intro top_level (CombConst (name as (s, _), T, T_args)) =
        (case proxify_const s of
           SOME proxy_base =>
           if top_level orelse is_setting_higher_order format type_sys then
             case (top_level, s) of
               (_, "c_False") => (`I tptp_false, [])
             | (_, "c_True") => (`I tptp_true, [])
             | (false, "c_Not") => (`I tptp_not, [])
             | (false, "c_conj") => (`I tptp_and, [])
             | (false, "c_disj") => (`I tptp_or, [])
             | (false, "c_implies") => (`I tptp_implies, [])
             | (false, s) =>
               if is_tptp_equal s then (`I tptp_equal, [])
               else (proxy_base |>> prefix const_prefix, T_args)
             | _ => (name, [])
           else
             (proxy_base |>> prefix const_prefix, T_args)
          | NONE => (name, T_args))
        |> (fn (name, T_args) => CombConst (name, T, T_args))
      | intro _ tm = tm
  in intro true end

fun combformula_from_prop thy format type_sys eq_as_iff =
  let
    fun do_term bs t atomic_types =
      combterm_from_term thy bs (Envir.eta_contract t)
      |>> (introduce_proxies format type_sys #> AAtom)
      ||> union (op =) atomic_types
    fun do_quant bs q s T t' =
      let val s = Name.variant (map fst bs) s in
        do_formula ((s, T) :: bs) t'
        #>> mk_aquant q [(`make_bound_var s, SOME T)]
      end
    and do_conn bs c t1 t2 =
      do_formula bs t1 ##>> do_formula bs t2 #>> uncurry (mk_aconn c)
    and do_formula bs t =
      case t of
        @{const Trueprop} $ t1 => do_formula bs t1
      | @{const Not} $ t1 => do_formula bs t1 #>> mk_anot
      | Const (@{const_name All}, _) $ Abs (s, T, t') =>
        do_quant bs AForall s T t'
      | Const (@{const_name Ex}, _) $ Abs (s, T, t') =>
        do_quant bs AExists s T t'
      | @{const HOL.conj} $ t1 $ t2 => do_conn bs AAnd t1 t2
      | @{const HOL.disj} $ t1 $ t2 => do_conn bs AOr t1 t2
      | @{const HOL.implies} $ t1 $ t2 => do_conn bs AImplies t1 t2
      | Const (@{const_name HOL.eq}, Type (_, [@{typ bool}, _])) $ t1 $ t2 =>
        if eq_as_iff then do_conn bs AIff t1 t2 else do_term bs t
      | _ => do_term bs t
  in do_formula [] end

fun presimplify_term ctxt =
  Skip_Proof.make_thm (Proof_Context.theory_of ctxt)
  #> Meson.presimplify ctxt
  #> prop_of

fun concealed_bound_name j = sledgehammer_weak_prefix ^ string_of_int j
fun conceal_bounds Ts t =
  subst_bounds (map (Free o apfst concealed_bound_name)
                    (0 upto length Ts - 1 ~~ Ts), t)
fun reveal_bounds Ts =
  subst_atomic (map (fn (j, T) => (Free (concealed_bound_name j, T), Bound j))
                    (0 upto length Ts - 1 ~~ Ts))

fun extensionalize_term ctxt t =
  let val thy = Proof_Context.theory_of ctxt in
    t |> cterm_of thy |> Meson.extensionalize_conv ctxt
      |> prop_of |> Logic.dest_equals |> snd
  end

fun introduce_combinators_in_term ctxt kind t =
  let val thy = Proof_Context.theory_of ctxt in
    if Meson.is_fol_term thy t then
      t
    else
      let
        fun aux Ts t =
          case t of
            @{const Not} $ t1 => @{const Not} $ aux Ts t1
          | (t0 as Const (@{const_name All}, _)) $ Abs (s, T, t') =>
            t0 $ Abs (s, T, aux (T :: Ts) t')
          | (t0 as Const (@{const_name All}, _)) $ t1 =>
            aux Ts (t0 $ eta_expand Ts t1 1)
          | (t0 as Const (@{const_name Ex}, _)) $ Abs (s, T, t') =>
            t0 $ Abs (s, T, aux (T :: Ts) t')
          | (t0 as Const (@{const_name Ex}, _)) $ t1 =>
            aux Ts (t0 $ eta_expand Ts t1 1)
          | (t0 as @{const HOL.conj}) $ t1 $ t2 => t0 $ aux Ts t1 $ aux Ts t2
          | (t0 as @{const HOL.disj}) $ t1 $ t2 => t0 $ aux Ts t1 $ aux Ts t2
          | (t0 as @{const HOL.implies}) $ t1 $ t2 => t0 $ aux Ts t1 $ aux Ts t2
          | (t0 as Const (@{const_name HOL.eq}, Type (_, [@{typ bool}, _])))
              $ t1 $ t2 =>
            t0 $ aux Ts t1 $ aux Ts t2
          | _ => if not (exists_subterm (fn Abs _ => true | _ => false) t) then
                   t
                 else
                   t |> conceal_bounds Ts
                     |> Envir.eta_contract
                     |> cterm_of thy
                     |> Meson_Clausify.introduce_combinators_in_cterm
                     |> prop_of |> Logic.dest_equals |> snd
                     |> reveal_bounds Ts
        val (t, ctxt') = Variable.import_terms true [t] ctxt |>> the_single
      in t |> aux [] |> singleton (Variable.export_terms ctxt' ctxt) end
      handle THM _ =>
             (* A type variable of sort "{}" will make abstraction fail. *)
             if kind = Conjecture then HOLogic.false_const
             else HOLogic.true_const
  end

(* Metis's use of "resolve_tac" freezes the schematic variables. We simulate the
   same in Sledgehammer to prevent the discovery of unreplayable proofs. *)
fun freeze_term t =
  let
    fun aux (t $ u) = aux t $ aux u
      | aux (Abs (s, T, t)) = Abs (s, T, aux t)
      | aux (Var ((s, i), T)) =
        Free (sledgehammer_weak_prefix ^ s ^ "_" ^ string_of_int i, T)
      | aux t = t
  in t |> exists_subterm is_Var t ? aux end

fun preprocess_prop ctxt presimp kind t =
  let
    val thy = Proof_Context.theory_of ctxt
    val t = t |> Envir.beta_eta_contract
              |> transform_elim_prop
              |> Object_Logic.atomize_term thy
    val need_trueprop = (fastype_of t = @{typ bool})
  in
    t |> need_trueprop ? HOLogic.mk_Trueprop
      |> Raw_Simplifier.rewrite_term thy (Meson.unfold_set_const_simps ctxt) []
      |> extensionalize_term ctxt
      |> presimp ? presimplify_term ctxt
      |> perhaps (try (HOLogic.dest_Trueprop))
      |> introduce_combinators_in_term ctxt kind
  end

(* making fact and conjecture formulas *)
fun make_formula thy format type_sys eq_as_iff name loc kind t =
  let
    val (combformula, atomic_types) =
      combformula_from_prop thy format type_sys eq_as_iff t []
  in
    {name = name, locality = loc, kind = kind, combformula = combformula,
     atomic_types = atomic_types}
  end

fun make_fact ctxt format type_sys keep_trivial eq_as_iff preproc presimp
              ((name, loc), t) =
  let val thy = Proof_Context.theory_of ctxt in
    case (keep_trivial,
          t |> preproc ? preprocess_prop ctxt presimp Axiom
            |> make_formula thy format type_sys eq_as_iff name loc Axiom) of
      (false,
       formula as {combformula = AAtom (CombConst ((s, _), _, _)), ...}) =>
      if s = tptp_true then NONE else SOME formula
    | (_, formula) => SOME formula
  end

fun make_conjecture ctxt format prem_kind type_sys preproc ts =
  let
    val thy = Proof_Context.theory_of ctxt
    val last = length ts - 1
  in
    map2 (fn j => fn t =>
             let
               val (kind, maybe_negate) =
                 if j = last then
                   (Conjecture, I)
                 else
                   (prem_kind,
                    if prem_kind = Conjecture then update_combformula mk_anot
                    else I)
              in
                t |> preproc ? (preprocess_prop ctxt true kind #> freeze_term)
                  |> make_formula thy format type_sys (format <> CNF)
                                  (string_of_int j) General kind
                  |> maybe_negate
              end)
         (0 upto last) ts
  end

(** Finite and infinite type inference **)

fun deep_freeze_atyp (TVar (_, S)) = TFree ("v", S)
  | deep_freeze_atyp T = T
val deep_freeze_type = map_atyps deep_freeze_atyp

(* Finite types such as "unit", "bool", "bool * bool", and "bool => bool" are
   dangerous because their "exhaust" properties can easily lead to unsound ATP
   proofs. On the other hand, all HOL infinite types can be given the same
   models in first-order logic (via Löwenheim-Skolem). *)

fun should_encode_type ctxt (nonmono_Ts as _ :: _) _ T =
    exists (curry (type_instance ctxt) (deep_freeze_type T)) nonmono_Ts
  | should_encode_type _ _ All_Types _ = true
  | should_encode_type ctxt _ Finite_Types T = is_type_surely_finite ctxt T
  | should_encode_type _ _ _ _ = false

fun should_predicate_on_type ctxt nonmono_Ts (Preds (_, level, heaviness))
                             should_predicate_on_var T =
    (heaviness = Heavyweight orelse should_predicate_on_var ()) andalso
    should_encode_type ctxt nonmono_Ts level T
  | should_predicate_on_type _ _ _ _ _ = false

fun is_var_or_bound_var (CombConst ((s, _), _, _)) =
    String.isPrefix bound_var_prefix s
  | is_var_or_bound_var (CombVar _) = true
  | is_var_or_bound_var _ = false

datatype tag_site = Top_Level | Eq_Arg | Elsewhere

fun should_tag_with_type _ _ _ Top_Level _ _ = false
  | should_tag_with_type ctxt nonmono_Ts (Tags (_, level, heaviness)) site u T =
    (case heaviness of
       Heavyweight => should_encode_type ctxt nonmono_Ts level T
     | Lightweight =>
       case (site, is_var_or_bound_var u) of
         (Eq_Arg, true) => should_encode_type ctxt nonmono_Ts level T
       | _ => false)
  | should_tag_with_type _ _ _ _ _ _ = false

fun homogenized_type ctxt nonmono_Ts level =
  let
    val should_encode = should_encode_type ctxt nonmono_Ts level
    fun homo 0 T = if should_encode T then T else homo_infinite_type
      | homo ary (Type (@{type_name fun}, [T1, T2])) =
        homo 0 T1 --> homo (ary - 1) T2
      | homo _ _ = raise Fail "expected function type"
  in homo end

(** "hBOOL" and "hAPP" **)

type sym_info =
  {pred_sym : bool, min_ary : int, max_ary : int, types : typ list}

fun add_combterm_syms_to_table ctxt explicit_apply =
  let
    fun consider_var_arity const_T var_T max_ary =
      let
        fun iter ary T =
          if ary = max_ary orelse type_instance ctxt (var_T, T) orelse
             type_instance ctxt (T, var_T) then
            ary
          else
            iter (ary + 1) (range_type T)
      in iter 0 const_T end
    fun add_var_or_bound_var T (accum as ((bool_vars, fun_var_Ts), sym_tab)) =
      if explicit_apply = NONE andalso
         (can dest_funT T orelse T = @{typ bool}) then
        let
          val bool_vars' = bool_vars orelse body_type T = @{typ bool}
          fun repair_min_arity {pred_sym, min_ary, max_ary, types} =
            {pred_sym = pred_sym andalso not bool_vars',
             min_ary = fold (fn T' => consider_var_arity T' T) types min_ary,
             max_ary = max_ary, types = types}
          val fun_var_Ts' =
            fun_var_Ts |> can dest_funT T ? insert_type ctxt I T
        in
          if bool_vars' = bool_vars andalso
             pointer_eq (fun_var_Ts', fun_var_Ts) then
            accum
          else
            ((bool_vars', fun_var_Ts'), Symtab.map (K repair_min_arity) sym_tab)
        end
      else
        accum
    fun add top_level tm (accum as ((bool_vars, fun_var_Ts), sym_tab)) =
      let val (head, args) = strip_combterm_comb tm in
        (case head of
           CombConst ((s, _), T, _) =>
           if String.isPrefix bound_var_prefix s then
             add_var_or_bound_var T accum
           else
             let val ary = length args in
               ((bool_vars, fun_var_Ts),
                case Symtab.lookup sym_tab s of
                  SOME {pred_sym, min_ary, max_ary, types} =>
                  let
                    val pred_sym =
                      pred_sym andalso top_level andalso not bool_vars
                    val types' = types |> insert_type ctxt I T
                    val min_ary =
                      if is_some explicit_apply orelse
                         pointer_eq (types', types) then
                        min_ary
                      else
                        fold (consider_var_arity T) fun_var_Ts min_ary
                  in
                    Symtab.update (s, {pred_sym = pred_sym,
                                       min_ary = Int.min (ary, min_ary),
                                       max_ary = Int.max (ary, max_ary),
                                       types = types'})
                                  sym_tab
                  end
                | NONE =>
                  let
                    val pred_sym = top_level andalso not bool_vars
                    val min_ary =
                      case explicit_apply of
                        SOME true => 0
                      | SOME false => ary
                      | NONE => fold (consider_var_arity T) fun_var_Ts ary
                  in
                    Symtab.update_new (s, {pred_sym = pred_sym,
                                           min_ary = min_ary, max_ary = ary,
                                           types = [T]})
                                      sym_tab
                  end)
             end
         | CombVar (_, T) => add_var_or_bound_var T accum
         | _ => accum)
        |> fold (add false) args
      end
  in add true end
fun add_fact_syms_to_table ctxt explicit_apply =
  fact_lift (formula_fold NONE
                          (K (add_combterm_syms_to_table ctxt explicit_apply)))

val default_sym_tab_entries : (string * sym_info) list =
  (prefixed_predicator_name,
   {pred_sym = true, min_ary = 1, max_ary = 1, types = []}) ::
  ([tptp_false, tptp_true]
   |> map (rpair {pred_sym = true, min_ary = 0, max_ary = 0, types = []})) @
  ([tptp_equal, tptp_old_equal]
   |> map (rpair {pred_sym = true, min_ary = 2, max_ary = 2, types = []}))

fun sym_table_for_facts ctxt explicit_apply facts =
  ((false, []), Symtab.empty)
  |> fold (add_fact_syms_to_table ctxt explicit_apply) facts |> snd
  |> fold Symtab.update default_sym_tab_entries

fun min_arity_of sym_tab s =
  case Symtab.lookup sym_tab s of
    SOME ({min_ary, ...} : sym_info) => min_ary
  | NONE =>
    case strip_prefix_and_unascii const_prefix s of
      SOME s =>
      let val s = s |> unmangled_const_name |> invert_const in
        if s = predicator_name then 1
        else if s = app_op_name then 2
        else if s = type_pred_name then 1
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

val predicator_combconst =
  CombConst (`make_fixed_const predicator_name, @{typ "bool => bool"}, [])
fun predicator tm = CombApp (predicator_combconst, tm)

fun introduce_predicators_in_combterm sym_tab tm =
  case strip_combterm_comb tm of
    (CombConst ((s, _), _, _), _) =>
    if is_pred_sym sym_tab s then tm else predicator tm
  | _ => predicator tm

fun list_app head args = fold (curry (CombApp o swap)) args head

val app_op = `make_fixed_const app_op_name

fun explicit_app arg head =
  let
    val head_T = combtyp_of head
    val (arg_T, res_T) = dest_funT head_T
    val explicit_app =
      CombConst (app_op, head_T --> head_T, [arg_T, res_T])
  in list_app explicit_app [head, arg] end
fun list_explicit_app head args = fold explicit_app args head

fun introduce_explicit_apps_in_combterm sym_tab =
  let
    fun aux tm =
      case strip_combterm_comb tm of
        (head as CombConst ((s, _), _, _), args) =>
        args |> map aux
             |> chop (min_arity_of sym_tab s)
             |>> list_app head
             |-> list_explicit_app
      | (head, args) => list_explicit_app head (map aux args)
  in aux end

fun chop_fun 0 T = ([], T)
  | chop_fun n (Type (@{type_name fun}, [dom_T, ran_T])) =
    chop_fun (n - 1) ran_T |>> cons dom_T
  | chop_fun _ _ = raise Fail "unexpected non-function"

fun filter_type_args _ _ _ [] = []
  | filter_type_args thy s arity T_args =
    let
      (* will throw "TYPE" for pseudo-constants *)
      val U = if s = app_op_name then
                @{typ "('a => 'b) => 'a => 'b"} |> Logic.varifyT_global
              else
                s |> Sign.the_const_type thy
    in
      case Term.add_tvarsT (U |> chop_fun arity |> snd) [] of
        [] => []
      | res_U_vars =>
        let val U_args = (s, U) |> Sign.const_typargs thy in
          U_args ~~ T_args
          |> map_filter (fn (U, T) =>
                            if member (op =) res_U_vars (dest_TVar U) then
                              SOME T
                            else
                              NONE)
        end
    end
    handle TYPE _ => T_args

fun enforce_type_arg_policy_in_combterm ctxt format type_sys =
  let
    val thy = Proof_Context.theory_of ctxt
    fun aux arity (CombApp (tm1, tm2)) =
        CombApp (aux (arity + 1) tm1, aux 0 tm2)
      | aux arity (CombConst (name as (s, _), T, T_args)) =
        (case strip_prefix_and_unascii const_prefix s of
           NONE => (name, T_args)
         | SOME s'' =>
           let
             val s'' = invert_const s''
             fun filtered_T_args false = T_args
               | filtered_T_args true = filter_type_args thy s'' arity T_args
           in
             case type_arg_policy type_sys s'' of
               Explicit_Type_Args drop_args =>
               (name, filtered_T_args drop_args)
             | Mangled_Type_Args drop_args =>
               (mangled_const_name format type_sys (filtered_T_args drop_args)
                                   name, [])
             | No_Type_Args => (name, [])
           end)
        |> (fn (name, T_args) => CombConst (name, T, T_args))
      | aux _ tm = tm
  in aux 0 end

fun repair_combterm ctxt format type_sys sym_tab =
  not (is_setting_higher_order format type_sys)
  ? (introduce_explicit_apps_in_combterm sym_tab
     #> introduce_predicators_in_combterm sym_tab)
  #> enforce_type_arg_policy_in_combterm ctxt format type_sys
fun repair_fact ctxt format type_sys sym_tab =
  update_combformula (formula_map
      (repair_combterm ctxt format type_sys sym_tab))

(** Helper facts **)

(* The Boolean indicates that a fairly sound type encoding is needed. *)
val helper_table =
  [(("COMBI", false), @{thms Meson.COMBI_def}),
   (("COMBK", false), @{thms Meson.COMBK_def}),
   (("COMBB", false), @{thms Meson.COMBB_def}),
   (("COMBC", false), @{thms Meson.COMBC_def}),
   (("COMBS", false), @{thms Meson.COMBS_def}),
   (("fequal", true),
    (* This is a lie: Higher-order equality doesn't need a sound type encoding.
       However, this is done so for backward compatibility: Including the
       equality helpers by default in Metis breaks a few existing proofs. *)
    @{thms fequal_def [THEN Meson.iff_to_disjD, THEN conjunct1]
           fequal_def [THEN Meson.iff_to_disjD, THEN conjunct2]}),
   (("fFalse", false), [@{lemma "~ fFalse" by (unfold fFalse_def) fast}]),
   (("fFalse", true), @{thms True_or_False}),
   (("fTrue", false), [@{lemma "fTrue" by (unfold fTrue_def) fast}]),
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
   (("If", true), @{thms if_True if_False True_or_False})]
  |> map (apsnd (map zero_var_indexes))

val type_tag = `make_fixed_const type_tag_name

fun type_tag_idempotence_fact () =
  let
    fun var s = ATerm (`I s, [])
    fun tag tm = ATerm (type_tag, [var "T", tm])
    val tagged_a = tag (var "A")
  in
    Formula (type_tag_idempotence_helper_name, Axiom,
             AAtom (ATerm (`I tptp_equal, [tag tagged_a, tagged_a]))
             |> close_formula_universally, simp_info, NONE)
  end

fun should_specialize_helper type_sys t =
  case general_type_arg_policy type_sys of
    Mangled_Type_Args _ => not (null (Term.hidden_polymorphism t))
  | _ => false

fun helper_facts_for_sym ctxt format type_sys (s, {types, ...} : sym_info) =
  case strip_prefix_and_unascii const_prefix s of
    SOME mangled_s =>
    let
      val thy = Proof_Context.theory_of ctxt
      val unmangled_s = mangled_s |> unmangled_const_name
      fun dub_and_inst needs_fairly_sound (th, j) =
        ((unmangled_s ^ "_" ^ string_of_int j ^
          (if mangled_s = unmangled_s then "" else "_" ^ ascii_of mangled_s) ^
          (if needs_fairly_sound then typed_helper_suffix
           else untyped_helper_suffix),
          General),
         let val t = th |> prop_of in
           t |> should_specialize_helper type_sys t
                ? (case types of
                     [T] => specialize_type thy (invert_const unmangled_s, T)
                   | _ => I)
         end)
      val make_facts =
        map_filter (make_fact ctxt format type_sys false false false false)
      val fairly_sound = is_type_sys_fairly_sound type_sys
    in
      helper_table
      |> maps (fn ((helper_s, needs_fairly_sound), ths) =>
                  if helper_s <> unmangled_s orelse
                     (needs_fairly_sound andalso not fairly_sound) then
                    []
                  else
                    ths ~~ (1 upto length ths)
                    |> map (dub_and_inst needs_fairly_sound)
                    |> make_facts)
    end
  | NONE => []
fun helper_facts_for_sym_table ctxt format type_sys sym_tab =
  Symtab.fold_rev (append o helper_facts_for_sym ctxt format type_sys) sym_tab
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

val tfree_classes_of_terms = classes_of_terms OldTerm.term_tfrees
val tvar_classes_of_terms = classes_of_terms OldTerm.term_tvars

(*fold type constructors*)
fun fold_type_constrs f (Type (a, Ts)) x =
    fold (fold_type_constrs f) Ts (f (a,x))
  | fold_type_constrs _ _ x = x

(*Type constructors used to instantiate overloaded constants are the only ones needed.*)
fun add_type_constrs_in_term thy =
  let
    fun add (Const (@{const_name Meson.skolem}, _) $ _) = I
      | add (t $ u) = add t #> add u
      | add (Const (x as (s, _))) =
        if String.isPrefix skolem_const_prefix s then I
        else x |> Sign.const_typargs thy |> fold (fold_type_constrs set_insert)
      | add (Abs (_, _, u)) = add u
      | add _ = I
  in add end

fun type_constrs_of_terms thy ts =
  Symtab.keys (fold (add_type_constrs_in_term thy) ts Symtab.empty)

fun translate_formulas ctxt format prem_kind type_sys preproc hyp_ts concl_t
                       facts =
  let
    val thy = Proof_Context.theory_of ctxt
    val fact_ts = facts |> map snd
    val (facts, fact_names) =
      facts |> map (fn (name, t) =>
                        (name, t)
                        |> make_fact ctxt format type_sys false true true true
                        |> rpair name)
            |> map_filter (try (apfst the))
            |> ListPair.unzip
    (* Remove existing facts from the conjecture, as this can dramatically
       boost an ATP's performance (for some reason). *)
    val hyp_ts =
      hyp_ts
      |> map (fn t => if member (op aconv) fact_ts t then @{prop True} else t)
    val goal_t = Logic.list_implies (hyp_ts, concl_t)
    val all_ts = goal_t :: fact_ts
    val subs = tfree_classes_of_terms all_ts
    val supers = tvar_classes_of_terms all_ts
    val tycons = type_constrs_of_terms thy all_ts
    val conjs =
      hyp_ts @ [concl_t]
      |> make_conjecture ctxt format prem_kind type_sys preproc
    val (supers', arity_clauses) =
      if level_of_type_sys type_sys = No_Types then ([], [])
      else make_arity_clauses thy tycons supers
    val class_rel_clauses = make_class_rel_clauses thy subs supers'
  in
    (fact_names |> map single, (conjs, facts, class_rel_clauses, arity_clauses))
  end

fun fo_literal_from_type_literal (TyLitVar (class, name)) =
    (true, ATerm (class, [ATerm (name, [])]))
  | fo_literal_from_type_literal (TyLitFree (class, name)) =
    (true, ATerm (class, [ATerm (name, [])]))

fun formula_from_fo_literal (pos, t) = AAtom t |> not pos ? mk_anot

val type_pred = `make_fixed_const type_pred_name

fun type_pred_combterm ctxt format type_sys T tm =
  CombApp (CombConst (type_pred, T --> @{typ bool}, [T])
           |> enforce_type_arg_policy_in_combterm ctxt format type_sys, tm)

fun var_occurs_positively_naked_in_term _ (SOME false) _ accum = accum
  | var_occurs_positively_naked_in_term name _ (ATerm ((s, _), tms)) accum =
    accum orelse (is_tptp_equal s andalso member (op =) tms (ATerm (name, [])))
fun is_var_nonmonotonic_in_formula _ _ (SOME false) _ = false
  | is_var_nonmonotonic_in_formula pos phi _ name =
    formula_fold pos (var_occurs_positively_naked_in_term name) phi false

fun mk_const_aterm format type_sys x T_args args =
  ATerm (x, map (fo_term_from_typ format type_sys) T_args @ args)

fun tag_with_type ctxt format nonmono_Ts type_sys T tm =
  CombConst (type_tag, T --> T, [T])
  |> enforce_type_arg_policy_in_combterm ctxt format type_sys
  |> term_from_combterm ctxt format nonmono_Ts type_sys Top_Level
  |> (fn ATerm (s, tms) => ATerm (s, tms @ [tm]))
and term_from_combterm ctxt format nonmono_Ts type_sys =
  let
    fun aux site u =
      let
        val (head, args) = strip_combterm_comb u
        val (x as (s, _), T_args) =
          case head of
            CombConst (name, _, T_args) => (name, T_args)
          | CombVar (name, _) => (name, [])
          | CombApp _ => raise Fail "impossible \"CombApp\""
        val arg_site = if site = Top_Level andalso is_tptp_equal s then Eq_Arg
                       else Elsewhere
        val t = mk_const_aterm format type_sys x T_args
                    (map (aux arg_site) args)
        val T = combtyp_of u
      in
        t |> (if should_tag_with_type ctxt nonmono_Ts type_sys site u T then
                tag_with_type ctxt format nonmono_Ts type_sys T
              else
                I)
      end
  in aux end
and formula_from_combformula ctxt format nonmono_Ts type_sys
                             should_predicate_on_var =
  let
    val do_term = term_from_combterm ctxt format nonmono_Ts type_sys Top_Level
    val do_bound_type =
      case type_sys of
        Simple_Types level =>
        homogenized_type ctxt nonmono_Ts level 0
        #> mangled_type format type_sys false 0 #> SOME
      | _ => K NONE
    fun do_out_of_bound_type pos phi universal (name, T) =
      if should_predicate_on_type ctxt nonmono_Ts type_sys
             (fn () => should_predicate_on_var pos phi universal name) T then
        CombVar (name, T)
        |> type_pred_combterm ctxt format type_sys T
        |> do_term |> AAtom |> SOME
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
      | do_formula _ (AAtom tm) = AAtom (do_term tm)
  in do_formula o SOME end

fun bound_tvars type_sys Ts =
  mk_ahorn (map (formula_from_fo_literal o fo_literal_from_type_literal)
                (type_literals_for_types type_sys add_sorts_on_tvar Ts))

fun formula_for_fact ctxt format nonmono_Ts type_sys
                     ({combformula, atomic_types, ...} : translated_formula) =
  combformula
  |> close_combformula_universally
  |> formula_from_combformula ctxt format nonmono_Ts type_sys
                              is_var_nonmonotonic_in_formula true
  |> bound_tvars type_sys atomic_types
  |> close_formula_universally

(* Each fact is given a unique fact number to avoid name clashes (e.g., because
   of monomorphization). The TPTP explicitly forbids name clashes, and some of
   the remote provers might care. *)
fun formula_line_for_fact ctxt format prefix encode freshen nonmono_Ts type_sys
                          (j, formula as {name, locality, kind, ...}) =
  Formula (prefix ^
           (if freshen andalso
               polymorphism_of_type_sys type_sys <> Polymorphic then
              string_of_int j ^ "_"
            else
              "") ^ encode name,
           kind, formula_for_fact ctxt format nonmono_Ts type_sys formula, NONE,
           case locality of
             Intro => intro_info
           | Elim => elim_info
           | Simp => simp_info
           | _ => NONE)

fun formula_line_for_class_rel_clause ({name, subclass, superclass, ...}
                                       : class_rel_clause) =
  let val ty_arg = ATerm (`I "T", []) in
    Formula (class_rel_clause_prefix ^ ascii_of name, Axiom,
             AConn (AImplies, [AAtom (ATerm (subclass, [ty_arg])),
                               AAtom (ATerm (superclass, [ty_arg]))])
             |> close_formula_universally, intro_info, NONE)
  end

fun fo_literal_from_arity_literal (TConsLit (c, t, args)) =
    (true, ATerm (c, [ATerm (t, map (fn arg => ATerm (arg, [])) args)]))
  | fo_literal_from_arity_literal (TVarLit (c, sort)) =
    (false, ATerm (c, [ATerm (sort, [])]))

fun formula_line_for_arity_clause ({name, prem_lits, concl_lits, ...}
                                   : arity_clause) =
  Formula (arity_clause_prefix ^ ascii_of name, Axiom,
           mk_ahorn (map (formula_from_fo_literal o apfst not
                          o fo_literal_from_arity_literal) prem_lits)
                    (formula_from_fo_literal
                         (fo_literal_from_arity_literal concl_lits))
           |> close_formula_universally, intro_info, NONE)

fun formula_line_for_conjecture ctxt format nonmono_Ts type_sys
        ({name, kind, combformula, atomic_types, ...} : translated_formula) =
  Formula (conjecture_prefix ^ name, kind,
           formula_from_combformula ctxt format nonmono_Ts type_sys
               is_var_nonmonotonic_in_formula false
               (close_combformula_universally combformula)
           |> bound_tvars type_sys atomic_types
           |> close_formula_universally, NONE, NONE)

fun free_type_literals type_sys ({atomic_types, ...} : translated_formula) =
  atomic_types |> type_literals_for_types type_sys add_sorts_on_tfree
               |> map fo_literal_from_type_literal

fun formula_line_for_free_type j lit =
  Formula (tfree_clause_prefix ^ string_of_int j, Hypothesis,
           formula_from_fo_literal lit, NONE, NONE)
fun formula_lines_for_free_types type_sys facts =
  let
    val litss = map (free_type_literals type_sys) facts
    val lits = fold (union (op =)) litss []
  in map2 formula_line_for_free_type (0 upto length lits - 1) lits end

(** Symbol declarations **)

fun should_declare_sym type_sys pred_sym s =
  is_tptp_user_symbol s andalso not (String.isPrefix bound_var_prefix s) andalso
  (case type_sys of
     Simple_Types _ => true
   | Tags (_, _, Lightweight) => true
   | _ => not pred_sym)

fun sym_decl_table_for_facts ctxt type_sys repaired_sym_tab (conjs, facts) =
  let
    fun add_combterm in_conj tm =
      let val (head, args) = strip_combterm_comb tm in
        (case head of
           CombConst ((s, s'), T, T_args) =>
           let val pred_sym = is_pred_sym repaired_sym_tab s in
             if should_declare_sym type_sys pred_sym s then
               Symtab.map_default (s, [])
                   (insert_type ctxt #3 (s', T_args, T, pred_sym, length args,
                                         in_conj))
             else
               I
           end
         | _ => I)
        #> fold (add_combterm in_conj) args
      end
    fun add_fact in_conj =
      fact_lift (formula_fold NONE (K (add_combterm in_conj)))
  in
    Symtab.empty
    |> is_type_sys_fairly_sound type_sys
       ? (fold (add_fact true) conjs #> fold (add_fact false) facts)
  end

(* These types witness that the type classes they belong to allow infinite
   models and hence that any types with these type classes is monotonic. *)
val known_infinite_types =
  [@{typ nat}, Type ("Int.int", []), @{typ "nat => bool"}]

(* This inference is described in section 2.3 of Claessen et al.'s "Sorting it
   out with monotonicity" paper presented at CADE 2011. *)
fun add_combterm_nonmonotonic_types _ _ (SOME false) _ = I
  | add_combterm_nonmonotonic_types ctxt level _
        (CombApp (CombApp (CombConst ((s, _), Type (_, [T, _]), _), tm1),
                           tm2)) =
    (is_tptp_equal s andalso exists is_var_or_bound_var [tm1, tm2] andalso
     (case level of
        Nonmonotonic_Types =>
        not (is_type_surely_infinite ctxt known_infinite_types T)
      | Finite_Types => is_type_surely_finite ctxt T
      | _ => true)) ? insert_type ctxt I (deep_freeze_type T)
  | add_combterm_nonmonotonic_types _ _ _ _ = I
fun add_fact_nonmonotonic_types ctxt level ({kind, combformula, ...}
                                            : translated_formula) =
  formula_fold (SOME (kind <> Conjecture))
               (add_combterm_nonmonotonic_types ctxt level) combformula
fun nonmonotonic_types_for_facts ctxt type_sys facts =
  let val level = level_of_type_sys type_sys in
    if level = Nonmonotonic_Types orelse level = Finite_Types then
      [] |> fold (add_fact_nonmonotonic_types ctxt level) facts
         (* We must add "bool" in case the helper "True_or_False" is added
            later. In addition, several places in the code rely on the list of
            nonmonotonic types not being empty. *)
         |> insert_type ctxt I @{typ bool}
    else
      []
  end

fun decl_line_for_sym ctxt format nonmono_Ts type_sys s
                      (s', T_args, T, pred_sym, ary, _) =
  let
    val (T_arg_Ts, level) =
      case type_sys of
        Simple_Types level => ([], level)
      | _ => (replicate (length T_args) homo_infinite_type, No_Types)
  in
    Decl (sym_decl_prefix ^ s, (s, s'),
          (T_arg_Ts ---> (T |> homogenized_type ctxt nonmono_Ts level ary))
          |> mangled_type format type_sys pred_sym (length T_arg_Ts + ary))
  end

fun is_polymorphic_type T = fold_atyps (fn TVar _ => K true | _ => I) T false

fun formula_line_for_preds_sym_decl ctxt format conj_sym_kind nonmono_Ts
        type_sys n s j (s', T_args, T, _, ary, in_conj) =
  let
    val (kind, maybe_negate) =
      if in_conj then (conj_sym_kind, conj_sym_kind = Conjecture ? mk_anot)
      else (Axiom, I)
    val (arg_Ts, res_T) = chop_fun ary T
    val bound_names =
      1 upto length arg_Ts |> map (`I o make_bound_var o string_of_int)
    val bounds =
      bound_names ~~ arg_Ts |> map (fn (name, T) => CombConst (name, T, []))
    val bound_Ts =
      arg_Ts |> map (fn T => if n > 1 orelse is_polymorphic_type T then SOME T
                             else NONE)
  in
    Formula (preds_sym_formula_prefix ^ s ^
             (if n > 1 then "_" ^ string_of_int j else ""), kind,
             CombConst ((s, s'), T, T_args)
             |> fold (curry (CombApp o swap)) bounds
             |> type_pred_combterm ctxt format type_sys res_T
             |> AAtom |> mk_aquant AForall (bound_names ~~ bound_Ts)
             |> formula_from_combformula ctxt format nonmono_Ts type_sys
                                         (K (K (K (K true)))) true
             |> n > 1 ? bound_tvars type_sys (atyps_of T)
             |> close_formula_universally
             |> maybe_negate,
             intro_info, NONE)
  end

fun formula_lines_for_lightweight_tags_sym_decl ctxt format conj_sym_kind
        nonmono_Ts type_sys n s (j, (s', T_args, T, pred_sym, ary, in_conj)) =
  let
    val ident_base =
      lightweight_tags_sym_formula_prefix ^ s ^
      (if n > 1 then "_" ^ string_of_int j else "")
    val (kind, maybe_negate) =
      if in_conj then (conj_sym_kind, conj_sym_kind = Conjecture ? mk_anot)
      else (Axiom, I)
    val (arg_Ts, res_T) = chop_fun ary T
    val bound_names =
      1 upto length arg_Ts |> map (`I o make_bound_var o string_of_int)
    val bounds = bound_names |> map (fn name => ATerm (name, []))
    val cst = mk_const_aterm format type_sys (s, s') T_args
    val atomic_Ts = atyps_of T
    fun eq tms =
      (if pred_sym then AConn (AIff, map AAtom tms)
       else AAtom (ATerm (`I tptp_equal, tms)))
      |> bound_tvars type_sys atomic_Ts
      |> close_formula_universally
      |> maybe_negate
    val should_encode = should_encode_type ctxt nonmono_Ts All_Types
    val tag_with = tag_with_type ctxt format nonmono_Ts type_sys
    val add_formula_for_res =
      if should_encode res_T then
        cons (Formula (ident_base ^ "_res", kind,
                       eq [tag_with res_T (cst bounds), cst bounds],
                       simp_info, NONE))
      else
        I
    fun add_formula_for_arg k =
      let val arg_T = nth arg_Ts k in
        if should_encode arg_T then
          case chop k bounds of
            (bounds1, bound :: bounds2) =>
            cons (Formula (ident_base ^ "_arg" ^ string_of_int (k + 1), kind,
                           eq [cst (bounds1 @ tag_with arg_T bound :: bounds2),
                               cst bounds],
                           simp_info, NONE))
          | _ => raise Fail "expected nonempty tail"
        else
          I
      end
  in
    [] |> not pred_sym ? add_formula_for_res
       |> fold add_formula_for_arg (ary - 1 downto 0)
  end

fun result_type_of_decl (_, _, T, _, ary, _) = chop_fun ary T |> snd

fun problem_lines_for_sym_decls ctxt format conj_sym_kind nonmono_Ts type_sys
                                (s, decls) =
  case type_sys of
    Simple_Types _ =>
    decls |> map (decl_line_for_sym ctxt format nonmono_Ts type_sys s)
  | Preds _ =>
    let
      val decls =
        case decls of
          decl :: (decls' as _ :: _) =>
          let val T = result_type_of_decl decl in
            if forall (curry (type_instance ctxt o swap) T
                       o result_type_of_decl) decls' then
              [decl]
            else
              decls
          end
        | _ => decls
      val n = length decls
      val decls =
        decls
        |> filter (should_predicate_on_type ctxt nonmono_Ts type_sys (K true)
                   o result_type_of_decl)
    in
      (0 upto length decls - 1, decls)
      |-> map2 (formula_line_for_preds_sym_decl ctxt format conj_sym_kind
                                                nonmono_Ts type_sys n s)
    end
  | Tags (_, _, heaviness) =>
    (case heaviness of
       Heavyweight => []
     | Lightweight =>
       let val n = length decls in
         (0 upto n - 1 ~~ decls)
         |> maps (formula_lines_for_lightweight_tags_sym_decl ctxt format
                      conj_sym_kind nonmono_Ts type_sys n s)
       end)

fun problem_lines_for_sym_decl_table ctxt format conj_sym_kind nonmono_Ts
                                     type_sys sym_decl_tab =
  sym_decl_tab
  |> Symtab.dest
  |> sort_wrt fst
  |> rpair []
  |-> fold_rev (append o problem_lines_for_sym_decls ctxt format conj_sym_kind
                                                     nonmono_Ts type_sys)

fun needs_type_tag_idempotence (Tags (poly, level, heaviness)) =
    poly <> Mangled_Monomorphic andalso
    ((level = All_Types andalso heaviness = Lightweight) orelse
     level = Nonmonotonic_Types orelse level = Finite_Types)
  | needs_type_tag_idempotence _ = false

fun offset_of_heading_in_problem _ [] j = j
  | offset_of_heading_in_problem needle ((heading, lines) :: problem) j =
    if heading = needle then j
    else offset_of_heading_in_problem needle problem (j + length lines)

val implicit_declsN = "Should-be-implicit typings"
val explicit_declsN = "Explicit typings"
val factsN = "Relevant facts"
val class_relsN = "Class relationships"
val aritiesN = "Arities"
val helpersN = "Helper facts"
val conjsN = "Conjectures"
val free_typesN = "Type variables"

val explicit_apply = NONE (* for experimental purposes *)

fun prepare_atp_problem ctxt format conj_sym_kind prem_kind type_sys
                        readable_names preproc hyp_ts concl_t facts =
  let
    val (format, type_sys) = choose_format [format] type_sys
    val (fact_names, (conjs, facts, class_rel_clauses, arity_clauses)) =
      translate_formulas ctxt format prem_kind type_sys preproc hyp_ts concl_t
                         facts
    val sym_tab = conjs @ facts |> sym_table_for_facts ctxt explicit_apply
    val nonmono_Ts = conjs @ facts |> nonmonotonic_types_for_facts ctxt type_sys
    val repair = repair_fact ctxt format type_sys sym_tab
    val (conjs, facts) = (conjs, facts) |> pairself (map repair)
    val repaired_sym_tab =
      conjs @ facts |> sym_table_for_facts ctxt (SOME false)
    val helpers =
      repaired_sym_tab |> helper_facts_for_sym_table ctxt format type_sys
                       |> map repair
    val lavish_nonmono_Ts =
      if null nonmono_Ts orelse nonmono_Ts = [@{typ bool}] orelse
         polymorphism_of_type_sys type_sys <> Polymorphic then
        nonmono_Ts
      else
        [TVar (("'a", 0), HOLogic.typeS)]
    val sym_decl_lines =
      (conjs, helpers @ facts)
      |> sym_decl_table_for_facts ctxt type_sys repaired_sym_tab
      |> problem_lines_for_sym_decl_table ctxt format conj_sym_kind
                                          lavish_nonmono_Ts type_sys
    val helper_lines =
      0 upto length helpers - 1 ~~ helpers
      |> map (formula_line_for_fact ctxt format helper_prefix I false
                                    lavish_nonmono_Ts type_sys)
      |> (if needs_type_tag_idempotence type_sys then
            cons (type_tag_idempotence_fact ())
          else
            I)
    (* Reordering these might confuse the proof reconstruction code or the SPASS
       FLOTTER hack. *)
    val problem =
      [(explicit_declsN, sym_decl_lines),
       (factsN,
        map (formula_line_for_fact ctxt format fact_prefix ascii_of true
                                   nonmono_Ts type_sys)
            (0 upto length facts - 1 ~~ facts)),
       (class_relsN, map formula_line_for_class_rel_clause class_rel_clauses),
       (aritiesN, map formula_line_for_arity_clause arity_clauses),
       (helpersN, helper_lines),
       (conjsN,
        map (formula_line_for_conjecture ctxt format nonmono_Ts type_sys)
            conjs),
       (free_typesN, formula_lines_for_free_types type_sys (facts @ conjs))]
    val problem =
      problem
      |> (case format of
            CNF => ensure_cnf_problem
          | CNF_UEQ => filter_cnf_ueq_problem
          | _ => I)
      |> (if is_format_typed format then
            declare_undeclared_syms_in_atp_problem type_decl_prefix
                                                   implicit_declsN
          else
            I)
    val (problem, pool) = problem |> nice_atp_problem readable_names
    val helpers_offset = offset_of_heading_in_problem helpersN problem 0
    val typed_helpers =
      map_filter (fn (j, {name, ...}) =>
                     if String.isSuffix typed_helper_suffix name then SOME j
                     else NONE)
                 ((helpers_offset + 1 upto helpers_offset + length helpers)
                  ~~ helpers)
    fun add_sym_arity (s, {min_ary, ...} : sym_info) =
      if min_ary > 0 then
        case strip_prefix_and_unascii const_prefix s of
          SOME s => Symtab.insert (op =) (s, min_ary)
        | NONE => I
      else
        I
  in
    (problem,
     case pool of SOME the_pool => snd the_pool | NONE => Symtab.empty,
     offset_of_heading_in_problem conjsN problem 0,
     offset_of_heading_in_problem factsN problem 0,
     fact_names |> Vector.fromList,
     typed_helpers,
     Symtab.empty |> Symtab.fold add_sym_arity sym_tab)
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

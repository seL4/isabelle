(*  Title:      Pure/theory.ML
    ID:         $Id$
    Author:     Lawrence C Paulson and Markus Wenzel
    Copyright   1996  University of Cambridge

The abstract type "theory" of theories.
*)

signature BASIC_THEORY =
sig
  type theory
  exception THEORY of string * theory list
  val rep_theory: theory ->
    {sign: Sign.sg,
      axioms: term Symtab.table,
      oracles: ((Sign.sg * Object.T -> term) * stamp) Symtab.table,
      parents: theory list,
      ancestors: theory list}
  val sign_of: theory -> Sign.sg
  val is_draft: theory -> bool
  val syn_of: theory -> Syntax.syntax
  val parents_of: theory -> theory list
  val ancestors_of: theory -> theory list
  val subthy: theory * theory -> bool
  val eq_thy: theory * theory -> bool
  val cert_axm: Sign.sg -> string * term -> string * term
  val read_def_axm: Sign.sg * (indexname -> typ option) * (indexname -> sort option) ->
    string list -> string * string -> string * term
  val read_axm: Sign.sg -> string * string -> string * term
  val inferT_axm: Sign.sg -> string * term -> string * term
end

signature THEORY =
sig
  include BASIC_THEORY
  val axiomK: string
  val oracleK: string
  (*theory extension primitives*)
  val add_classes: (bclass * xclass list) list -> theory -> theory
  val add_classes_i: (bclass * class list) list -> theory -> theory
  val add_classrel: (xclass * xclass) list -> theory -> theory
  val add_classrel_i: (class * class) list -> theory -> theory
  val add_defsort: string -> theory -> theory
  val add_defsort_i: sort -> theory -> theory
  val add_types: (bstring * int * mixfix) list -> theory -> theory
  val add_nonterminals: bstring list -> theory -> theory
  val add_tyabbrs: (bstring * string list * string * mixfix) list
    -> theory -> theory
  val add_tyabbrs_i: (bstring * string list * typ * mixfix) list
    -> theory -> theory
  val add_arities: (xstring * string list * string) list -> theory -> theory
  val add_arities_i: (string * sort list * sort) list -> theory -> theory
  val add_consts: (bstring * string * mixfix) list -> theory -> theory
  val add_consts_i: (bstring * typ * mixfix) list -> theory -> theory
  val add_syntax: (bstring * string * mixfix) list -> theory -> theory
  val add_syntax_i: (bstring * typ * mixfix) list -> theory -> theory
  val add_modesyntax: string * bool -> (bstring * string * mixfix) list -> theory -> theory
  val add_modesyntax_i: string * bool -> (bstring * typ * mixfix) list -> theory -> theory
  val add_trfuns:
    (string * (Syntax.ast list -> Syntax.ast)) list *
    (string * (term list -> term)) list *
    (string * (term list -> term)) list *
    (string * (Syntax.ast list -> Syntax.ast)) list -> theory -> theory
  val add_trfunsT:
    (string * (bool -> typ -> term list -> term)) list -> theory -> theory
  val add_tokentrfuns:
    (string * string * (string -> string * real)) list -> theory -> theory
  val add_mode_tokentrfuns: string -> (string * (string -> string * real)) list
    -> theory -> theory
  val add_trrules: (xstring * string) Syntax.trrule list -> theory -> theory
  val add_trrules_i: Syntax.ast Syntax.trrule list -> theory -> theory
  val add_axioms: (bstring * string) list -> theory -> theory
  val add_axioms_i: (bstring * term) list -> theory -> theory
  val add_oracle: bstring * (Sign.sg * Object.T -> term) -> theory -> theory
  val add_defs: (bstring * string) list -> theory -> theory
  val add_defs_i: (bstring * term) list -> theory -> theory
  val add_path: string -> theory -> theory
  val parent_path: theory -> theory
  val root_path: theory -> theory
  val hide_space: string * xstring list -> theory -> theory
  val hide_space_i: string * string list -> theory -> theory
  val hide_classes: string list -> theory -> theory
  val hide_types: string list -> theory -> theory
  val hide_consts: string list -> theory -> theory
  val add_name: string -> theory -> theory
  val copy: theory -> theory
  val prep_ext: theory -> theory
  val prep_ext_merge: theory list -> theory
  val requires: theory -> string -> string -> unit
  val assert_super: theory -> theory -> theory
  val pre_pure: theory
end;

signature PRIVATE_THEORY =
sig
  include THEORY
  val init_data: Object.kind -> (Object.T * (Object.T -> Object.T) * (Object.T -> Object.T) *
    (Object.T * Object.T -> Object.T) * (Sign.sg -> Object.T -> unit)) -> theory -> theory
  val print_data: Object.kind -> theory -> unit
  val get_data: Object.kind -> (Object.T -> 'a) -> theory -> 'a
  val put_data: Object.kind -> ('a -> Object.T) -> 'a -> theory -> theory
end;


structure Theory: PRIVATE_THEORY =
struct


(** datatype theory **)

datatype theory =
  Theory of {
    sign: Sign.sg,
    axioms: term Symtab.table,
    oracles: ((Sign.sg * Object.T -> term) * stamp) Symtab.table,
    parents: theory list,
    ancestors: theory list};

fun make_theory sign axms oras parents ancestors =
  Theory {sign = sign, axioms = axms, oracles = oras,
    parents = parents, ancestors = ancestors};

fun rep_theory (Theory args) = args;

val sign_of = #sign o rep_theory;
val is_draft = Sign.is_draft o sign_of;
val syn_of = #syn o Sign.rep_sg o sign_of;
val parents_of = #parents o rep_theory;
val ancestors_of = #ancestors o rep_theory;

(*errors involving theories*)
exception THEORY of string * theory list;

(*compare theories*)
val subthy = Sign.subsig o pairself sign_of;
val eq_thy = Sign.eq_sg o pairself sign_of;

(*check for some theory*)
fun requires thy name what =
  if exists (equal name) (Sign.stamp_names_of (sign_of thy)) then ()
  else error ("Require theory " ^ quote name ^ " as an ancestor for " ^ what);

fun assert_super thy1 thy2 =
  if subthy (thy1, thy2) then thy2
  else raise THEORY ("Not a super theory", [thy1, thy2]);

(*partial Pure theory*)
val pre_pure = make_theory Sign.pre_pure Symtab.empty Symtab.empty [] [];



(** extend theory **)

(*name spaces*)
val axiomK = "axiom";
val oracleK = "oracle";


(* extend logical part of a theory *)

fun err_dup_axms names =
  error ("Duplicate axiom name(s) " ^ commas_quote names);

fun err_dup_oras names =
  error ("Duplicate oracles " ^ commas_quote names);

fun ext_theory thy ext_sg new_axms new_oras =
  let
    val Theory {sign, axioms, oracles, parents, ancestors} = thy;
    val draft = Sign.is_draft sign;
    val axioms' =
      Symtab.extend (if draft then axioms else Symtab.empty, new_axms)
        handle Symtab.DUPS names => err_dup_axms names;
    val oracles' =
      Symtab.extend (oracles, new_oras)
        handle Symtab.DUPS names => err_dup_oras names;
    val (parents', ancestors') =
      if draft then (parents, ancestors) else ([thy], thy :: ancestors);
  in
    make_theory (ext_sg sign) axioms' oracles' parents' ancestors'
  end;


(* extend signature of a theory *)

fun ext_sign extfun decls thy = ext_theory thy (extfun decls) [] [];

val add_classes      = ext_sign Sign.add_classes;
val add_classes_i    = ext_sign Sign.add_classes_i;
val add_classrel     = ext_sign Sign.add_classrel;
val add_classrel_i   = ext_sign Sign.add_classrel_i;
val add_defsort      = ext_sign Sign.add_defsort;
val add_defsort_i    = ext_sign Sign.add_defsort_i;
val add_types        = ext_sign Sign.add_types;
val add_nonterminals = ext_sign Sign.add_nonterminals;
val add_tyabbrs      = ext_sign Sign.add_tyabbrs;
val add_tyabbrs_i    = ext_sign Sign.add_tyabbrs_i;
val add_arities      = ext_sign Sign.add_arities;
val add_arities_i    = ext_sign Sign.add_arities_i;
val add_consts       = ext_sign Sign.add_consts;
val add_consts_i     = ext_sign Sign.add_consts_i;
val add_syntax       = ext_sign Sign.add_syntax;
val add_syntax_i     = ext_sign Sign.add_syntax_i;
val add_modesyntax   = curry (ext_sign Sign.add_modesyntax);
val add_modesyntax_i = curry (ext_sign Sign.add_modesyntax_i);
val add_trfuns       = ext_sign Sign.add_trfuns;
val add_trfunsT      = ext_sign Sign.add_trfunsT;
val add_tokentrfuns  = ext_sign Sign.add_tokentrfuns;
fun add_mode_tokentrfuns m = add_tokentrfuns o map (fn (s, f) => (m, s, f));
val add_trrules      = ext_sign Sign.add_trrules;
val add_trrules_i    = ext_sign Sign.add_trrules_i;
val add_path         = ext_sign Sign.add_path;
val parent_path      = add_path "..";
val root_path        = add_path "/";
val add_space        = ext_sign Sign.add_space;
val hide_space       = ext_sign Sign.hide_space;
val hide_space_i     = ext_sign Sign.hide_space_i;
val hide_classes     = curry hide_space_i Sign.classK;
val hide_types       = curry hide_space_i Sign.typeK;
val hide_consts      = curry hide_space_i Sign.constK;
val add_name         = ext_sign Sign.add_name;
val copy             = ext_sign (K Sign.copy) ();
val prep_ext         = ext_sign (K Sign.prep_ext) ();



(** add axioms **)

(* prepare axioms *)

fun err_in_axm name =
  error ("The error(s) above occurred in axiom " ^ quote name);

fun no_vars tm =
  if null (term_vars tm) andalso null (term_tvars tm) then tm
  else error "Illegal schematic variable(s) in term";

fun cert_axm sg (name, raw_tm) =
  let
    val (t, T, _) = Sign.certify_term sg raw_tm
      handle TYPE (msg, _, _) => error msg
           | TERM (msg, _) => error msg;
  in
    assert (T = propT) "Term not of type prop";
    (name, no_vars t)
  end
  handle ERROR => err_in_axm name;

(*some duplication of code with read_def_cterm*)
fun read_def_axm (sg, types, sorts) used (name, str) =
  let
    val ts = Syntax.read (#syn (Sign.rep_sg sg)) propT str;
    val (t, _) = Sign.infer_types sg types sorts used true (ts, propT);
  in cert_axm sg (name,t) end
  handle ERROR => err_in_axm name;

fun read_axm sg name_str = read_def_axm (sg, K None, K None) [] name_str;

fun inferT_axm sg (name, pre_tm) =
  let
    val (t, _) = Sign.infer_types sg (K None) (K None) [] true ([pre_tm], propT);
  in (name, no_vars t) end
  handle ERROR => err_in_axm name;


(* extend axioms of a theory *)

fun ext_axms prep_axm raw_axms (thy as Theory {sign, ...}) =
  let
    val raw_axms' = map (apfst (Sign.full_name sign)) raw_axms;
    val axioms =
      map (apsnd (Term.compress_term o Logic.varify) o prep_axm sign) raw_axms';
    val ext_sg = Sign.add_space (axiomK, map fst axioms);
  in
    ext_theory thy ext_sg axioms []
  end;

val add_axioms = ext_axms read_axm;
val add_axioms_i = ext_axms cert_axm;


(* add oracle **)

fun add_oracle (raw_name, oracle) (thy as Theory {sign, ...}) =
  let
    val name = Sign.full_name sign raw_name;
    val ext_sg = Sign.add_space (oracleK, [name]);
  in
    ext_theory thy ext_sg [] [(name, (oracle, stamp ()))]
  end;



(** add constant definitions **)

(* all_axioms_of *)

(*results may contain duplicates!*)

fun all_axioms_of thy =
  flat (map (Symtab.dest o #axioms o rep_theory) (thy :: ancestors_of thy));


(* clash_types, clash_consts *)

(*check if types have common instance (ignoring sorts)*)

fun clash_types ty1 ty2 =
  let
    val ty1' = Type.varifyT ty1;
    val ty2' = incr_tvar (maxidx_of_typ ty1' + 1) (Type.varifyT ty2);
  in
    Type.raw_unify (ty1', ty2')
  end;

fun clash_consts (c1, ty1) (c2, ty2) =
  c1 = c2 andalso clash_types ty1 ty2;


(* clash_defns *)

fun clash_defn c_ty (name, tm) =
  let val (c, ty') = dest_Const (head_of (fst (Logic.dest_equals tm))) in
    if clash_consts c_ty (c, ty') then Some (name, ty') else None
  end handle TERM _ => None;

fun clash_defns c_ty axms =
  distinct (mapfilter (clash_defn c_ty) axms);


(* dest_defn *)

fun dest_defn tm =
  let
    fun err msg = raise TERM (msg, [tm]);

    val (lhs, rhs) = Logic.dest_equals (Logic.strip_imp_concl tm)
      handle TERM _ => err "Not a meta-equality (==)";
    val (head, args) = strip_comb lhs;
    val (c, ty) = dest_Const head
      handle TERM _ => err "Head of lhs not a constant";

    fun occs_const (Const c_ty') = (c_ty' = (c, ty))
      | occs_const (Abs (_, _, t)) = occs_const t
      | occs_const (t $ u) = occs_const t orelse occs_const u
      | occs_const _ = false;

    fun dest_free (Free (x, _)) = x
      | dest_free (Const ("TYPE", Type ("itself", [TFree (x, _)]))) = x
      | dest_free _ = raise Match;

    val show_frees = commas_quote o map dest_free;
    val show_tfrees = commas_quote o map fst;

    val lhs_dups = duplicates args;
    val rhs_extras = gen_rems (op =) (term_frees rhs, args);
    val rhs_extrasT = gen_rems (op =) (term_tfrees rhs, typ_tfrees ty);
  in
    if not (forall (can dest_free) args) then
      err "Arguments (on lhs) must be variables"
    else if not (null lhs_dups) then
      err ("Duplicate variables on lhs: " ^ show_frees lhs_dups)
    else if not (null rhs_extras) then
      err ("Extra variables on rhs: " ^ show_frees rhs_extras)
    else if not (null rhs_extrasT) then
      err ("Extra type variables on rhs: " ^ show_tfrees rhs_extrasT)
    else if occs_const rhs then
      err ("Constant to be defined occurs on rhs")
    else (c, ty)
  end;


(* check_defn *)

fun err_in_defn sg name msg =
  (error_msg msg; error ("The error(s) above occurred in definition " ^
    quote (Sign.full_name sg name)));

fun check_defn sign (axms, (name, tm)) =
  let
    fun show_const (c, ty) = quote (Pretty.string_of (Pretty.block
      [Pretty.str (c ^ " ::"), Pretty.brk 1, Sign.pretty_typ sign ty]));

    fun show_defn c (dfn, ty') = show_const (c, ty') ^ " in " ^ dfn;
    fun show_defns c = cat_lines o map (show_defn c);

    val (c, ty) = dest_defn tm
      handle TERM (msg, _) => err_in_defn sign name msg;
    val defns = clash_defns (c, ty) axms;
  in
    if not (null defns) then
      err_in_defn sign name ("Definition of " ^ show_const (c, ty) ^
        "\nclashes with " ^ show_defns c defns)
    else (name, tm) :: axms
  end;


(* add_defs *)

fun ext_defns prep_axm raw_axms thy =
  let
    val axms = map (prep_axm (sign_of thy)) raw_axms;
    val all_axms = all_axioms_of thy;
  in
    foldl (check_defn (sign_of thy)) (all_axms, axms);
    add_axioms_i axms thy
  end;

val add_defs_i = ext_defns cert_axm;
val add_defs = ext_defns read_axm;



(** additional theory data **)

val init_data = curry (ext_sign Sign.init_data);
fun print_data kind = Sign.print_data kind o sign_of;
fun get_data kind f = Sign.get_data kind f o sign_of;
fun put_data kind f = ext_sign (Sign.put_data kind f);



(** merge theories **)          (*exception ERROR*)

fun merge_sign (sg, thy) =
  Sign.nontriv_merge (sg, sign_of thy) handle TERM (msg, _) => error msg;

(*merge list of theories from left to right, preparing extend*)
fun prep_ext_merge thys =
  if null thys then
    error "Merge: no parent theories"
  else if exists is_draft thys then
    error "Attempt to merge draft theories"
  else
    let
      val sign' =
        foldl merge_sign (sign_of (hd thys), tl thys)
        |> Sign.prep_ext
        |> Sign.add_path "/";

      val axioms' = Symtab.empty;

      fun eq_ora ((_, (_, s1: stamp)), (_, (_, s2))) = s1 = s2;
      val oracles' =
        Symtab.make (gen_distinct eq_ora
          (flat (map (Symtab.dest o #oracles o rep_theory) thys)))
        handle Symtab.DUPS names => err_dup_oras names;

      val parents' = gen_distinct eq_thy thys;
      val ancestors' =
        gen_distinct eq_thy (parents' @ flat (map ancestors_of thys));
    in
      make_theory sign' axioms' oracles' parents' ancestors'
    end;


end;

structure BasicTheory: BASIC_THEORY = Theory;
open BasicTheory;

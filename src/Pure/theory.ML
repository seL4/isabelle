(*  Title:      Pure/theory.ML
    ID:         $Id$
    Author:     Lawrence C Paulson and Markus Wenzel
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

The abstract type "theory" of theories.
*)

signature BASIC_THEORY =
sig
  type theory
  exception THEORY of string * theory list
  val rep_theory: theory ->
    {sign: Sign.sg,
      const_deps: unit Graph.T,
      final_consts: typ list Symtab.table,
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
  val add_advanced_trfuns:
    (string * (Sign.sg -> Syntax.ast list -> Syntax.ast)) list *
    (string * (Sign.sg -> term list -> term)) list *
    (string * (Sign.sg -> term list -> term)) list *
    (string * (Sign.sg -> Syntax.ast list -> Syntax.ast)) list -> theory -> theory
  val add_advanced_trfunsT:
    (string * (Sign.sg -> bool -> typ -> term list -> term)) list -> theory -> theory
  val add_tokentrfuns:
    (string * string * (string -> string * real)) list -> theory -> theory
  val add_mode_tokentrfuns: string -> (string * (string -> string * real)) list
    -> theory -> theory
  val add_trrules: (xstring * string) Syntax.trrule list -> theory -> theory
  val add_trrules_i: Syntax.ast Syntax.trrule list -> theory -> theory
  val add_axioms: (bstring * string) list -> theory -> theory
  val add_axioms_i: (bstring * term) list -> theory -> theory
  val add_oracle: bstring * (Sign.sg * Object.T -> term) -> theory -> theory
  val add_finals: bool -> string list -> theory -> theory
  val add_finals_i: bool -> term list -> theory -> theory
  val add_defs: bool -> (bstring * string) list -> theory -> theory
  val add_defs_i: bool -> (bstring * term) list -> theory -> theory
  val add_path: string -> theory -> theory
  val parent_path: theory -> theory
  val root_path: theory -> theory
  val absolute_path: theory -> theory
  val hide_space: bool -> string * xstring list -> theory -> theory
  val hide_space_i: bool -> string * string list -> theory -> theory
  val hide_classes: bool -> string list -> theory -> theory
  val hide_types: bool -> string list -> theory -> theory
  val hide_consts: bool -> string list -> theory -> theory
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

(*Note: dependencies are only tracked for non-overloaded constant definitions*)

datatype theory =
  Theory of {
    sign: Sign.sg,
    const_deps: unit Graph.T,
    final_consts: typ list Symtab.table,
    axioms: term Symtab.table,
    oracles: ((Sign.sg * Object.T -> term) * stamp) Symtab.table,
    parents: theory list,
    ancestors: theory list};

fun make_theory sign const_deps final_consts axioms oracles parents ancestors =
  Theory {sign = sign, const_deps = const_deps, final_consts = final_consts, axioms = axioms,
    oracles = oracles,  parents = parents, ancestors = ancestors};

fun rep_theory (Theory args) = args;

val sign_of = #sign o rep_theory;
val is_draft = Sign.is_draft o sign_of;
val syn_of = Sign.syn_of o sign_of;
val parents_of = #parents o rep_theory;
val ancestors_of = #ancestors o rep_theory;

(*errors involving theories*)
exception THEORY of string * theory list;

(*compare theories*)
val subthy = Sign.subsig o pairself sign_of;
val eq_thy = Sign.eq_sg o pairself sign_of;

(*check for some theory*)
fun requires thy name what =
  if Sign.exists_stamp name (sign_of thy) then ()
  else error ("Require theory " ^ quote name ^ " as an ancestor for " ^ what);

fun assert_super thy1 thy2 =
  if subthy (thy1, thy2) then thy2
  else raise THEORY ("Not a super theory", [thy1, thy2]);

(*partial Pure theory*)
val pre_pure =
  make_theory Sign.pre_pure Graph.empty Symtab.empty Symtab.empty Symtab.empty [] [];



(** extend theory **)

(*name spaces*)
val axiomK = "axiom";
val oracleK = "oracle";


(* extend logical part of a theory *)

fun err_dup_axms names =
  error ("Duplicate axiom name(s): " ^ commas_quote names);

fun err_dup_oras names =
  error ("Duplicate oracles: " ^ commas_quote names);

fun ext_theory thy ext_sg ext_deps new_axms new_oras =
  let
    val Theory {sign, const_deps, final_consts, axioms, oracles, parents, ancestors} = thy;
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
    make_theory (ext_sg sign) (ext_deps const_deps) final_consts axioms' oracles' parents' ancestors'
  end;


(* extend signature of a theory *)

fun ext_sign extfun decls thy = ext_theory thy (extfun decls) I [] [];

val add_classes            = ext_sign Sign.add_classes;
val add_classes_i          = ext_sign Sign.add_classes_i;
val add_classrel           = ext_sign Sign.add_classrel;
val add_classrel_i         = ext_sign Sign.add_classrel_i;
val add_defsort            = ext_sign Sign.add_defsort;
val add_defsort_i          = ext_sign Sign.add_defsort_i;
val add_types              = ext_sign Sign.add_types;
val add_nonterminals       = ext_sign Sign.add_nonterminals;
val add_tyabbrs            = ext_sign Sign.add_tyabbrs;
val add_tyabbrs_i          = ext_sign Sign.add_tyabbrs_i;
val add_arities            = ext_sign Sign.add_arities;
val add_arities_i          = ext_sign Sign.add_arities_i;
val add_consts             = ext_sign Sign.add_consts;
val add_consts_i           = ext_sign Sign.add_consts_i;
val add_syntax             = ext_sign Sign.add_syntax;
val add_syntax_i           = ext_sign Sign.add_syntax_i;
val add_modesyntax         = curry (ext_sign Sign.add_modesyntax);
val add_modesyntax_i       = curry (ext_sign Sign.add_modesyntax_i);
val add_trfuns             = ext_sign Sign.add_trfuns;
val add_trfunsT            = ext_sign Sign.add_trfunsT;
val add_advanced_trfuns    = ext_sign Sign.add_advanced_trfuns;
val add_advanced_trfunsT   = ext_sign Sign.add_advanced_trfunsT;
val add_tokentrfuns        = ext_sign Sign.add_tokentrfuns;
fun add_mode_tokentrfuns m = add_tokentrfuns o map (fn (s, f) => (m, s, f));
val add_trrules            = ext_sign Sign.add_trrules;
val add_trrules_i          = ext_sign Sign.add_trrules_i;
val add_path               = ext_sign Sign.add_path;
val parent_path            = add_path "..";
val root_path              = add_path "/";
val absolute_path          = add_path "//";
val add_space              = ext_sign Sign.add_space;
val hide_space             = ext_sign o Sign.hide_space;
val hide_space_i           = ext_sign o Sign.hide_space_i;
fun hide_classes b         = curry (hide_space_i b) Sign.classK;
fun hide_types b           = curry (hide_space_i b) Sign.typeK;
fun hide_consts b          = curry (hide_space_i b) Sign.constK;
val add_name               = ext_sign Sign.add_name;
val copy                   = ext_sign (K Sign.copy) ();
val prep_ext               = ext_sign (K Sign.prep_ext) ();



(** add axioms **)

(* prepare axioms *)

fun err_in_axm name =
  error ("The error(s) above occurred in axiom " ^ quote name);

fun no_vars sg tm = (case (term_vars tm, term_tvars tm) of
    ([], []) => tm
  | (ts, ixns) => error (Pretty.string_of (Pretty.block (Pretty.breaks
      (Pretty.str "Illegal schematic variable(s) in term:" ::
       map (Sign.pretty_term sg) ts @
       map (Sign.pretty_typ sg o TVar) ixns)))));

fun cert_axm sg (name, raw_tm) =
  let
    val (t, T, _) = Sign.certify_term (Sign.pp sg) sg raw_tm
      handle TYPE (msg, _, _) => error msg
           | TERM (msg, _) => error msg;
  in
    Term.no_dummy_patterns t handle TERM (msg, _) => error msg;
    assert (T = propT) "Term not of type prop";
    (name, no_vars sg t)
  end;

(*some duplication of code with read_def_cterm*)
fun read_def_axm (sg, types, sorts) used (name, str) =
  let
    val ts = Syntax.read (Sign.syn_of sg) propT str;
    val (t, _) = Sign.infer_types (Sign.pp sg) sg types sorts used true (ts, propT);
  in cert_axm sg (name, t) end
  handle ERROR => err_in_axm name;

fun read_axm sg name_str = read_def_axm (sg, K None, K None) [] name_str;

fun inferT_axm sg (name, pre_tm) =
  let val (t, _) = Sign.infer_types (Sign.pp sg) sg
    (K None) (K None) [] true ([pre_tm], propT);
  in (name, no_vars sg t) end
  handle ERROR => err_in_axm name;


(* extend axioms of a theory *)

fun ext_axms prep_axm raw_axms (thy as Theory {sign, ...}) =
  let
    val raw_axms' = map (apfst (Sign.full_name sign)) raw_axms;
    val axioms =
      map (apsnd (Term.compress_term o Logic.varify) o prep_axm sign) raw_axms';
    val ext_sg = Sign.add_space (axiomK, map fst axioms);
  in ext_theory thy ext_sg I axioms [] end;

val add_axioms = ext_axms read_axm;
val add_axioms_i = ext_axms cert_axm;


(* add oracle **)

fun add_oracle (raw_name, oracle) (thy as Theory {sign, ...}) =
  let
    val name = Sign.full_name sign raw_name;
    val ext_sg = Sign.add_space (oracleK, [name]);
  in ext_theory thy ext_sg I [] [(name, (oracle, stamp ()))] end;



(** add constant definitions **)

(* clash_types, clash_consts *)

(*check if types have common instance (ignoring sorts)*)

fun clash_types ty1 ty2 =
  let
    val ty1' = Type.varifyT ty1;
    val ty2' = incr_tvar (maxidx_of_typ ty1' + 1) (Type.varifyT ty2);
  in Type.raw_unify (ty1', ty2') end;

fun clash_consts (c1, ty1) (c2, ty2) =
  c1 = c2 andalso clash_types ty1 ty2;


(* clash_defns *)

fun clash_defn c_ty (name, tm) =
  let val (c, ty') = dest_Const (head_of (fst (Logic.dest_equals (Logic.strip_imp_concl tm)))) in
    if clash_consts c_ty (c, ty') then Some (name, ty') else None
  end handle TERM _ => None;

fun clash_defns c_ty axms =
  distinct (mapfilter (clash_defn c_ty) axms);


(* overloading *)

datatype overloading = NoOverloading | Useless | Plain;

fun overloading sg declT defT =
  let val T = Term.incr_tvar (maxidx_of_typ declT + 1) (Type.varifyT defT) in
    if Sign.typ_instance sg (declT, T) then NoOverloading
    else if Sign.typ_instance sg (Type.strip_sorts declT, Type.strip_sorts T) then Useless
    else Plain
  end;


(* dest_defn *)

fun dest_defn tm =
  let
    fun err msg = raise TERM (msg, [tm]);

    val (lhs, rhs) = Logic.dest_equals (Logic.strip_imp_concl tm)
      handle TERM _ => err "Not a meta-equality (==)";
    val (head, args) = strip_comb lhs;
    val c_ty as (c, ty) = dest_Const head
      handle TERM _ => err "Head of lhs not a constant";

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
    else if exists_Const (fn c_ty' => c_ty' = c_ty) rhs then
      err ("Constant to be defined occurs on rhs")
    else (c_ty, rhs)
  end;


(* check_defn *)

fun err_in_defn sg name msg =
  (error_msg msg;
    error ("The error(s) above occurred in definition " ^ quote (Sign.full_name sg name)));

fun cycle_msg namess = "Cyclic dependency of constants:\n" ^
  cat_lines (map (space_implode " -> " o map quote o rev) namess);

fun add_deps (c, cs) deps =
  let fun declare (G, x) = Graph.new_node (x, ()) G handle Graph.DUP _ => G
  in foldl declare (deps, c :: cs) |> Graph.add_deps_acyclic (c, cs) end;

fun check_defn sg overloaded final_consts ((deps, axms), def as (name, tm)) =
  let
    fun is_final (c, ty) =
      case Symtab.lookup(final_consts,c) of
        Some [] => true
      | Some tys => exists (curry (Sign.typ_instance sg) ty) tys
      | None => false;

    fun pretty_const (c, ty) = [Pretty.str c, Pretty.str " ::", Pretty.brk 1,
      Pretty.quote (Sign.pretty_typ sg (#1 (Type.freeze_thaw_type ty)))];

    fun def_txt (c_ty, txt) = Pretty.block
      (Pretty.str "Definition of " :: pretty_const c_ty @
        (if txt = "" then [] else [Pretty.str txt]));

    fun show_defn c (dfn, ty') = Pretty.block
      (Pretty.str "  " :: pretty_const (c, ty') @ [Pretty.str " in ", Pretty.str dfn]);

    val (c_ty as (c, ty), rhs) = dest_defn tm
      handle TERM (msg, _) => err_in_defn sg name msg;
    val c_decl =
      (case Sign.const_type sg c of Some T => T
      | None => err_in_defn sg name ("Undeclared constant " ^ quote c));

    val clashed = clash_defns c_ty axms;
  in
    if not (null clashed) then
      err_in_defn sg name (Pretty.string_of (Pretty.chunks
        (def_txt (c_ty, " clashes with") :: map (show_defn c) clashed)))
    else if is_final c_ty then
      err_in_defn sg name (Pretty.string_of (Pretty.block
        ([Pretty.str "The constant",Pretty.brk 1] @
	 pretty_const c_ty @
	 [Pretty.brk 1,Pretty.str "has been declared final"])))
    else
      (case overloading sg c_decl ty of
        NoOverloading =>
          (add_deps (c, Term.term_consts rhs) deps
              handle Graph.CYCLES namess => err_in_defn sg name (cycle_msg namess),
            def :: axms)
      | Useless =>
           err_in_defn sg name (Pretty.string_of (Pretty.chunks
             [Library.setmp show_sorts true def_txt (c_ty, ""), Pretty.str
                 "imposes additional sort constraints on the declared type of the constant"]))
      | Plain =>
         (if not overloaded then warning (Pretty.string_of (Pretty.chunks
           [def_txt (c_ty, ""), Pretty.str ("is strictly less general than the declared type (see "
               ^ quote (Sign.full_name sg name) ^ ")")]))
         else (); (deps, def :: axms)))
  end;


(* add_defs *)

fun ext_defns prep_axm overloaded raw_axms thy =
  let
    val Theory {sign, const_deps, final_consts, axioms, oracles, parents, ancestors} = thy;
    val all_axioms = flat (map (Symtab.dest o #axioms o rep_theory) (thy :: ancestors));

    val axms = map (prep_axm sign) raw_axms;
    val (const_deps', _) = foldl (check_defn sign overloaded final_consts) ((const_deps, all_axioms), axms);
  in
    make_theory sign const_deps' final_consts axioms oracles parents ancestors
    |> add_axioms_i axms
  end;

val add_defs_i = ext_defns cert_axm;
val add_defs = ext_defns read_axm;


(* add_finals *)

fun ext_finals prep_term overloaded raw_terms thy =
  let
    val Theory {sign, const_deps, final_consts, axioms, oracles, parents, ancestors} = thy;
    fun mk_final (finals,tm) =
      let
        fun err msg = raise TERM(msg,[tm]);
        val (c,ty) = dest_Const tm
          handle TERM _ => err "Can only make constants final";
        val c_decl =
          (case Sign.const_type sign c of Some T => T
          | None => err ("Undeclared constant " ^ quote c));
        val simple =
	  case overloading sign c_decl ty of
	    NoOverloading => true
	  | Useless => err "Sort restrictions too strong"
	  | Plain => if overloaded then false
		     else err "Type is more general than declared";
        val typ_instance = Sign.typ_instance sign;
      in
        if simple then
	  (case Symtab.lookup(finals,c) of
	    Some [] => err "Constant already final"
	  | _ => Symtab.update((c,[]),finals))
	else
	  (case Symtab.lookup(finals,c) of
	    Some [] => err "Constant already completely final"
          | Some tys => if exists (curry typ_instance ty) tys
			then err "Instance of constant is already final"
			else Symtab.update((c,ty::gen_rem typ_instance (tys,ty)),finals)
	  | None => Symtab.update((c,[ty]),finals))
      end;
    val consts = map (prep_term sign) raw_terms;
    val final_consts' = foldl mk_final (final_consts,consts);
  in
    make_theory sign const_deps final_consts' axioms oracles parents ancestors
  end;

local
  fun read_term sg = Sign.simple_read_term sg TypeInfer.logicT;
  fun cert_term sg = #1 o Sign.certify_term (Sign.pp sg) sg;
in
val add_finals = ext_finals read_term;
val add_finals_i = ext_finals cert_term;
end;

fun merge_final sg =
  let
    fun merge_single (tys,ty) =
      if exists (curry (Sign.typ_instance sg) ty) tys
      then tys
      else (ty::gen_rem (Sign.typ_instance sg) (tys,ty));
    fun merge ([],_) = []
      | merge (_,[]) = []
      | merge input = foldl merge_single input;
  in
    Some o merge
  end;


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

      val depss = map (#const_deps o rep_theory) thys;
      val deps' = foldl (Graph.merge_acyclic (K true)) (hd depss, tl depss)
        handle Graph.CYCLES namess => error (cycle_msg namess);

      val final_constss = map (#final_consts o rep_theory) thys;
      val final_consts' = foldl (Symtab.join (merge_final sign')) (hd final_constss,
								   tl final_constss);
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
      make_theory sign' deps' final_consts' axioms' oracles' parents' ancestors'
    end;


end;

structure BasicTheory: BASIC_THEORY = Theory;
open BasicTheory;

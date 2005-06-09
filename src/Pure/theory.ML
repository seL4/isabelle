(*  Title:      Pure/theory.ML
    ID:         $Id$
    Author:     Lawrence C Paulson and Markus Wenzel

The abstract type "theory" of theories.
*)

signature BASIC_THEORY =
sig
  type theory
  exception THEORY of string * theory list
  val rep_theory: theory ->
    {sign: Sign.sg,
      defs: Defs.graph,
      axioms: term NameSpace.table,
      oracles: ((Sign.sg * Object.T -> term) * stamp) NameSpace.table,
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
  val axioms_of: theory -> (string * term) list
  val all_axioms_of: theory -> (string * term) list
  val add_classes: (bstring * xstring list) list -> theory -> theory
  val add_classes_i: (bstring * class list) list -> theory -> theory
  val add_classrel: (xstring * xstring) list -> theory -> theory
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
  val del_modesyntax: string * bool -> (bstring * string * mixfix) list -> theory -> theory
  val del_modesyntax_i: string * bool -> (bstring * typ * mixfix) list -> theory -> theory
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
  val qualified_names: theory -> theory
  val no_base_names: theory -> theory
  val custom_accesses: (string list -> string list list) -> theory -> theory
  val set_policy: (string -> bstring -> string) * (string list -> string list list) ->
    theory -> theory
  val restore_naming: theory -> theory -> theory
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

datatype theory =
  Theory of {
    sign: Sign.sg,
    defs: Defs.graph,
    axioms: term NameSpace.table,
    oracles: ((Sign.sg * Object.T -> term) * stamp) NameSpace.table,
    parents: theory list,
    ancestors: theory list};

fun make_theory sign defs axioms oracles parents ancestors =
  Theory {sign = sign, defs = defs, axioms = axioms,
    oracles = oracles, parents = parents, ancestors = ancestors};

fun rep_theory (Theory args) = args;

val sign_of = #sign o rep_theory;
val is_draft = Sign.is_draft o sign_of;
val syn_of = Sign.syn_of o sign_of;
val parents_of = #parents o rep_theory;
val ancestors_of = #ancestors o rep_theory;

val axioms_of = Symtab.dest o #2 o #axioms o rep_theory;
fun all_axioms_of thy = List.concat (map axioms_of (thy :: ancestors_of thy));

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
  make_theory Sign.pre_pure Defs.empty NameSpace.empty_table NameSpace.empty_table [] [];



(** extend theory **)

(* extend logical part of a theory *)

fun err_dup_axms dups = error ("Duplicate axiom(s): " ^ commas_quote dups);
fun err_dup_oras dups = error ("Duplicate oracle(s): " ^ commas_quote dups);

fun ext_theory thy ext_sg axms oras =
  let
    val Theory {sign, defs, axioms, oracles, parents, ancestors} = thy;
    val draft = Sign.is_draft sign;
    val naming = Sign.naming_of sign;

    val axioms' = NameSpace.extend_table naming
        (if draft then axioms else NameSpace.empty_table, axms)
      handle Symtab.DUPS dups => err_dup_axms dups;
    val oracles' = NameSpace.extend_table naming (oracles, oras)
      handle Symtab.DUPS dups => err_dup_oras dups;

    val (parents', ancestors') =
      if draft then (parents, ancestors) else ([thy], thy :: ancestors);
  in make_theory (ext_sg sign) defs axioms' oracles' parents' ancestors' end;


(* extend signature of a theory *)

fun ext_sign ext_sg args thy = ext_theory thy (ext_sg args) [] [];

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
val del_modesyntax         = curry (ext_sign Sign.del_modesyntax);
val del_modesyntax_i       = curry (ext_sign Sign.del_modesyntax_i);
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
val qualified_names        = ext_sign (K Sign.qualified_names) ();
val no_base_names          = ext_sign (K Sign.no_base_names) ();
val custom_accesses        = ext_sign Sign.custom_accesses;
val set_policy             = ext_sign Sign.set_policy;
val restore_naming         = ext_sign Sign.restore_naming o sign_of;
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

fun no_vars pp tm =
  (case (Term.term_vars tm, Term.term_tvars tm) of
    ([], []) => tm
  | (ts, ixns) => error (Pretty.string_of (Pretty.block (Pretty.breaks
      (Pretty.str "Illegal schematic variable(s) in term:" ::
       map (Pretty.term pp) ts @ map (Pretty.typ pp o TVar) ixns)))));

fun cert_axm sg (name, raw_tm) =
  let
    val pp = Sign.pp sg;
    val (t, T, _) = Sign.certify_term pp sg raw_tm
      handle TYPE (msg, _, _) => error msg
        | TERM (msg, _) => error msg;
  in
    Term.no_dummy_patterns t handle TERM (msg, _) => error msg;
    assert (T = propT) "Term not of type prop";
    (name, no_vars pp t)
  end;

(*some duplication of code with read_def_cterm*)
fun read_def_axm (sg, types, sorts) used (name, str) =
  let
    val ts = Syntax.read (Sign.is_logtype sg) (Sign.syn_of sg) propT str;
    val (t, _) = Sign.infer_types (Sign.pp sg) sg types sorts used true (ts, propT);
  in cert_axm sg (name, t) end
  handle ERROR => err_in_axm name;

fun read_axm sg name_str = read_def_axm (sg, K NONE, K NONE) [] name_str;

fun inferT_axm sg (name, pre_tm) =
  let
    val pp = Sign.pp sg;
    val (t, _) = Sign.infer_types pp sg (K NONE) (K NONE) [] true ([pre_tm], propT);
  in (name, no_vars pp t) end
  handle ERROR => err_in_axm name;


(* extend axioms of a theory *)

local

fun gen_add_axioms prep_axm raw_axms thy =
  let
    val sg = sign_of thy;
    val axms = map (apsnd (Term.compress_term o Logic.varify) o prep_axm sg) raw_axms;
  in ext_theory thy I axms [] end;

in

val add_axioms = gen_add_axioms read_axm;
val add_axioms_i = gen_add_axioms cert_axm;

end;


(* add oracle **)

fun add_oracle (bname, oracle) thy =
  ext_theory thy I [] [(bname, (oracle, stamp ()))];



(** add constant definitions **)

(* overloading *)

datatype overloading = Clean | Implicit | Useless;

fun overloading sg overloaded declT defT =
  let
    val defT' = Term.incr_tvar (maxidx_of_typ declT + 1) (Type.varifyT defT);
  in
    if Sign.typ_instance sg (declT, defT') then Clean
    else if Sign.typ_instance sg (Type.strip_sorts declT, Type.strip_sorts defT') then Useless
    else if overloaded then Clean
    else Implicit
  end;


(* dest_def *)

fun dest_def pp tm =
  let
    fun err msg = raise TERM (msg, [tm]);

    val (lhs, rhs) = Logic.dest_equals (Logic.strip_imp_concl tm)
      handle TERM _ => err "Not a meta-equality (==)";
    val (head, args) = Term.strip_comb lhs;
    val (c, T) = Term.dest_Const head
      handle TERM _ => err "Head of lhs not a constant";

    fun dest_free (Free (x, _)) = x
      | dest_free (Const ("TYPE", Type ("itself", [TFree (x, _)]))) = x
      | dest_free _ = raise Match;

    val show_terms = commas_quote o map (Pretty.string_of_term pp);
    val show_frees = commas_quote o map dest_free;
    val show_tfrees = commas_quote o map fst;

    val lhs_nofrees = filter (not o can dest_free) args;
    val lhs_dups = duplicates args;
    val rhs_extras = term_frees rhs |> fold (remove op =) args;
    val rhs_extrasT = term_tfrees rhs |> fold (remove op =) (typ_tfrees T);
  in
    if not (null lhs_nofrees) then
      err ("Non-variables as arguments on lhs: " ^ show_terms lhs_nofrees)
    else if not (null lhs_dups) then
      err ("Duplicate variables on lhs: " ^ show_frees lhs_dups)
    else if not (null rhs_extras) then
      err ("Extra variables on rhs: " ^ show_frees rhs_extras)
    else if not (null rhs_extrasT) then
      err ("Extra type variables on rhs: " ^ show_tfrees rhs_extrasT)
    else if exists_Const (equal (c, T)) rhs then
      err ("Constant to be defined occurs on rhs")
    else ((c, T), rhs)
  end;


(* check_def *)

fun pretty_const pp (c, T) =
 [Pretty.str c, Pretty.str " ::", Pretty.brk 1,
  Pretty.quote (Pretty.typ pp (Type.freeze_type T))];    (* FIXME zero indexes!? *)

(* FIXME move error messages to defs.ML !? *)

fun pretty_path pp path = fold_rev (fn (T, c, def) =>
  fn [] => [Pretty.block (pretty_const pp (c, T))]
   | prts => Pretty.block (pretty_const pp (c, T) @
      [Pretty.brk 1, Pretty.str ("depends via " ^ quote def ^ " on")]) :: prts) path [];

fun chain_history_msg s = 
    if Defs.chain_history () then s^": " 
    else s^" (set DEFS_CHAIN_HISTORY=ON for full history): "

fun defs_circular pp path =
  Pretty.str (chain_history_msg "Cyclic dependency of definitions") :: pretty_path pp path
  |> Pretty.chunks |> Pretty.string_of;

fun defs_infinite_chain pp path =
  Pretty.str (chain_history_msg "Infinite chain of definitions") :: pretty_path pp path
  |> Pretty.chunks |> Pretty.string_of;

fun defs_clash def1 def2 = "Type clash in definitions " ^ quote def1 ^ " and " ^ quote def2;

fun defs_final pp const =
  (Pretty.str "Attempt to define final constant" :: Pretty.brk 1 :: pretty_const pp const)
  |> Pretty.block |> Pretty.string_of;

(* FIXME move to defs.ML; avoid exceptions *)
fun declare sg c defs =
  let val T = Sign.the_const_type sg c
  in if_none (try (Defs.declare defs) (c, T)) defs end;


fun check_def sg overloaded (bname, tm) defs =
  let
    val pp = Sign.pp sg;
    val name = Sign.full_name sg bname;

    fun err msg = error (Pretty.string_of (Pretty.chunks
     [Pretty.str msg,
      Pretty.block [Pretty.str ("The error(s) above occurred in definition " ^ quote name ^ ":"),
        Pretty.fbrk, Pretty.quote (Pretty.term pp tm)]]));

    fun show_def const txt =
      [Pretty.block (Pretty.str "Definition of " :: pretty_const pp const), Pretty.str txt]
      |> Pretty.chunks |> Pretty.string_of;

    val ((c, defT), rhs) = dest_def pp tm handle TERM (msg, _) => err msg;
    val rhs_consts = Term.term_constsT rhs;
    val declT = Sign.the_const_type sg c;

    val _ =
      (case overloading sg overloaded declT defT of
        Clean => ()
      | Implicit => warning (show_def (c, defT)
          ("is strictly less general than the declared type (see " ^ quote name ^ ")"))
      | Useless => err (Library.setmp show_sorts true (show_def (c, defT))
          "imposes additional sort constraints on the declared type of the constant"));

    val decl_defs = defs |> declare sg c |> fold (declare sg) (map #1 rhs_consts);
  in
    Defs.define decl_defs (c, defT) name rhs_consts
      handle Defs.DEFS msg => err ("DEFS: " ^ msg)   (* FIXME sys_error!? *)
        | Defs.CIRCULAR path => err (defs_circular pp path)
        | Defs.INFINITE_CHAIN path => err (defs_infinite_chain pp path)
        | Defs.CLASH (_, def1, def2) => err (defs_clash def1 def2)
        | Defs.FINAL const => err (defs_final pp const)
  end;


(* add_defs *)

local

fun gen_add_defs prep_axm overloaded raw_axms thy =
  let
    val Theory {sign, defs, axioms, oracles, parents, ancestors} = thy;
    val axms = map (prep_axm sign) raw_axms;
    val defs' = fold (check_def sign overloaded) axms defs;
  in
    make_theory sign defs' axioms oracles parents ancestors
    |> add_axioms_i axms
  end;

in

val add_defs_i = gen_add_defs cert_axm;
val add_defs = gen_add_defs read_axm;

end;


(* add_finals *)

local

fun gen_add_finals prep_term overloaded raw_terms thy =
  let
    val Theory {sign, defs, axioms, oracles, parents, ancestors} = thy;
    fun finalize tm finals =
      let
        fun err msg = raise TERM (msg, [tm]);    (* FIXME error!? *)
        val (c, defT) =
          (case tm of Const x => x
          | Free _ => err "Attempt to finalize variable (or undeclared constant)"
          | _ => err "Attempt to finalize non-constant term");
        val declT = Sign.the_const_type sign c
          handle TYPE (msg, _, _) => err msg;
        val _ =
          (case overloading sign overloaded declT defT of
            Clean => ()
          | Implcit => warning ("Finalizing " ^ quote c ^
              " at a strictly less general type than declared")
          | Useless => err "Sort constraints stronger than declared");
      in
        Defs.finalize (if_none (try (Defs.declare finals) (c, declT)) finals) (c, defT)
      end;
    val defs' = fold finalize (map (prep_term sign) raw_terms) defs;
  in make_theory sign defs' axioms oracles parents ancestors end;

fun read_term sg = Sign.simple_read_term sg TypeInfer.logicT;
fun cert_term sg = #1 o Sign.certify_term (Sign.pp sg) sg;

in

val add_finals = gen_add_finals read_term;
val add_finals_i = gen_add_finals cert_term;

end;



(** additional theory data **)

val init_data = curry (ext_sign Sign.init_data);
fun print_data kind = Sign.print_data kind o sign_of;
fun get_data kind f = Sign.get_data kind f o sign_of;
fun put_data kind f = ext_sign (Sign.put_data kind f);



(** merge theories **)          (*exception ERROR*)

(*merge list of theories from left to right, preparing extend*)
fun prep_ext_merge thys =
  let
    val sign' = Sign.prep_ext_merge (map sign_of thys);

    val defss = map (#defs o rep_theory) thys;
    val defs' = foldl (uncurry Defs.merge) (hd defss) (tl defss)
      handle Defs.CIRCULAR namess => error (defs_circular (Sign.pp sign') namess)
        | Defs.INFINITE_CHAIN namess => error (defs_infinite_chain (Sign.pp sign') namess);

    val axioms' = NameSpace.empty_table;

    val oras_spaces = map (#1 o #oracles o rep_theory) thys;
    val oras_space' = Library.foldl NameSpace.merge (hd oras_spaces, tl oras_spaces);
    fun eq_ora ((_, (_, s1: stamp)), (_, (_, s2))) = s1 = s2;
    val oras' =
      Symtab.make (gen_distinct eq_ora
        (List.concat (map (Symtab.dest o #2 o #oracles o rep_theory) thys)))
      handle Symtab.DUPS names => err_dup_oras names;
    val oracles' = (oras_space', oras');

    val parents' = gen_distinct eq_thy thys;
    val ancestors' =
      gen_distinct eq_thy (parents' @ List.concat (map ancestors_of thys));
  in make_theory sign' defs' axioms' oracles' parents' ancestors' end;


end;

structure BasicTheory: BASIC_THEORY = Theory;
open BasicTheory;

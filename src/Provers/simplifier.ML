(*  Title:      Provers/simplifier.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Generic simplifier, suitable for most logics.  See Pure/meta_simplifier.ML
for the actual meta-level rewriting engine.
*)

signature BASIC_SIMPLIFIER =
sig
  type simproc = MetaSimplifier.simproc
  val mk_simproc: string -> cterm list
    -> (Sign.sg -> thm list -> term -> thm option) -> simproc
  type solver = MetaSimplifier.solver
  val mk_solver: string -> (thm list -> int -> tactic) -> solver
  type simpset = MetaSimplifier.simpset
  val empty_ss: simpset
  val rep_ss: simpset ->
   {mss: MetaSimplifier.meta_simpset,
    mk_cong: thm -> thm,
    subgoal_tac: simpset -> int -> tactic,
    loop_tacs: (string * (int -> tactic)) list,
    unsafe_solvers: solver list,
    solvers: solver list};
  val print_ss: simpset -> unit
  val print_simpset: theory -> unit
  val setsubgoaler: simpset *  (simpset -> int -> tactic) -> simpset
  val setloop:      simpset *             (int -> tactic) -> simpset
  val addloop:      simpset *  (string * (int -> tactic)) -> simpset
  val delloop:      simpset *   string                    -> simpset
  val setSSolver:   simpset * solver -> simpset
  val addSSolver:   simpset * solver -> simpset
  val setSolver:    simpset * solver -> simpset
  val addSolver:    simpset * solver -> simpset
  val setmksimps:   simpset * (thm -> thm list) -> simpset
  val setmkeqTrue:  simpset * (thm -> thm option) -> simpset
  val setmkcong:    simpset * (thm -> thm) -> simpset
  val setmksym:     simpset * (thm -> thm option) -> simpset
  val settermless:  simpset * (term * term -> bool) -> simpset
  val addsimps:     simpset * thm list -> simpset
  val delsimps:     simpset * thm list -> simpset
  val addeqcongs:   simpset * thm list -> simpset
  val deleqcongs:   simpset * thm list -> simpset
  val addcongs:     simpset * thm list -> simpset
  val delcongs:     simpset * thm list -> simpset
  val addsimprocs:  simpset * simproc list -> simpset
  val delsimprocs:  simpset * simproc list -> simpset
  val merge_ss:     simpset * simpset -> simpset
  val prems_of_ss:  simpset -> thm list
  val simpset_ref_of_sg: Sign.sg -> simpset ref
  val simpset_ref_of: theory -> simpset ref
  val simpset_of_sg: Sign.sg -> simpset
  val simpset_of: theory -> simpset
  val SIMPSET: (simpset -> tactic) -> tactic
  val SIMPSET': (simpset -> 'a -> tactic) -> 'a -> tactic
  val simpset: unit -> simpset
  val simpset_ref: unit -> simpset ref
  val Addsimps: thm list -> unit
  val Delsimps: thm list -> unit
  val Addsimprocs: simproc list -> unit
  val Delsimprocs: simproc list -> unit
  val Addcongs: thm list -> unit
  val Delcongs: thm list -> unit
  val generic_simp_tac: bool -> bool * bool * bool -> simpset -> int -> tactic
  val safe_asm_full_simp_tac: simpset -> int -> tactic
  val               simp_tac: simpset -> int -> tactic
  val           asm_simp_tac: simpset -> int -> tactic
  val          full_simp_tac: simpset -> int -> tactic
  val        asm_lr_simp_tac: simpset -> int -> tactic
  val      asm_full_simp_tac: simpset -> int -> tactic
  val               Simp_tac:            int -> tactic
  val           Asm_simp_tac:            int -> tactic
  val          Full_simp_tac:            int -> tactic
  val        Asm_lr_simp_tac:            int -> tactic
  val      Asm_full_simp_tac:            int -> tactic
  val          simplify: simpset -> thm -> thm
  val      asm_simplify: simpset -> thm -> thm
  val     full_simplify: simpset -> thm -> thm
  val   asm_lr_simplify: simpset -> thm -> thm
  val asm_full_simplify: simpset -> thm -> thm
end;

signature SIMPLIFIER =
sig
  include BASIC_SIMPLIFIER
  val simproc: Sign.sg -> string -> string list
    -> (Sign.sg -> thm list -> term -> thm option) -> simproc
  val simproc_i: Sign.sg -> string -> term list
    -> (Sign.sg -> thm list -> term -> thm option) -> simproc
  val          rewrite: simpset -> cterm -> thm
  val      asm_rewrite: simpset -> cterm -> thm
  val     full_rewrite: simpset -> cterm -> thm
  val   asm_lr_rewrite: simpset -> cterm -> thm
  val asm_full_rewrite: simpset -> cterm -> thm
  val print_local_simpset: Proof.context -> unit
  val get_local_simpset: Proof.context -> simpset
  val put_local_simpset: simpset -> Proof.context -> Proof.context
  val change_global_ss: (simpset * thm list -> simpset) -> theory attribute
  val change_local_ss: (simpset * thm list -> simpset) -> Proof.context attribute
  val simp_add_global: theory attribute
  val simp_del_global: theory attribute
  val simp_add_local: Proof.context attribute
  val simp_del_local: Proof.context attribute
  val cong_add_global: theory attribute
  val cong_del_global: theory attribute
  val cong_add_local: Proof.context attribute
  val cong_del_local: Proof.context attribute
  val change_simpset_of: (simpset * 'a -> simpset) -> 'a -> theory -> theory
  val simp_modifiers: (Args.T list -> (Method.modifier * Args.T list)) list
  val setup: (theory -> theory) list
  val method_setup: (Args.T list -> (Method.modifier * Args.T list)) list
    -> (theory -> theory) list
  val easy_setup: thm -> thm list -> (theory -> theory) list
end;

structure Simplifier: SIMPLIFIER =
struct

(* Compatibility *)
open MetaSimplifier;

(** global and local simpset data **)

(* theory data kind 'Provers/simpset' *)

structure GlobalSimpsetArgs =
struct
  val name = "Provers/simpset";
  type T = simpset ref;

  val empty = ref empty_ss;
  fun copy (ref ss) = (ref ss): T;            (*create new reference!*)
  val prep_ext = copy;
  fun merge (ref ss1, ref ss2) = ref (merge_ss (ss1, ss2));
  fun print _ (ref ss) = print_ss ss;
end;

structure GlobalSimpset = TheoryDataFun(GlobalSimpsetArgs);
val print_simpset = GlobalSimpset.print;
val simpset_ref_of_sg = GlobalSimpset.get_sg;
val simpset_ref_of = GlobalSimpset.get;


(* access global simpset *)

val simpset_of_sg = ! o simpset_ref_of_sg;
val simpset_of = simpset_of_sg o Theory.sign_of;

fun SIMPSET tacf state = tacf (simpset_of_sg (Thm.sign_of_thm state)) state;
fun SIMPSET' tacf i state = tacf (simpset_of_sg (Thm.sign_of_thm state)) i state;

val simpset = simpset_of o Context.the_context;
val simpset_ref = simpset_ref_of_sg o Theory.sign_of o Context.the_context;


(* change global simpset *)

fun change_simpset_of f x thy =
  let val r = simpset_ref_of thy
  in r := f (! r, x); thy end;

fun change_simpset f x = (change_simpset_of f x (Context.the_context ()); ());

val Addsimps = change_simpset (op addsimps);
val Delsimps = change_simpset (op delsimps);
val Addsimprocs = change_simpset (op addsimprocs);
val Delsimprocs = change_simpset (op delsimprocs);
val Addcongs = change_simpset (op addcongs);
val Delcongs = change_simpset (op delcongs);


(* proof data kind 'Provers/simpset' *)

structure LocalSimpsetArgs =
struct
  val name = "Provers/simpset";
  type T = simpset;
  val init = simpset_of;
  fun print _ ss = print_ss ss;
end;

structure LocalSimpset = ProofDataFun(LocalSimpsetArgs);
val print_local_simpset = LocalSimpset.print;
val get_local_simpset = LocalSimpset.get;
val put_local_simpset = LocalSimpset.put;
fun map_local_simpset f ctxt = put_local_simpset (f (get_local_simpset ctxt)) ctxt;


(* attributes *)

fun change_global_ss f (thy, th) =
  let val r = simpset_ref_of thy
  in r := f (! r, [th]); (thy, th) end;

fun change_local_ss f (ctxt, th) =
  let val ss = f (get_local_simpset ctxt, [th])
  in (put_local_simpset ss ctxt, th) end;

val simp_add_global = change_global_ss (op addsimps);
val simp_del_global = change_global_ss (op delsimps);
val simp_add_local = change_local_ss (op addsimps);
val simp_del_local = change_local_ss (op delsimps);

val cong_add_global = change_global_ss (op addcongs);
val cong_del_global = change_global_ss (op delcongs);
val cong_add_local = change_local_ss (op addcongs);
val cong_del_local = change_local_ss (op delcongs);


val simp_tac = generic_simp_tac false (false, false, false);
val asm_simp_tac = generic_simp_tac false (false, true, false);
val full_simp_tac = generic_simp_tac false (true, false, false);
val asm_lr_simp_tac = generic_simp_tac false (true, true, false);
val asm_full_simp_tac = generic_simp_tac false (true, true, true);
val safe_asm_full_simp_tac = generic_simp_tac true (true, true, true);



(*the abstraction over the proof state delays the dereferencing*)
fun          Simp_tac i st =          simp_tac (simpset ()) i st;
fun      Asm_simp_tac i st =      asm_simp_tac (simpset ()) i st;
fun     Full_simp_tac i st =     full_simp_tac (simpset ()) i st;
fun   Asm_lr_simp_tac i st =   asm_lr_simp_tac (simpset ()) i st;
fun Asm_full_simp_tac i st = asm_full_simp_tac (simpset ()) i st;

val          simplify = simp_thm (false, false, false);
val      asm_simplify = simp_thm (false, true, false);
val     full_simplify = simp_thm (true, false, false);
val   asm_lr_simplify = simp_thm (true, true, false);
val asm_full_simplify = simp_thm (true, true, true);

val          rewrite = simp_cterm (false, false, false);
val      asm_rewrite = simp_cterm (false, true, false);
val     full_rewrite = simp_cterm (true, false, false);
val   asm_lr_rewrite = simp_cterm (true, true, false);
val asm_full_rewrite = simp_cterm (true, true, true);



(** concrete syntax of attributes **)

(* add / del *)

val simpN = "simp";
val congN = "cong";
val addN = "add";
val delN = "del";
val onlyN = "only";
val no_asmN = "no_asm";
val no_asm_useN = "no_asm_use";
val no_asm_simpN = "no_asm_simp";
val asm_lrN = "asm_lr";

val simp_attr =
 (Attrib.add_del_args simp_add_global simp_del_global,
  Attrib.add_del_args simp_add_local simp_del_local);

val cong_attr =
 (Attrib.add_del_args cong_add_global cong_del_global,
  Attrib.add_del_args cong_add_local cong_del_local);


(* conversions *)

local

fun conv_mode x =
  ((Args.parens (Args.$$$ no_asmN) >> K simplify ||
    Args.parens (Args.$$$ no_asm_simpN) >> K asm_simplify ||
    Args.parens (Args.$$$ no_asm_useN) >> K full_simplify ||
    Scan.succeed asm_full_simplify) |> Scan.lift) x;

fun simplified_att get args =
  Attrib.syntax (conv_mode -- args >> (fn (f, ths) =>
    Drule.rule_attribute (fn x => f ((if null ths then I else clear_ss) (get x) addsimps ths))));

in

val simplified_attr =
 (simplified_att simpset_of Attrib.global_thmss,
  simplified_att get_local_simpset Attrib.local_thmss);

end;


(* setup_attrs *)

val setup_attrs = Attrib.add_attributes
 [(simpN, simp_attr, "declaration of simplification rule"),
  (congN, cong_attr, "declaration of Simplifier congruence rule"),
  ("simplified", simplified_attr, "simplified rule")];



(** proof methods **)

(* simplification *)

val simp_options =
 (Args.parens (Args.$$$ no_asmN) >> K simp_tac ||
  Args.parens (Args.$$$ no_asm_simpN) >> K asm_simp_tac ||
  Args.parens (Args.$$$ no_asm_useN) >> K full_simp_tac ||
  Args.parens (Args.$$$ asm_lrN) >> K asm_lr_simp_tac ||
  Scan.succeed asm_full_simp_tac);

val cong_modifiers =
 [Args.$$$ congN -- Args.colon >> K ((I, cong_add_local):Method.modifier),
  Args.$$$ congN -- Args.add -- Args.colon >> K (I, cong_add_local),
  Args.$$$ congN -- Args.del -- Args.colon >> K (I, cong_del_local)];

val simp_modifiers =
 [Args.$$$ simpN -- Args.colon >> K (I, simp_add_local),
  Args.$$$ simpN -- Args.add -- Args.colon >> K (I, simp_add_local),
  Args.$$$ simpN -- Args.del -- Args.colon >> K (I, simp_del_local),
  Args.$$$ simpN -- Args.$$$ onlyN -- Args.colon >> K (map_local_simpset clear_ss, simp_add_local)]
   @ cong_modifiers;

val simp_modifiers' =
 [Args.add -- Args.colon >> K (I, simp_add_local),
  Args.del -- Args.colon >> K (I, simp_del_local),
  Args.$$$ onlyN -- Args.colon >> K (map_local_simpset clear_ss, simp_add_local)]
   @ cong_modifiers;

fun simp_args more_mods =
  Method.sectioned_args (Args.bang_facts -- Scan.lift simp_options) (more_mods @ simp_modifiers');


fun simp_method (prems, tac) ctxt = Method.METHOD (fn facts =>
  ALLGOALS (Method.insert_tac (prems @ facts)) THEN
    (CHANGED_PROP o ALLGOALS o tac) (get_local_simpset ctxt));

fun simp_method' (prems, tac) ctxt = Method.METHOD (fn facts =>
  HEADGOAL (Method.insert_tac (prems @ facts) THEN'
      (CHANGED_PROP oo tac) (get_local_simpset ctxt)));


(* setup_methods *)

fun setup_methods more_mods = Method.add_methods
 [(simpN, simp_args more_mods simp_method', "simplification"),
  ("simp_all", simp_args more_mods simp_method, "simplification (all goals)")];



(** theory setup **)

val setup = [GlobalSimpset.init, LocalSimpset.init, setup_attrs];
fun method_setup mods = [setup_methods mods];

fun easy_setup reflect trivs =
  let
    val trivialities = Drule.reflexive_thm :: trivs;

    fun unsafe_solver_tac prems = FIRST' [resolve_tac (trivialities @ prems), assume_tac];
    val unsafe_solver = mk_solver "easy unsafe" unsafe_solver_tac;

    (*no premature instantiation of variables during simplification*)
    fun safe_solver_tac prems = FIRST' [match_tac (trivialities @ prems), eq_assume_tac];
    val safe_solver = mk_solver "easy safe" safe_solver_tac;

    fun mk_eq thm =
      if Logic.is_equals (Thm.concl_of thm) then [thm]
      else [thm RS reflect] handle THM _ => [];

    fun mksimps thm = mk_eq (Drule.forall_elim_vars (#maxidx (Thm.rep_thm thm) + 1) thm);

    fun init_ss thy =
      (simpset_ref_of thy :=
        empty_ss setsubgoaler asm_simp_tac
        setSSolver safe_solver
        setSolver unsafe_solver
        setmksimps mksimps; thy);
  in setup @ method_setup [] @ [init_ss] end;



(** outer syntax **)

val print_simpsetP =
  OuterSyntax.improper_command "print_simpset" "print context of Simplifier"
    OuterSyntax.Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_context o (Toplevel.keep
      (Toplevel.node_case print_simpset (print_local_simpset o Proof.context_of)))));

val _ = OuterSyntax.add_parsers [print_simpsetP];

end;


structure BasicSimplifier: BASIC_SIMPLIFIER = Simplifier;
open BasicSimplifier;

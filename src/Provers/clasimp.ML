(*  Title:      Provers/clasimp.ML
    Author:     David von Oheimb, TU Muenchen

Combination of classical reasoner and simplifier (depends on
splitter.ML, classical.ML, blast.ML).
*)

infix 4 addSIs2 addSEs2 addSDs2 addIs2 addEs2 addDs2 addsimps2 delsimps2
  addSss addss addss' addIffs delIffs;

signature CLASIMP_DATA =
sig
  structure Splitter: SPLITTER
  structure Classical: CLASSICAL
  structure Blast: BLAST
  sharing type Classical.claset = Blast.claset
  val notE: thm
  val iffD1: thm
  val iffD2: thm
end

signature CLASIMP =
sig
  include CLASIMP_DATA
  type claset
  type clasimpset
  val get_css: Context.generic -> clasimpset
  val map_css: (clasimpset -> clasimpset) -> Context.generic -> Context.generic
  val change_clasimpset: (clasimpset -> clasimpset) -> unit
  val clasimpset: unit -> clasimpset
  val local_clasimpset_of: Proof.context -> clasimpset
  val addSIs2: clasimpset * thm list -> clasimpset
  val addSEs2: clasimpset * thm list -> clasimpset
  val addSDs2: clasimpset * thm list -> clasimpset
  val addIs2: clasimpset * thm list -> clasimpset
  val addEs2: clasimpset * thm list -> clasimpset
  val addDs2: clasimpset * thm list -> clasimpset
  val addsimps2: clasimpset * thm list -> clasimpset
  val delsimps2: clasimpset * thm list -> clasimpset
  val addSss: claset * simpset -> claset
  val addss: claset * simpset -> claset
  val addss': claset * simpset -> claset
  val addIffs: clasimpset * thm list -> clasimpset
  val delIffs: clasimpset * thm list -> clasimpset
  val AddIffs: thm list -> unit
  val DelIffs: thm list -> unit
  val CLASIMPSET: (clasimpset -> tactic) -> tactic
  val CLASIMPSET': (clasimpset -> 'a -> tactic) -> 'a -> tactic
  val clarsimp_tac: clasimpset -> int -> tactic
  val Clarsimp_tac: int -> tactic
  val mk_auto_tac: clasimpset -> int -> int -> tactic
  val auto_tac: clasimpset -> tactic
  val Auto_tac: tactic
  val auto: unit -> unit
  val force_tac: clasimpset  -> int -> tactic
  val Force_tac: int -> tactic
  val force: int -> unit
  val fast_simp_tac: clasimpset -> int -> tactic
  val slow_simp_tac: clasimpset -> int -> tactic
  val best_simp_tac: clasimpset -> int -> tactic
  val attrib: (clasimpset * thm list -> clasimpset) -> attribute
  val iff_add: attribute
  val iff_add': attribute
  val iff_del: attribute
  val iff_modifiers: Method.modifier parser list
  val clasimp_modifiers: Method.modifier parser list
  val clasimp_setup: theory -> theory
end;

functor ClasimpFun(Data: CLASIMP_DATA): CLASIMP =
struct

open Data;


(* type clasimpset *)

type claset = Classical.claset;
type clasimpset = claset * simpset;

fun get_css context = (Classical.get_cs context, Simplifier.get_ss context);

fun map_css f context =
  let val (cs', ss') = f (get_css context)
  in context |> Classical.map_cs (K cs') |> Simplifier.map_ss (K ss') end;

fun change_clasimpset f = Context.>> (fn context => (Context.the_theory context; map_css f context));
fun clasimpset () = (Classical.claset (), Simplifier.simpset ());

fun local_clasimpset_of ctxt =
  (Classical.local_claset_of ctxt, Simplifier.local_simpset_of ctxt);


(* clasimpset operations *)

(*this interface for updating a clasimpset is rudimentary and just for
  convenience for the most common cases*)

fun pair_upd1 f ((a, b), x) = (f (a, x), b);
fun pair_upd2 f ((a, b), x) = (a, f (b, x));

fun op addSIs2   arg = pair_upd1 Classical.addSIs arg;
fun op addSEs2   arg = pair_upd1 Classical.addSEs arg;
fun op addSDs2   arg = pair_upd1 Classical.addSDs arg;
fun op addIs2    arg = pair_upd1 Classical.addIs arg;
fun op addEs2    arg = pair_upd1 Classical.addEs arg;
fun op addDs2    arg = pair_upd1 Classical.addDs arg;
fun op addsimps2 arg = pair_upd2 Simplifier.addsimps arg;
fun op delsimps2 arg = pair_upd2 Simplifier.delsimps arg;

(*not totally safe: may instantiate unknowns that appear also in other subgoals*)
val safe_asm_full_simp_tac = Simplifier.generic_simp_tac true (true,true,true);

(*Add a simpset to a classical set!*)
(*Caution: only one simpset added can be added by each of addSss and addss*)
fun cs addSss ss = Classical.addSafter (cs, ("safe_asm_full_simp_tac",
                            CHANGED o safe_asm_full_simp_tac ss));
fun cs addss  ss = Classical.addbefore  (cs, ("asm_full_simp_tac",
                            CHANGED o Simplifier.asm_full_simp_tac ss));
fun cs addss' ss = Classical.addbefore  (cs, ("asm_full_simp_tac",
                            CHANGED o Simplifier.asm_lr_simp_tac ss));

(* iffs: addition of rules to simpsets and clasets simultaneously *)

(*Takes (possibly conditional) theorems of the form A<->B to
        the Safe Intr     rule B==>A and
        the Safe Destruct rule A==>B.
  Also ~A goes to the Safe Elim rule A ==> ?R
  Failing other cases, A is added as a Safe Intr rule*)
local

fun addIff decls1 decls2 simp ((cs, ss), th) =
  let
    val n = nprems_of th;
    val (elim, intro) = if n = 0 then decls1 else decls2;
    val zero_rotate = zero_var_indexes o rotate_prems n;
  in
    (elim (intro (cs, [zero_rotate (th RS iffD2)]),
           [Tactic.make_elim (zero_rotate (th RS iffD1))])
      handle THM _ => (elim (cs, [zero_rotate (th RS notE)])
        handle THM _ => intro (cs, [th])),
     simp (ss, [th]))
  end;

fun delIff delcs delss ((cs, ss), th) =
  let val zero_rotate = zero_var_indexes o rotate_prems (nprems_of th) in
    (delcs (cs, [zero_rotate (th RS iffD2),
        Tactic.make_elim (zero_rotate (th RS iffD1))])
      handle THM _ => (delcs (cs, [zero_rotate (th RS notE)])
        handle THM _ => delcs (cs, [th])),
     delss (ss, [th]))
  end;

fun modifier att (x, ths) =
  fst (Library.foldl_map (Library.apply [att]) (x, rev ths));

val addXIs = modifier (ContextRules.intro_query NONE);
val addXEs = modifier (ContextRules.elim_query NONE);
val addXDs = modifier (ContextRules.dest_query NONE);
val delXs = modifier ContextRules.rule_del;

in

val op addIffs =
  Library.foldl
      (addIff (Classical.addSEs, Classical.addSIs)
              (Classical.addEs, Classical.addIs)
              Simplifier.addsimps);
val op delIffs = Library.foldl (delIff Classical.delrules Simplifier.delsimps);

fun AddIffs thms = change_clasimpset (fn css => css addIffs thms);
fun DelIffs thms = change_clasimpset (fn css => css delIffs thms);

fun addIffs_generic (x, ths) =
  Library.foldl (addIff (addXEs, addXIs) (addXEs, addXIs) #1) ((x, ()), ths) |> #1;

fun delIffs_generic (x, ths) =
  Library.foldl (delIff delXs #1) ((x, ()), ths) |> #1;

end;


(* tacticals *)

fun CLASIMPSET tacf state =
  Classical.CLASET (fn cs => Simplifier.SIMPSET (fn ss => tacf (cs, ss))) state;

fun CLASIMPSET' tacf i state =
  Classical.CLASET (fn cs => Simplifier.SIMPSET (fn ss => tacf (cs, ss) i)) state;


fun clarsimp_tac (cs, ss) =
  safe_asm_full_simp_tac ss THEN_ALL_NEW
  Classical.clarify_tac (cs addSss ss);

fun Clarsimp_tac i = clarsimp_tac (clasimpset ()) i;


(* auto_tac *)

fun blast_depth_tac cs m i thm =
    Blast.depth_tac cs m i thm
      handle Blast.TRANS s => (warning ("Blast_tac: " ^ s); Seq.empty);

(* a variant of depth_tac that avoids interference of the simplifier
   with dup_step_tac when they are combined by auto_tac *)
local
fun slow_step_tac' cs = Classical.appWrappers cs
        (Classical.instp_step_tac cs APPEND' Classical.haz_step_tac cs);
in fun nodup_depth_tac cs m i state = SELECT_GOAL
   (Classical.safe_steps_tac cs 1 THEN_ELSE
        (DEPTH_SOLVE (nodup_depth_tac cs m 1),
         Classical.inst0_step_tac cs 1 APPEND COND (K (m=0)) no_tac
             (slow_step_tac' cs 1 THEN DEPTH_SOLVE (nodup_depth_tac cs (m-1) 1))
        )) i state;
end;

(*Designed to be idempotent, except if blast_depth_tac instantiates variables
  in some of the subgoals*)
fun mk_auto_tac (cs, ss) m n =
    let val cs' = cs addss ss
        val maintac =
          blast_depth_tac cs m               (* fast but can't use wrappers *)
          ORELSE'
          (CHANGED o nodup_depth_tac cs' n); (* slower but more general *)
    in  EVERY [ALLGOALS (Simplifier.asm_full_simp_tac ss),
               TRY (Classical.safe_tac cs),
               REPEAT (FIRSTGOAL maintac),
               TRY (Classical.safe_tac (cs addSss ss)),
               prune_params_tac]
    end;

fun auto_tac css = mk_auto_tac css 4 2;
fun Auto_tac st = auto_tac (clasimpset ()) st;
fun auto () = by Auto_tac;


(* force_tac *)

(* aimed to solve the given subgoal totally, using whatever tools possible *)
fun force_tac (cs,ss) = let val cs' = cs addss ss in SELECT_GOAL (EVERY [
        Classical.clarify_tac cs' 1,
        IF_UNSOLVED (Simplifier.asm_full_simp_tac ss 1),
        ALLGOALS (Classical.first_best_tac cs')]) end;
fun Force_tac i = force_tac (clasimpset ()) i;
fun force i = by (Force_tac i);


(* basic combinations *)

fun ADDSS tac (cs, ss) = let val cs' = cs addss ss in tac cs' end;

val fast_simp_tac = ADDSS Classical.fast_tac;
val slow_simp_tac = ADDSS Classical.slow_tac;
val best_simp_tac = ADDSS Classical.best_tac;


(* access clasimpset *)



(* attributes *)

fun attrib f = Thm.declaration_attribute (fn th => map_css (fn css => f (css, [th])));
fun attrib' f (x, th) = (f (x, [th]), th);

val iff_add = attrib (op addIffs);
val iff_add' = attrib' addIffs_generic;
val iff_del = attrib (op delIffs) o attrib' delIffs_generic;

fun iff_att x = (Scan.lift
 (Args.del >> K iff_del ||
  Scan.option Args.add -- Args.query >> K iff_add' ||
  Scan.option Args.add >> K iff_add)) x;


(* method modifiers *)

val iffN = "iff";

val iff_modifiers =
 [Args.$$$ iffN -- Scan.option Args.add -- Args.colon >> K ((I, iff_add): Method.modifier),
  Args.$$$ iffN -- Scan.option Args.add -- Args.query_colon >> K (I, iff_add'),
  Args.$$$ iffN -- Args.del -- Args.colon >> K (I, iff_del)];

val clasimp_modifiers =
  Simplifier.simp_modifiers @ Splitter.split_modifiers @
  Classical.cla_modifiers @ iff_modifiers;


(* methods *)

fun clasimp_meth tac prems ctxt = METHOD (fn facts =>
  ALLGOALS (Method.insert_tac (prems @ facts)) THEN tac (local_clasimpset_of ctxt));

fun clasimp_meth' tac prems ctxt = METHOD (fn facts =>
  HEADGOAL (Method.insert_tac (prems @ facts) THEN' tac (local_clasimpset_of ctxt)));

val clasimp_method = Method.bang_sectioned_args clasimp_modifiers o clasimp_meth;
val clasimp_method' = Method.bang_sectioned_args clasimp_modifiers o clasimp_meth';


fun auto_args m =
  Method.bang_sectioned_args' clasimp_modifiers
    (Scan.lift (Scan.option (OuterParse.nat -- OuterParse.nat))) m;

fun auto_meth NONE = clasimp_meth (CHANGED_PROP o auto_tac)
  | auto_meth (SOME (m, n)) = clasimp_meth (CHANGED_PROP o (fn css => mk_auto_tac css m n));


(* theory setup *)

val clasimp_setup =
 (Attrib.setup @{binding iff} iff_att "declaration of Simplifier / Classical rules" #>
  Method.add_methods
   [("fastsimp", clasimp_method' fast_simp_tac, "combined fast and simp"),
    ("slowsimp", clasimp_method' slow_simp_tac, "combined slow and simp"),
    ("bestsimp", clasimp_method' best_simp_tac, "combined best and simp"),
    ("force", clasimp_method' force_tac, "force"),
    ("auto", auto_args auto_meth, "auto"),
    ("clarsimp", clasimp_method' (CHANGED_PROP oo clarsimp_tac), "clarify simplified goal")]);

end;

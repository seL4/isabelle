(*  Title:      Provers/simplifier.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1993  TU Munich

Generic simplifier, suitable for most logics.

TODO:
  - stamps to identify funs / tacs
  - merge: fail if incompatible funs
  - improve merge
*)

infix 4 setloop addloop setsolver addsolver 
        setsubgoaler setmksimps
	addsimps addeqcongs delsimps 
	settermless addsimprocs delsimprocs;


signature SIMPLIFIER =
sig
  type simproc
  val mk_simproc: string -> cterm list -> (Sign.sg -> term -> thm option) -> simproc
  val name_of_simproc: simproc -> string
  val conv_prover: (term * term -> term) -> thm -> (thm -> thm)
    -> tactic -> (int -> tactic) -> Sign.sg -> term -> term -> thm	(* FIXME move?, rename? *)
  type simpset
  val empty_ss: simpset
  val rep_ss: simpset -> {simps: thm list, procs: string list, congs: thm list}
  val prems_of_ss: simpset -> thm list
  val setloop: simpset * (int -> tactic) -> simpset
  val addloop: simpset * (int -> tactic) -> simpset
  val setsolver: simpset * (thm list -> int -> tactic) -> simpset
  val addsolver: simpset * (thm list -> int -> tactic) -> simpset
  val setsubgoaler: simpset * (simpset -> int -> tactic) -> simpset
  val setmksimps: simpset * (thm -> thm list) -> simpset
  val settermless: simpset * (term * term -> bool) -> simpset
  val addsimps: simpset * thm list -> simpset
  val delsimps: simpset * thm list -> simpset
  val addsimprocs: simpset * simproc list -> simpset
  val delsimprocs: simpset * simproc list -> simpset
  val addeqcongs: simpset * thm list -> simpset
  val merge_ss: simpset * simpset -> simpset
  val simpset: simpset ref
  val Addsimps: thm list -> unit
  val Delsimps: thm list -> unit
  val Addsimprocs: simproc list -> unit
  val Delsimprocs: simproc list -> unit
  val          simp_tac: simpset -> int -> tactic
  val      asm_simp_tac: simpset -> int -> tactic
  val     full_simp_tac: simpset -> int -> tactic
  val asm_full_simp_tac: simpset -> int -> tactic
  val          Simp_tac: int -> tactic
  val      Asm_simp_tac: int -> tactic
  val     Full_simp_tac: int -> tactic
  val Asm_full_simp_tac: int -> tactic
end;


structure Simplifier: SIMPLIFIER =
struct


(** simplification procedures **)

(* datatype simproc *)

datatype simproc =
  Simproc of {
    name: string,
    procs: (Sign.sg * term * (Sign.sg -> term -> thm option) * stamp) list}

(* FIXME stamps!? *)
fun eq_simproc (Simproc {name = name1, ...}, Simproc {name = name2, ...}) =
  (name1 = name2);

fun mk_simproc name lhss proc =
  let
    fun mk_proc lhs =
      (#sign (Thm.rep_cterm lhs), Logic.varify (term_of lhs), proc, stamp ());
  in
    Simproc {name = name, procs = map mk_proc lhss}
  end;

fun name_of_simproc (Simproc {name, ...}) = name;


(* generic conversion prover *)		(* FIXME move?, rename? *)

fun conv_prover mk_eqv eqv_refl mk_meta_eq expand_tac norm_tac sg t u =
  let
    val X = Free (gensym "X.", fastype_of t);
    val goal = Logic.mk_implies (mk_eqv (X, t), mk_eqv (X, u));
    val pre_result =
      prove_goalw_cterm [] (cterm_of sg goal)   (*goal: X=t ==> X=u*)
        (fn prems => [
          expand_tac,				(*expand u*)
          ALLGOALS (cut_facts_tac prems),
          ALLGOALS norm_tac]);			(*normalize both t and u*)
  in
    mk_meta_eq (eqv_refl RS pre_result)         (*final result: t==u*)
  end
  handle ERROR => error ("The error(s) above occurred while trying to prove " ^
    (string_of_cterm (cterm_of sg (mk_eqv (t, u)))));



(** simplification sets **)

(* type simpset *)

datatype simpset =
  Simpset of {
    mss: meta_simpset,
    simps: thm list,
    procs: simproc list,
    congs: thm list,
    subgoal_tac: simpset -> int -> tactic,
    finish_tac: thm list -> int -> tactic,
    loop_tac: int -> tactic};

fun make_ss (mss, simps, procs, congs, subgoal_tac, finish_tac, loop_tac) =
  Simpset {mss = mss, simps = simps, procs = procs, congs = congs,
    subgoal_tac = subgoal_tac, finish_tac = finish_tac,
    loop_tac = loop_tac};

val empty_ss =
  make_ss (Thm.empty_mss, [], [], [], K (K no_tac), K (K no_tac), K no_tac);

fun rep_ss (Simpset {simps, procs, congs, ...}) =
  {simps = simps, procs = map name_of_simproc procs, congs = congs};

fun prems_of_ss (Simpset {mss, ...}) = Thm.prems_of_mss mss;


(* extend simpsets *)

fun (Simpset {mss, simps, procs, congs, subgoal_tac, finish_tac, loop_tac = _})
    setloop loop_tac =
  make_ss (mss, simps, procs, congs, subgoal_tac, finish_tac, DETERM o loop_tac);

fun (Simpset {mss, simps, procs, congs, subgoal_tac, finish_tac, loop_tac})
    addloop tac =
  make_ss (mss, simps, procs, congs, subgoal_tac, finish_tac, 
    loop_tac ORELSE' (DETERM o tac));

fun (Simpset {mss, simps, procs, congs, subgoal_tac, finish_tac = _, loop_tac})
    setsolver finish_tac =
  make_ss (mss, simps, procs, congs, subgoal_tac, finish_tac, loop_tac);

fun (Simpset {mss, simps, procs, congs, subgoal_tac, finish_tac, loop_tac})
    addsolver tac =
  make_ss (mss, simps, procs, congs, subgoal_tac,
    fn hyps => finish_tac hyps ORELSE' tac hyps, loop_tac);

fun (Simpset {mss, simps, procs, congs, subgoal_tac = _, finish_tac, loop_tac})
    setsubgoaler subgoal_tac =
  make_ss (mss, simps, procs, congs, subgoal_tac, finish_tac, loop_tac);

fun (Simpset {mss, simps, procs, congs, subgoal_tac, finish_tac, loop_tac})
    setmksimps mk_simps =
  make_ss (Thm.set_mk_rews (mss, mk_simps), simps, procs, congs,
    subgoal_tac, finish_tac, loop_tac);

fun (Simpset {mss, simps, procs, congs, subgoal_tac, finish_tac, loop_tac})
    settermless termless =
  make_ss (Thm.set_termless (mss, termless), simps, procs, congs,
    subgoal_tac, finish_tac, loop_tac);

fun (Simpset {mss, simps, procs, congs, subgoal_tac, finish_tac, loop_tac})
    addsimps rews =
  let val rews' = flat (map (Thm.mk_rews_of_mss mss) rews) in
    make_ss (Thm.add_simps (mss, rews'), gen_union eq_thm (rews', simps),
      procs, congs, subgoal_tac, finish_tac, loop_tac)
  end;

fun (Simpset {mss, simps, procs, congs, subgoal_tac, finish_tac, loop_tac})
    delsimps rews =
  let val rews' = flat (map (Thm.mk_rews_of_mss mss) rews) in
    make_ss (Thm.del_simps (mss, rews'),
      foldl (gen_rem eq_thm) (simps, rews'),
      procs, congs, subgoal_tac, finish_tac, loop_tac)
  end;

fun (Simpset {mss, simps, procs, congs, subgoal_tac, finish_tac, loop_tac})
    addeqcongs newcongs =
  make_ss (Thm.add_congs (mss, newcongs),
    simps, procs, gen_union eq_thm (newcongs, congs),
    subgoal_tac, finish_tac, loop_tac);

fun addsimproc ((Simpset {mss, simps, procs, congs, subgoal_tac, finish_tac, loop_tac}),
      simproc as Simproc {name = _, procs = procs'}) =
  make_ss (Thm.add_simprocs (mss, procs'),
    simps, gen_ins eq_simproc (simproc, procs),
    congs, subgoal_tac, finish_tac, loop_tac);

val op addsimprocs = foldl addsimproc;

fun delsimproc ((Simpset {mss, simps, procs, congs, subgoal_tac, finish_tac, loop_tac}),
      simproc as Simproc {name = _, procs = procs'}) =
  make_ss (Thm.del_simprocs (mss, procs'),
    simps, gen_rem eq_simproc (procs, simproc),
    congs, subgoal_tac, finish_tac, loop_tac);

val op delsimprocs = foldl delsimproc;


(* merge simpsets *)

(*prefers first simpset (FIXME improve?)*)
fun merge_ss (Simpset {mss, simps, procs, congs, subgoal_tac, finish_tac, loop_tac},
    Simpset {simps = simps2, procs = procs2, congs = congs2, ...}) =
  let
    val simps' = gen_union eq_thm (simps, simps2);
    val procs' = gen_union eq_simproc (procs, procs2);
    val congs' = gen_union eq_thm (congs, congs2);
    val mss' = Thm.set_mk_rews (empty_mss, Thm.mk_rews_of_mss mss);
    val mss' = Thm.add_simps (mss', simps');
    val mss' = Thm.add_congs (mss', congs');
  in
    make_ss (mss', simps', procs', congs', subgoal_tac, finish_tac, loop_tac)
  end;


(* the current simpset *)

val simpset = ref empty_ss;

fun Addsimps rews = (simpset := ! simpset addsimps rews);
fun Delsimps rews = (simpset := ! simpset delsimps rews);

fun Addsimprocs procs = (simpset := ! simpset addsimprocs procs);
fun Delsimprocs procs = (simpset := ! simpset delsimprocs procs);



(** simplification tactics **)

fun NEWSUBGOALS tac tacf =
  STATE (fn state0 =>
    tac THEN STATE (fn state1 => tacf (nprems_of state1 - nprems_of state0)));

fun gen_simp_tac mode =
  fn (Simpset {mss, simps, procs, congs, subgoal_tac, finish_tac, loop_tac}) =>
  let fun solve_all_tac mss =
        let val ss =
              make_ss (mss, simps, procs, congs, subgoal_tac, finish_tac, loop_tac);
            val solve1_tac =
              NEWSUBGOALS (subgoal_tac ss 1)
                          (fn n => if n<0 then all_tac else no_tac)
        in DEPTH_SOLVE(solve1_tac) end

      fun simp_loop_tac i thm =
          (asm_rewrite_goal_tac mode solve_all_tac mss i THEN
           (finish_tac (prems_of_mss mss) i  ORELSE  looper i))  thm
      and allsimp i n = EVERY(map (fn j => simp_loop_tac (i+j)) (n downto 0))
      and looper i = TRY(NEWSUBGOALS (loop_tac i) (allsimp i))
  in simp_loop_tac end;

val          simp_tac = gen_simp_tac (false, false);
val      asm_simp_tac = gen_simp_tac (false, true);
val     full_simp_tac = gen_simp_tac (true,  false);
val asm_full_simp_tac = gen_simp_tac (true,  true);

fun          Simp_tac i =          simp_tac (! simpset) i;
fun      Asm_simp_tac i =      asm_simp_tac (! simpset) i;
fun     Full_simp_tac i =     full_simp_tac (! simpset) i;
fun Asm_full_simp_tac i = asm_full_simp_tac (! simpset) i;

end;

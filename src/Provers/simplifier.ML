(*  Title:      Provers/simplifier.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Generic simplifier, suitable for most logics.  See also Pure/thm.ML
for the actual meta level rewriting engine.
*)

infix 4
  setsubgoaler setloop addloop setSSolver addSSolver setSolver
  addSolver setmksimps addsimps delsimps addeqcongs deleqcongs
  settermless addsimprocs delsimprocs;


signature SIMPLIFIER =
sig
  type simproc
  val mk_simproc: string -> cterm list
    -> (Sign.sg -> thm list -> term -> thm option) -> simproc
  val conv_prover: (term * term -> term) -> thm -> (thm -> thm)
    -> tactic -> (int -> tactic) -> Sign.sg -> term -> term -> thm
  type simpset
  val empty_ss: simpset
  val rep_ss: simpset ->
   {mss: meta_simpset,
    subgoal_tac:        simpset -> int -> tactic,
    loop_tac:                      int -> tactic,
           finish_tac: thm list -> int -> tactic,
    unsafe_finish_tac: thm list -> int -> tactic};
  val print_ss: simpset -> unit
  val setsubgoaler: simpset *  (simpset -> int -> tactic) -> simpset
  val setloop:      simpset *             (int -> tactic) -> simpset
  val addloop:      simpset *             (int -> tactic) -> simpset
  val setSSolver:   simpset * (thm list -> int -> tactic) -> simpset
  val addSSolver:   simpset * (thm list -> int -> tactic) -> simpset
  val setSolver:    simpset * (thm list -> int -> tactic) -> simpset
  val addSolver:    simpset * (thm list -> int -> tactic) -> simpset
  val setmksimps:   simpset * (thm -> thm list) -> simpset
  val settermless:  simpset * (term * term -> bool) -> simpset
  val addsimps:     simpset * thm list -> simpset
  val delsimps:     simpset * thm list -> simpset
  val addeqcongs:   simpset * thm list -> simpset
  val deleqcongs:   simpset * thm list -> simpset
  val addsimprocs:  simpset * simproc list -> simpset
  val delsimprocs:  simpset * simproc list -> simpset
  val merge_ss:     simpset * simpset -> simpset
  val prems_of_ss:  simpset -> thm list

  val simpset_thy_data: string * (object * (object -> object) *
    (object * object -> object) * (Sign.sg -> object -> unit))
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

  val               simp_tac: simpset -> int -> tactic
  val           asm_simp_tac: simpset -> int -> tactic
  val          full_simp_tac: simpset -> int -> tactic
  val      asm_full_simp_tac: simpset -> int -> tactic
  val safe_asm_full_simp_tac: simpset -> int -> tactic
  val               Simp_tac:            int -> tactic
  val           Asm_simp_tac:            int -> tactic
  val          Full_simp_tac:            int -> tactic
  val      Asm_full_simp_tac:            int -> tactic
  val          simplify: simpset -> thm -> thm
  val      asm_simplify: simpset -> thm -> thm
  val     full_simplify: simpset -> thm -> thm
  val asm_full_simplify: simpset -> thm -> thm
end;


structure Simplifier: SIMPLIFIER =
struct


(** simplification procedures **)

(* datatype simproc *)

datatype simproc =
  Simproc of string * cterm list * (Sign.sg -> thm list -> term -> thm option) * stamp;

fun mk_simproc name lhss proc =
  Simproc (name, map (Thm.cterm_fun Logic.varify) lhss, proc, stamp ());

fun rep_simproc (Simproc args) = args;


(* generic conversion prover *)

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
    subgoal_tac:        simpset -> int -> tactic,
    loop_tac:                      int -> tactic,
           finish_tac: thm list -> int -> tactic,
    unsafe_finish_tac: thm list -> int -> tactic};

fun make_ss (mss, subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac) =
  Simpset {mss = mss, subgoal_tac = subgoal_tac, loop_tac = loop_tac,
    finish_tac = finish_tac, unsafe_finish_tac = unsafe_finish_tac};

val empty_ss =
  make_ss (Thm.empty_mss, K (K no_tac), K no_tac, K (K no_tac), K (K no_tac));

fun rep_ss (Simpset args) = args;
fun prems_of_ss (Simpset {mss, ...}) = Thm.prems_of_mss mss;


(* print simpsets *)

fun print_ss ss =
  let
    val Simpset {mss, ...} = ss;
    val {simps, procs, congs} = Thm.dest_mss mss;

    val pretty_thms = map Display.pretty_thm;
    fun pretty_proc (name, lhss) =
      Pretty.big_list (name ^ ":") (map Display.pretty_cterm lhss);
  in
    Pretty.writeln (Pretty.big_list "simplification rules:" (pretty_thms simps));
    Pretty.writeln (Pretty.big_list "simplification procedures:" (map pretty_proc procs));
    Pretty.writeln (Pretty.big_list "congruences:" (pretty_thms congs))
  end;


(* extend simpsets *)

fun (Simpset {mss, subgoal_tac = _, loop_tac, finish_tac, unsafe_finish_tac})
    setsubgoaler subgoal_tac =
  make_ss (mss, subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tac = _, finish_tac, unsafe_finish_tac})
    setloop loop_tac =
  make_ss (mss, subgoal_tac, DETERM o loop_tac, finish_tac, unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac})
    addloop tac =
  make_ss (mss, subgoal_tac, loop_tac ORELSE' (DETERM o tac), finish_tac, unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tac, finish_tac = _, unsafe_finish_tac})
    setSSolver finish_tac =
  make_ss (mss, subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac})
    addSSolver tac =
  make_ss (mss, subgoal_tac, loop_tac, fn hyps => finish_tac hyps ORELSE' tac hyps,
    unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac = _})
    setSolver unsafe_finish_tac =
  make_ss (mss, subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac})
    addSolver tac =
  make_ss (mss, subgoal_tac, loop_tac, finish_tac,
    fn hyps => unsafe_finish_tac hyps ORELSE' tac hyps);

fun (Simpset {mss, subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac})
    setmksimps mk_simps =
  make_ss (Thm.set_mk_rews (mss, map (Thm.strip_shyps o Drule.zero_var_indexes) o mk_simps),
    subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tac,  finish_tac, unsafe_finish_tac})
    settermless termless =
  make_ss (Thm.set_termless (mss, termless), subgoal_tac, loop_tac,
    finish_tac, unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac})
    addsimps rews =
  let val rews' = flat (map (Thm.mk_rews_of_mss mss) rews) in
    make_ss (Thm.add_simps (mss, rews'), subgoal_tac, loop_tac,
      finish_tac, unsafe_finish_tac)
  end;

fun (Simpset {mss, subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac})
    delsimps rews =
  let val rews' = flat (map (Thm.mk_rews_of_mss mss) rews) in
    make_ss (Thm.del_simps (mss, rews'), subgoal_tac, loop_tac,
      finish_tac, unsafe_finish_tac)
  end;

fun (Simpset {mss, subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac})
    addeqcongs newcongs =
  make_ss (Thm.add_congs (mss, newcongs), subgoal_tac, loop_tac,
    finish_tac, unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac})
    deleqcongs oldcongs =
  make_ss (Thm.del_congs (mss, oldcongs), subgoal_tac, loop_tac,
    finish_tac, unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac})
    addsimprocs simprocs =
  make_ss
    (Thm.add_simprocs (mss, map rep_simproc simprocs),
      subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac})
    delsimprocs simprocs =
  make_ss
    (Thm.del_simprocs (mss, map rep_simproc simprocs),
      subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac);


(* merge simpsets *)	(*NOTE: ignores tactics of 2nd simpset*)

fun merge_ss
   (Simpset {mss = mss1, subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac},
    Simpset {mss = mss2, ...}) =
  make_ss (Thm.merge_mss (mss1, mss2),
    subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac);



(** simpset theory data **)

(* data kind simpset *)

val simpsetK = "simpset";
exception SimpsetData of simpset ref;

local
  val empty = SimpsetData (ref empty_ss);

  (*create new reference*)
  fun prep_ext (SimpsetData (ref ss)) = SimpsetData (ref ss);

  fun merge (SimpsetData (ref ss1), SimpsetData (ref ss2)) =
    SimpsetData (ref (merge_ss (ss1, ss2)));

  fun print (_: Sign.sg) (SimpsetData (ref ss)) = print_ss ss;
in
  val simpset_thy_data = (simpsetK, (empty, prep_ext, merge, print));
end;


(* access simpset *)

fun simpset_ref_of_sg sg =
  (case Sign.get_data sg simpsetK of
    SimpsetData r => r
  | _ => sys_error "simpset_ref_of_sg")

val simpset_ref_of = simpset_ref_of_sg o sign_of;
val simpset_of_sg = ! o simpset_ref_of_sg;
val simpset_of = simpset_of_sg o sign_of;

fun SIMPSET tacf state = tacf (simpset_of_sg (sign_of_thm state)) state;
fun SIMPSET' tacf i state = tacf (simpset_of_sg (sign_of_thm state)) i state;

val simpset = simpset_of o Context.get_context;
val simpset_ref = simpset_ref_of_sg o sign_of o Context.get_context;


(* change simpset *)

fun change_simpset f x = simpset_ref () := (f (simpset (), x));

val Addsimps = change_simpset (op addsimps);
val Delsimps = change_simpset (op delsimps);
val Addsimprocs = change_simpset (op addsimprocs);
val Delsimprocs = change_simpset (op delsimprocs);



(** simplification tactics **)

fun NEWSUBGOALS tac tacf st0 =
  st0 |> (tac THEN (fn st1 => tacf (nprems_of st1 - nprems_of st0) st1));

fun solve_all_tac (subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac) mss =
  let
    val ss =
      make_ss (mss, subgoal_tac, loop_tac, unsafe_finish_tac, unsafe_finish_tac);
    val solve1_tac =
      NEWSUBGOALS (subgoal_tac ss 1) (fn n => if n < 0 then all_tac else no_tac);
  in DEPTH_SOLVE solve1_tac end;


(*not totally safe: may instantiate unknowns that appear also in other subgoals*)
fun basic_gen_simp_tac mode =
  fn (Simpset {mss, subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac}) =>
    let
      fun simp_loop_tac i thm =
        (asm_rewrite_goal_tac mode
          (solve_all_tac (subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac)) mss i
        THEN (finish_tac (prems_of_mss mss) i ORELSE looper i)) thm
      and allsimp i n = EVERY (map (fn j => simp_loop_tac (i + j)) (n downto 0))
      and looper i = TRY (NEWSUBGOALS (loop_tac i) (allsimp i));
  in simp_loop_tac end;

fun gen_simp_tac mode (ss as Simpset {unsafe_finish_tac, ...}) =
  basic_gen_simp_tac mode (ss setSSolver unsafe_finish_tac);


val          simp_tac = gen_simp_tac (false, false);
val      asm_simp_tac = gen_simp_tac (false, true);
val     full_simp_tac = gen_simp_tac (true,  false);
val asm_full_simp_tac = gen_simp_tac (true,  true);

(*not totally safe: may instantiate unknowns that appear also in other subgoals*)
val safe_asm_full_simp_tac = basic_gen_simp_tac (true, true);

(** The abstraction over the proof state delays the dereferencing **)

fun          Simp_tac i st =          simp_tac (simpset ()) i st;
fun      Asm_simp_tac i st =      asm_simp_tac (simpset ()) i st;
fun     Full_simp_tac i st =     full_simp_tac (simpset ()) i st;
fun Asm_full_simp_tac i st = asm_full_simp_tac (simpset ()) i st;



(** simplification meta rules **)

fun simp mode (Simpset {mss, subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac}) thm =
  let
    val tacf = solve_all_tac (subgoal_tac, loop_tac, finish_tac, unsafe_finish_tac);
    fun prover m th = apsome fst (Sequence.pull (tacf m th));
  in
    Drule.rewrite_thm mode prover mss thm
  end;

val          simplify = simp (false, false);
val      asm_simplify = simp (false, true);
val     full_simplify = simp (true, false);
val asm_full_simplify = simp (true, true);


end;

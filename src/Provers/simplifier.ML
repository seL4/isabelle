(*  Title:      Provers/simplifier.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Generic simplifier, suitable for most logics.  See also Pure/thm.ML
for the actual meta level rewriting engine.
*)

infix 4
  setsubgoaler setloop addloop delloop setSSolver addSSolver setSolver
  addSolver addsimps delsimps addeqcongs deleqcongs
  setmksimps setmkeqTrue setmksym settermless addsimprocs delsimprocs;


signature SIMPLIFIER =
sig
  type simproc
  val mk_simproc: string -> cterm list
    -> (Sign.sg -> thm list -> term -> thm option) -> simproc
  type simpset
  val empty_ss: simpset
  val rep_ss: simpset ->
   {mss: meta_simpset,
    subgoal_tac:        simpset -> int -> tactic,
    loop_tacs:          (string * (int -> tactic))list,
           finish_tac: thm list -> int -> tactic,
    unsafe_finish_tac: thm list -> int -> tactic};
  val print_ss: simpset -> unit
  val print_simpset: theory -> unit
  val setsubgoaler: simpset *  (simpset -> int -> tactic) -> simpset
  val setloop:      simpset *             (int -> tactic) -> simpset
  val addloop:      simpset *  (string * (int -> tactic)) -> simpset
  val delloop:      simpset *   string                    -> simpset
  val setSSolver:   simpset * (thm list -> int -> tactic) -> simpset
  val addSSolver:   simpset * (thm list -> int -> tactic) -> simpset
  val setSolver:    simpset * (thm list -> int -> tactic) -> simpset
  val addSolver:    simpset * (thm list -> int -> tactic) -> simpset
  val setmksimps:   simpset * (thm -> thm list) -> simpset
  val setmkeqTrue:  simpset * (thm -> thm option) -> simpset
  val setmksym:     simpset * (thm -> thm option) -> simpset
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
  val        asm_lr_simp_tac: simpset -> int -> tactic
  val      asm_full_simp_tac: simpset -> int -> tactic
  val safe_asm_full_simp_tac: simpset -> int -> tactic
  val               Simp_tac:            int -> tactic
  val           Asm_simp_tac:            int -> tactic
  val          Full_simp_tac:            int -> tactic
  val        Asm_lr_simp_tac:            int -> tactic
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



(** simplification sets **)

(* type simpset *)

datatype simpset =
  Simpset of {
    mss: meta_simpset,
    subgoal_tac:        simpset -> int -> tactic,
    loop_tacs:          (string * (int -> tactic))list,
           finish_tac: thm list -> int -> tactic,
    unsafe_finish_tac: thm list -> int -> tactic};

fun make_ss (mss, subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac) =
  Simpset {mss = mss, subgoal_tac = subgoal_tac, loop_tacs = loop_tacs,
    finish_tac = finish_tac, unsafe_finish_tac = unsafe_finish_tac};

val empty_ss =
  let val mss = Thm.set_mk_sym(Thm.empty_mss, Some o symmetric_fun)
  in make_ss (mss, K (K no_tac), [], K (K no_tac), K (K no_tac)) end;

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

fun (Simpset {mss, subgoal_tac = _, loop_tacs, finish_tac, unsafe_finish_tac})
    setsubgoaler subgoal_tac =
  make_ss (mss, subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tacs = _, finish_tac, unsafe_finish_tac})
    setloop tac =
  make_ss (mss, subgoal_tac, [("",tac)], finish_tac, unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac})
    addloop tac = make_ss (mss, subgoal_tac, 
	(case assoc_string (loop_tacs,(fst tac)) of None => () | Some x => 
	 warning ("overwriting looper "^fst tac); overwrite(loop_tacs,tac)),
           finish_tac, unsafe_finish_tac);

fun (ss as Simpset {mss,subgoal_tac,loop_tacs,finish_tac,unsafe_finish_tac})
    delloop name =
  let val (del,rest) = partition (fn (n,_) => n=name) loop_tacs
  in if null del then (warning ("No such looper in simpset: " ^ name); ss)
     else make_ss (mss, subgoal_tac, rest, finish_tac, unsafe_finish_tac)
  end;

fun (Simpset {mss, subgoal_tac, loop_tacs, finish_tac = _, unsafe_finish_tac})
    setSSolver finish_tac =
  make_ss (mss, subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac})
    addSSolver tac =
  make_ss (mss, subgoal_tac, loop_tacs, fn hyps => finish_tac hyps ORELSE' tac hyps,
    unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac = _})
    setSolver unsafe_finish_tac =
  make_ss (mss, subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac})
    addSolver tac =
  make_ss (mss, subgoal_tac, loop_tacs, finish_tac,
    fn hyps => unsafe_finish_tac hyps ORELSE' tac hyps);

fun (Simpset {mss, subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac})
    setmksimps mk_simps =
  make_ss (Thm.set_mk_rews (mss, map (Thm.strip_shyps o Drule.zero_var_indexes) o mk_simps),
    subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac})
    setmkeqTrue mk_eq_True =
  make_ss (Thm.set_mk_eq_True (mss, mk_eq_True),
    subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac})
    setmksym mksym =
  make_ss (Thm.set_mk_sym (mss, mksym),
    subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tacs,  finish_tac, unsafe_finish_tac})
    settermless termless =
  make_ss (Thm.set_termless (mss, termless), subgoal_tac, loop_tacs,
    finish_tac, unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac})
    addsimps rews =
  make_ss (Thm.add_simps (mss, rews), subgoal_tac, loop_tacs,
           finish_tac, unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac})
    delsimps rews =
  make_ss (Thm.del_simps (mss, rews), subgoal_tac, loop_tacs,
           finish_tac, unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac})
    addeqcongs newcongs =
  make_ss (Thm.add_congs (mss, newcongs), subgoal_tac, loop_tacs,
    finish_tac, unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac})
    deleqcongs oldcongs =
  make_ss (Thm.del_congs (mss, oldcongs), subgoal_tac, loop_tacs,
    finish_tac, unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac})
    addsimprocs simprocs =
  make_ss
    (Thm.add_simprocs (mss, map rep_simproc simprocs),
      subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac);

fun (Simpset {mss, subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac})
    delsimprocs simprocs =
  make_ss
    (Thm.del_simprocs (mss, map rep_simproc simprocs),
      subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac);


(* merge simpsets *)	(*NOTE: ignores tactics of 2nd simpset*)

fun merge_ss
   (Simpset {mss = mss1, loop_tacs = loop_tacs1,
             subgoal_tac, finish_tac, unsafe_finish_tac},
    Simpset {mss = mss2, loop_tacs = loop_tacs2, ...}) =
  make_ss (Thm.merge_mss (mss1, mss2), subgoal_tac,
           merge_alists loop_tacs1 loop_tacs2,
           finish_tac, unsafe_finish_tac);



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

fun print_simpset thy = Display.print_data thy simpsetK;

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

fun solve_all_tac (subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac) mss =
  let
    val ss =
      make_ss (mss, subgoal_tac, loop_tacs, unsafe_finish_tac, unsafe_finish_tac);
    val solve1_tac = (subgoal_tac ss THEN_ALL_NEW (K no_tac)) 1
  in DEPTH_SOLVE solve1_tac end;

fun loop_tac loop_tacs = FIRST'(map snd loop_tacs);

(*not totally safe: may instantiate unknowns that appear also in other subgoals*)
fun basic_gen_simp_tac mode =
  fn (Simpset {mss, subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac}) =>
    let
      fun simp_loop_tac i =
        asm_rewrite_goal_tac mode
          (solve_all_tac (subgoal_tac,loop_tacs,finish_tac,unsafe_finish_tac))
          mss i
        THEN (finish_tac (prems_of_mss mss) i ORELSE
              TRY ((loop_tac loop_tacs THEN_ALL_NEW simp_loop_tac) i))
    in simp_loop_tac end;

fun gen_simp_tac mode (ss as Simpset {unsafe_finish_tac, ...}) =
  basic_gen_simp_tac mode (ss setSSolver unsafe_finish_tac);


val          simp_tac = gen_simp_tac (false, false, false);
val      asm_simp_tac = gen_simp_tac (false, true, false);
val     full_simp_tac = gen_simp_tac (true,  false, false);
val   asm_lr_simp_tac = gen_simp_tac (true,  true, false);
val asm_full_simp_tac = gen_simp_tac (true,  true, true);

(*not totally safe: may instantiate unknowns that appear also in other subgoals*)
val safe_asm_full_simp_tac = basic_gen_simp_tac (true, true, false);

(** The abstraction over the proof state delays the dereferencing **)

fun          Simp_tac i st =          simp_tac (simpset ()) i st;
fun      Asm_simp_tac i st =      asm_simp_tac (simpset ()) i st;
fun     Full_simp_tac i st =     full_simp_tac (simpset ()) i st;
fun   Asm_lr_simp_tac i st =   asm_lr_simp_tac (simpset ()) i st;
fun Asm_full_simp_tac i st = asm_full_simp_tac (simpset ()) i st;


(** simplification meta rules **)

fun simp mode (Simpset {mss, subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac}) thm =
  let
    val tacf = solve_all_tac (subgoal_tac, loop_tacs, finish_tac, unsafe_finish_tac);
    fun prover m th = apsome fst (Seq.pull (tacf m th));
  in
    Drule.rewrite_thm mode prover mss thm
  end;

val          simplify = simp (false, false, false);
val      asm_simplify = simp (false, true, false);
val     full_simplify = simp (true, false, false);
val asm_full_simplify = simp (true, true, false);


end;

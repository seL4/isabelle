(*  Title:      Sequents/prover.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Simple classical reasoner for the sequent calculus, based on "theorem packs".
*)

signature CLA =
sig
  type pack
  val empty_pack: pack
  val get_pack: Proof.context -> pack
  val put_pack: pack -> Proof.context -> Proof.context
  val pretty_pack: Proof.context -> Pretty.T
  val add_safe: thm -> Proof.context -> Proof.context
  val add_unsafe: thm -> Proof.context -> Proof.context
  val safe_add: attribute
  val unsafe_add: attribute
  val method: (Proof.context -> int -> tactic) -> (Proof.context -> Proof.method) context_parser
  val trace: bool Config.T
  val forms_of_seq: term -> term list
  val safe_tac: Proof.context -> int -> tactic
  val step_tac: Proof.context -> int -> tactic
  val pc_tac: Proof.context -> int -> tactic
  val fast_tac: Proof.context -> int -> tactic
  val best_tac: Proof.context -> int -> tactic
end;

structure Cla: CLA =
struct

(** rule declarations **)

(*A theorem pack has the form  (safe rules, unsafe rules)
  An unsafe rule is incomplete or introduces variables in subgoals,
  and is tried only when the safe rules are not applicable.  *)

fun less (rl1, rl2) = Thm.nprems_of rl1 < Thm.nprems_of rl2;
val sort_rules = sort (make_ord less);

datatype pack = Pack of thm list * thm list;

val empty_pack = Pack ([], []);

structure Pack = Generic_Data
(
  type T = pack;
  val empty = empty_pack;
  val extend = I;
  fun merge (Pack (safes, unsafes), Pack (safes', unsafes')) =
    Pack
     (sort_rules (Thm.merge_thms (safes, safes')),
      sort_rules (Thm.merge_thms (unsafes, unsafes')));
);

val put_pack = Context.proof_map o Pack.put;
val get_pack = Pack.get o Context.Proof;
fun get_rules ctxt = let val Pack rules = get_pack ctxt in rules end;


(* print pack *)

fun pretty_pack ctxt =
  let val (safes, unsafes) = get_rules ctxt in
    Pretty.chunks
     [Pretty.big_list "safe rules:" (map (Thm.pretty_thm ctxt) safes),
      Pretty.big_list "unsafe rules:" (map (Thm.pretty_thm ctxt) unsafes)]
  end;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_pack\<close> "print pack of classical rules"
    (Scan.succeed (Toplevel.keep (Pretty.writeln o pretty_pack o Toplevel.context_of)));


(* declare rules *)

fun add_rule which th context = context |> Pack.map (fn Pack rules =>
  Pack (rules |> which (fn ths =>
    if member Thm.eq_thm_prop ths th then
      let
        val _ =
          (case context of
            Context.Proof ctxt =>
              if Context_Position.is_really_visible ctxt then
                warning ("Ignoring duplicate theorems:\n" ^ Thm.string_of_thm ctxt th)
              else ()
          | _ => ());
      in ths end
    else sort_rules (th :: ths))));

val add_safe = Context.proof_map o add_rule apfst;
val add_unsafe = Context.proof_map o add_rule apsnd;


(* attributes *)

val safe_add = Thm.declaration_attribute (add_rule apfst);
val unsafe_add = Thm.declaration_attribute (add_rule apsnd);

val _ = Theory.setup
  (Attrib.setup \<^binding>\<open>safe\<close> (Scan.succeed safe_add) "" #>
   Attrib.setup \<^binding>\<open>unsafe\<close> (Scan.succeed unsafe_add) "");


(* proof method syntax *)

fun method tac =
  Method.sections
   [Args.$$$ "add" -- Args.bang_colon >> K (Method.modifier safe_add \<^here>),
    Args.$$$ "add" -- Args.colon >> K (Method.modifier unsafe_add \<^here>)]
  >> K (SIMPLE_METHOD' o tac);


(** tactics **)

val trace = Attrib.setup_config_bool \<^binding>\<open>cla_trace\<close> (K false);


(*Returns the list of all formulas in the sequent*)
fun forms_of_seq \<^Const_>\<open>SeqO' for P u\<close> = P :: forms_of_seq u
  | forms_of_seq (H $ u) = forms_of_seq u
  | forms_of_seq _ = [];

(*Tests whether two sequences (left or right sides) could be resolved.
  seqp is a premise (subgoal), seqc is a conclusion of an object-rule.
  Assumes each formula in seqc is surrounded by sequence variables
  -- checks that each concl formula looks like some subgoal formula.
  It SHOULD check order as well, using recursion rather than forall/exists*)
fun could_res (seqp,seqc) =
      forall (fn Qc => exists (fn Qp => Term.could_unify (Qp,Qc))
                              (forms_of_seq seqp))
             (forms_of_seq seqc);

(*Tests whether two sequents or pairs of sequents could be resolved*)
fun could_resolve_seq (prem,conc) =
  case (prem,conc) of
      (_ $ Abs(_,_,leftp) $ Abs(_,_,rightp),
       _ $ Abs(_,_,leftc) $ Abs(_,_,rightc)) =>
          could_res (leftp,leftc) andalso could_res (rightp,rightc)
    | (_ $ Abs(_,_,leftp) $ rightp,
       _ $ Abs(_,_,leftc) $ rightc) =>
          could_res (leftp,leftc)  andalso  Term.could_unify (rightp,rightc)
    | _ => false;


(*Like filt_resolve_tac, using could_resolve_seq
  Much faster than resolve_tac when there are many rules.
  Resolve subgoal i using the rules, unless more than maxr are compatible. *)
fun filseq_resolve_tac ctxt rules maxr = SUBGOAL(fn (prem,i) =>
  let val rls = filter_thms could_resolve_seq (maxr+1, prem, rules)
  in  if length rls > maxr  then  no_tac
          else (*((rtac derelict 1 THEN rtac impl 1
                 THEN (rtac identity 2 ORELSE rtac ll_mp 2)
                 THEN rtac context1 1)
                 ORELSE *) resolve_tac ctxt rls i
  end);


(*Predicate: does the rule have n premises? *)
fun has_prems n rule = (Thm.nprems_of rule = n);

(*Continuation-style tactical for resolution.
  The list of rules is partitioned into 0, 1, 2 premises.
  The resulting tactic, gtac, tries to resolve with rules.
  If successful, it recursively applies nextac to the new subgoals only.
  Else fails.  (Treatment of goals due to Ph. de Groote)
  Bind (RESOLVE_THEN rules) to a variable: it preprocesses the rules. *)

(*Takes rule lists separated in to 0, 1, 2, >2 premises.
  The abstraction over state prevents needless divergence in recursion.
  The 9999 should be a parameter, to delay treatment of flexible goals. *)

fun RESOLVE_THEN ctxt rules =
  let val [rls0,rls1,rls2] = partition_list has_prems 0 2 rules;
      fun tac nextac i state = state |>
             (filseq_resolve_tac ctxt rls0 9999 i
              ORELSE
              (DETERM(filseq_resolve_tac ctxt rls1 9999 i) THEN  TRY(nextac i))
              ORELSE
              (DETERM(filseq_resolve_tac ctxt rls2 9999 i) THEN  TRY(nextac(i+1))
                                            THEN  TRY(nextac i)))
  in  tac  end;



(*repeated resolution applied to the designated goal*)
fun reresolve_tac ctxt rules =
  let
    val restac = RESOLVE_THEN ctxt rules;  (*preprocessing done now*)
    fun gtac i = restac gtac i;
  in gtac end;

(*tries the safe rules repeatedly before the unsafe rules. *)
fun repeat_goal_tac ctxt =
  let
    val (safes, unsafes) = get_rules ctxt;
    val restac = RESOLVE_THEN ctxt safes;
    val lastrestac = RESOLVE_THEN ctxt unsafes;
    fun gtac i =
      restac gtac i ORELSE
       (if Config.get ctxt trace then print_tac ctxt "" THEN lastrestac gtac i
        else lastrestac gtac i)
  in gtac end;


(*Tries safe rules only*)
fun safe_tac ctxt = reresolve_tac ctxt (#1 (get_rules ctxt));

(*Tries a safe rule or else a unsafe rule.  Single-step for tracing. *)
fun step_tac ctxt =
  safe_tac ctxt ORELSE' filseq_resolve_tac ctxt (#2 (get_rules ctxt)) 9999;


(* Tactic for reducing a goal, using Predicate Calculus rules.
   A decision procedure for Propositional Calculus, it is incomplete
   for Predicate-Calculus because of allL_thin and exR_thin.
   Fails if it can do nothing.      *)
fun pc_tac ctxt = SELECT_GOAL (DEPTH_SOLVE (repeat_goal_tac ctxt 1));


(*The following two tactics are analogous to those provided by
  Provers/classical.  In fact, pc_tac is usually FASTER than fast_tac!*)
fun fast_tac ctxt =
  SELECT_GOAL (DEPTH_SOLVE (step_tac ctxt 1));

fun best_tac ctxt  =
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, size_of_thm) (step_tac ctxt 1));

val _ = Theory.setup
  (Method.setup \<^binding>\<open>safe\<close> (method safe_tac) "" #>
   Method.setup \<^binding>\<open>step\<close> (method step_tac) "" #>
   Method.setup \<^binding>\<open>pc\<close> (method pc_tac) "" #>
   Method.setup \<^binding>\<open>fast\<close> (method fast_tac) "" #>
   Method.setup \<^binding>\<open>best\<close> (method best_tac) "");

end;


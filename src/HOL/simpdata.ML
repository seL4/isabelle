(*  Title:      HOL/simpdata.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1991  University of Cambridge

Instantiation of the generic simplifier for HOL.
*)

section "Simplifier";

(*** Addition of rules to simpsets and clasets simultaneously ***)	(* FIXME move to Provers/clasimp.ML? *)

infix 4 addIffs delIffs;

(*Takes UNCONDITIONAL theorems of the form A<->B to 
        the Safe Intr     rule B==>A and 
        the Safe Destruct rule A==>B.
  Also ~A goes to the Safe Elim rule A ==> ?R
  Failing other cases, A is added as a Safe Intr rule*)
local
  val iff_const = HOLogic.eq_const HOLogic.boolT;

  fun addIff ((cla, simp), th) = 
      (case HOLogic.dest_Trueprop (#prop (rep_thm th)) of
                (Const("Not", _) $ A) =>
                    cla addSEs [zero_var_indexes (th RS notE)]
              | (con $ _ $ _) =>
                    if con = iff_const
                    then cla addSIs [zero_var_indexes (th RS iffD2)]  
                              addSDs [zero_var_indexes (th RS iffD1)]
                    else  cla addSIs [th]
              | _ => cla addSIs [th],
       simp addsimps [th])
      handle TERM _ => error ("AddIffs: theorem must be unconditional\n" ^ 
                         string_of_thm th);

  fun delIff ((cla, simp), th) = 
      (case HOLogic.dest_Trueprop (#prop (rep_thm th)) of
	   (Const ("Not", _) $ A) =>
	       cla delrules [zero_var_indexes (th RS notE)]
	 | (con $ _ $ _) =>
	       if con = iff_const
	       then cla delrules 
		        [zero_var_indexes (th RS iffD2),
			 cla_make_elim (zero_var_indexes (th RS iffD1))]
	       else cla delrules [th]
	 | _ => cla delrules [th],
       simp delsimps [th])
      handle TERM _ => (warning("DelIffs: ignoring conditional theorem\n" ^ 
				string_of_thm th); (cla, simp));

  fun store_clasimp (cla, simp) = (claset_ref () := cla; simpset_ref () := simp)
in
val op addIffs = foldl addIff;
val op delIffs = foldl delIff;
fun AddIffs thms = store_clasimp ((claset (), simpset ()) addIffs thms);
fun DelIffs thms = store_clasimp ((claset (), simpset ()) delIffs thms);
end;


val [prem] = goal (the_context ()) "x==y ==> x=y";
by (rewtac prem);
by (rtac refl 1);
qed "meta_eq_to_obj_eq";

Goal "(%s. f s) = f";
br refl 1;
qed "eta_contract_eq";

local

  fun prover s = prove_goal (the_context ()) s (fn _ => [(Blast_tac 1)]);

in

(*Make meta-equalities.  The operator below is Trueprop*)

fun mk_meta_eq r = r RS eq_reflection;

val Eq_TrueI  = mk_meta_eq(prover  "P --> (P = True)"  RS mp);
val Eq_FalseI = mk_meta_eq(prover "~P --> (P = False)" RS mp);

fun mk_eq th = case concl_of th of
        Const("==",_)$_$_       => th
    |   _$(Const("op =",_)$_$_) => mk_meta_eq th
    |   _$(Const("Not",_)$_)    => th RS Eq_FalseI
    |   _                       => th RS Eq_TrueI;
(* last 2 lines requires all formulae to be of the from Trueprop(.) *)

fun mk_eq_True r = Some(r RS meta_eq_to_obj_eq RS Eq_TrueI);

fun mk_meta_cong rl =
  standard(mk_meta_eq(replicate (nprems_of rl) meta_eq_to_obj_eq MRS rl))
  handle THM _ =>
  error("Premises and conclusion of congruence rules must be =-equalities");

val not_not = prover "(~ ~ P) = P";

val simp_thms = [not_not] @ map prover
 [ "(x=x) = True",
   "(~True) = False", "(~False) = True",
   "(~P) ~= P", "P ~= (~P)", "(P ~= Q) = (P = (~Q))",
   "(True=P) = P", "(P=True) = P", "(False=P) = (~P)", "(P=False) = (~P)",
   "(True --> P) = P", "(False --> P) = True", 
   "(P --> True) = True", "(P --> P) = True",
   "(P --> False) = (~P)", "(P --> ~P) = (~P)",
   "(P & True) = P", "(True & P) = P", 
   "(P & False) = False", "(False & P) = False",
   "(P & P) = P", "(P & (P & Q)) = (P & Q)",
   "(P & ~P) = False",    "(~P & P) = False",
   "(P | True) = True", "(True | P) = True", 
   "(P | False) = P", "(False | P) = P",
   "(P | P) = P", "(P | (P | Q)) = (P | Q)",
   "(P | ~P) = True",    "(~P | P) = True",
   "((~P) = (~Q)) = (P=Q)",
   "(!x. P) = P", "(? x. P) = P", "? x. x=t", "? x. t=x", 
(*two needed for the one-point-rule quantifier simplification procs*)
   "(? x. x=t & P(x)) = P(t)",		(*essential for termination!!*)
   "(! x. t=x --> P(x)) = P(t)" ];      (*covers a stray case*)

(* Add congruence rules for = (instead of ==) *)

(* ###FIXME: Move to simplifier, 
   taking mk_meta_cong as input, eliminating addeqcongs and deleqcongs *)
infix 4 addcongs delcongs;
fun ss addcongs congs = ss addeqcongs (map mk_meta_cong congs);
fun ss delcongs congs = ss deleqcongs (map mk_meta_cong congs);
fun Addcongs congs = (simpset_ref() := simpset() addcongs congs);
fun Delcongs congs = (simpset_ref() := simpset() delcongs congs);

val cong_add_global = Simplifier.change_global_ss (op addcongs);
val cong_del_global = Simplifier.change_global_ss (op delcongs);
val cong_add_local = Simplifier.change_local_ss (op addcongs);
val cong_del_local = Simplifier.change_local_ss (op delcongs);

val cong_attrib_setup =
 [Attrib.add_attributes [("cong",
   (Attrib.add_del_args cong_add_global cong_del_global,
    Attrib.add_del_args cong_add_local cong_del_local),
    "declare Simplifier congruence rules")]];


val imp_cong = impI RSN
    (2, prove_goal (the_context ()) "(P=P')--> (P'--> (Q=Q'))--> ((P-->Q) = (P'-->Q'))"
        (fn _=> [(Blast_tac 1)]) RS mp RS mp);

(*Miniscoping: pushing in existential quantifiers*)
val ex_simps = map prover
                ["(EX x. P x & Q)   = ((EX x. P x) & Q)",
                 "(EX x. P & Q x)   = (P & (EX x. Q x))",
                 "(EX x. P x | Q)   = ((EX x. P x) | Q)",
                 "(EX x. P | Q x)   = (P | (EX x. Q x))",
                 "(EX x. P x --> Q) = ((ALL x. P x) --> Q)",
                 "(EX x. P --> Q x) = (P --> (EX x. Q x))"];

(*Miniscoping: pushing in universal quantifiers*)
val all_simps = map prover
                ["(ALL x. P x & Q)   = ((ALL x. P x) & Q)",
                 "(ALL x. P & Q x)   = (P & (ALL x. Q x))",
                 "(ALL x. P x | Q)   = ((ALL x. P x) | Q)",
                 "(ALL x. P | Q x)   = (P | (ALL x. Q x))",
                 "(ALL x. P x --> Q) = ((EX x. P x) --> Q)",
                 "(ALL x. P --> Q x) = (P --> (ALL x. Q x))"];


(* elimination of existential quantifiers in assumptions *)

val ex_all_equiv =
  let val lemma1 = prove_goal (the_context ())
        "(? x. P(x) ==> PROP Q) ==> (!!x. P(x) ==> PROP Q)"
        (fn prems => [resolve_tac prems 1, etac exI 1]);
      val lemma2 = prove_goalw (the_context ()) [Ex_def]
        "(!!x. P(x) ==> PROP Q) ==> (? x. P(x) ==> PROP Q)"
        (fn prems => [(REPEAT(resolve_tac prems 1))])
  in equal_intr lemma1 lemma2 end;

end;

bind_thms ("ex_simps", ex_simps);
bind_thms ("all_simps", all_simps);
bind_thm ("not_not", not_not);

(* Elimination of True from asumptions: *)

val True_implies_equals = prove_goal (the_context ())
 "(True ==> PROP P) == PROP P"
(fn _ => [rtac equal_intr_rule 1, atac 2,
          METAHYPS (fn prems => resolve_tac prems 1) 1,
          rtac TrueI 1]);

fun prove nm thm  = qed_goal nm (the_context ()) thm (fn _ => [(Blast_tac 1)]);

prove "eq_commute" "(a=b)=(b=a)";
prove "eq_left_commute" "(P=(Q=R)) = (Q=(P=R))";
prove "eq_assoc" "((P=Q)=R) = (P=(Q=R))";
val eq_ac = [eq_commute, eq_left_commute, eq_assoc];

prove "conj_commute" "(P&Q) = (Q&P)";
prove "conj_left_commute" "(P&(Q&R)) = (Q&(P&R))";
val conj_comms = [conj_commute, conj_left_commute];
prove "conj_assoc" "((P&Q)&R) = (P&(Q&R))";

prove "disj_commute" "(P|Q) = (Q|P)";
prove "disj_left_commute" "(P|(Q|R)) = (Q|(P|R))";
val disj_comms = [disj_commute, disj_left_commute];
prove "disj_assoc" "((P|Q)|R) = (P|(Q|R))";

prove "conj_disj_distribL" "(P&(Q|R)) = (P&Q | P&R)";
prove "conj_disj_distribR" "((P|Q)&R) = (P&R | Q&R)";

prove "disj_conj_distribL" "(P|(Q&R)) = ((P|Q) & (P|R))";
prove "disj_conj_distribR" "((P&Q)|R) = ((P|R) & (Q|R))";

prove "imp_conjR" "(P --> (Q&R)) = ((P-->Q) & (P-->R))";
prove "imp_conjL" "((P&Q) -->R)  = (P --> (Q --> R))";
prove "imp_disjL" "((P|Q) --> R) = ((P-->R)&(Q-->R))";

(*These two are specialized, but imp_disj_not1 is useful in Auth/Yahalom.ML*)
prove "imp_disj_not1" "(P --> Q | R) = (~Q --> P --> R)";
prove "imp_disj_not2" "(P --> Q | R) = (~R --> P --> Q)";

prove "imp_disj1" "((P-->Q)|R) = (P--> Q|R)";
prove "imp_disj2" "(Q|(P-->R)) = (P--> Q|R)";

prove "de_Morgan_disj" "(~(P | Q)) = (~P & ~Q)";
prove "de_Morgan_conj" "(~(P & Q)) = (~P | ~Q)";
prove "not_imp" "(~(P --> Q)) = (P & ~Q)";
prove "not_iff" "(P~=Q) = (P = (~Q))";
prove "disj_not1" "(~P | Q) = (P --> Q)";
prove "disj_not2" "(P | ~Q) = (Q --> P)"; (* changes orientation :-( *)
prove "imp_conv_disj" "(P --> Q) = ((~P) | Q)";

prove "iff_conv_conj_imp" "(P = Q) = ((P --> Q) & (Q --> P))";


(*Avoids duplication of subgoals after split_if, when the true and false 
  cases boil down to the same thing.*) 
prove "cases_simp" "((P --> Q) & (~P --> Q)) = Q";

prove "not_all" "(~ (! x. P(x))) = (? x.~P(x))";
prove "imp_all" "((! x. P x) --> Q) = (? x. P x --> Q)";
prove "not_ex"  "(~ (? x. P(x))) = (! x.~P(x))";
prove "imp_ex" "((? x. P x) --> Q) = (! x. P x --> Q)";

prove "ex_disj_distrib" "(? x. P(x) | Q(x)) = ((? x. P(x)) | (? x. Q(x)))";
prove "all_conj_distrib" "(!x. P(x) & Q(x)) = ((! x. P(x)) & (! x. Q(x)))";

(* '&' congruence rule: not included by default!
   May slow rewrite proofs down by as much as 50% *)

let val th = prove_goal (the_context ()) 
                "(P=P')--> (P'--> (Q=Q'))--> ((P&Q) = (P'&Q'))"
                (fn _=> [(Blast_tac 1)])
in  bind_thm("conj_cong",standard (impI RSN (2, th RS mp RS mp)))  end;

let val th = prove_goal (the_context ()) 
                "(Q=Q')--> (Q'--> (P=P'))--> ((P&Q) = (P'&Q'))"
                (fn _=> [(Blast_tac 1)])
in  bind_thm("rev_conj_cong",standard (impI RSN (2, th RS mp RS mp)))  end;

(* '|' congruence rule: not included by default! *)

let val th = prove_goal (the_context ()) 
                "(P=P')--> (~P'--> (Q=Q'))--> ((P|Q) = (P'|Q'))"
                (fn _=> [(Blast_tac 1)])
in  bind_thm("disj_cong",standard (impI RSN (2, th RS mp RS mp)))  end;

prove "eq_sym_conv" "(x=y) = (y=x)";


(** if-then-else rules **)

Goalw [if_def] "(if True then x else y) = x";
by (Blast_tac 1);
qed "if_True";

Goalw [if_def] "(if False then x else y) = y";
by (Blast_tac 1);
qed "if_False";

Goalw [if_def] "P ==> (if P then x else y) = x";
by (Blast_tac 1);
qed "if_P";

Goalw [if_def] "~P ==> (if P then x else y) = y";
by (Blast_tac 1);
qed "if_not_P";

Goal "P(if Q then x else y) = ((Q --> P(x)) & (~Q --> P(y)))";
by (res_inst_tac [("Q","Q")] (excluded_middle RS disjE) 1);
by (stac if_P 2);
by (stac if_not_P 1);
by (ALLGOALS (Blast_tac));
qed "split_if";

Goal "P(if Q then x else y) = (~((Q & ~P x) | (~Q & ~P y)))";
by (stac split_if 1);
by (Blast_tac 1);
qed "split_if_asm";

bind_thms ("if_splits", [split_if, split_if_asm]);

Goal "(if c then x else x) = x";
by (stac split_if 1);
by (Blast_tac 1);
qed "if_cancel";

Goal "(if x = y then y else x) = x";
by (stac split_if 1);
by (Blast_tac 1);
qed "if_eq_cancel";

(*This form is useful for expanding IFs on the RIGHT of the ==> symbol*)
Goal "(if P then Q else R) = ((P-->Q) & (~P-->R))";
by (rtac split_if 1);
qed "if_bool_eq_conj";

(*And this form is useful for expanding IFs on the LEFT*)
Goal "(if P then Q else R) = ((P&Q) | (~P&R))";
by (stac split_if 1);
by (Blast_tac 1);
qed "if_bool_eq_disj";


(*** make simplification procedures for quantifier elimination ***)

structure Quantifier1 = Quantifier1Fun(
struct
  (*abstract syntax*)
  fun dest_eq((c as Const("op =",_)) $ s $ t) = Some(c,s,t)
    | dest_eq _ = None;
  fun dest_conj((c as Const("op &",_)) $ s $ t) = Some(c,s,t)
    | dest_conj _ = None;
  val conj = HOLogic.conj
  val imp  = HOLogic.imp
  (*rules*)
  val iff_reflection = eq_reflection
  val iffI = iffI
  val sym  = sym
  val conjI= conjI
  val conjE= conjE
  val impI = impI
  val impE = impE
  val mp   = mp
  val exI  = exI
  val exE  = exE
  val allI = allI
  val allE = allE
end);

local
val ex_pattern =
  Thm.read_cterm (Theory.sign_of (the_context ())) ("EX x. P(x) & Q(x)",HOLogic.boolT)

val all_pattern =
  Thm.read_cterm (Theory.sign_of (the_context ())) ("ALL x. P(x) & P'(x) --> Q(x)",HOLogic.boolT)

in
val defEX_regroup =
  mk_simproc "defined EX" [ex_pattern] Quantifier1.rearrange_ex;
val defALL_regroup =
  mk_simproc "defined ALL" [all_pattern] Quantifier1.rearrange_all;
end;


(*** Case splitting ***)

structure SplitterData =
  struct
  structure Simplifier = Simplifier
  val mk_eq          = mk_eq
  val meta_eq_to_iff = meta_eq_to_obj_eq
  val iffD           = iffD2
  val disjE          = disjE
  val conjE          = conjE
  val exE            = exE
  val contrapos      = contrapos
  val contrapos2     = contrapos2
  val notnotD        = notnotD
  end;

structure Splitter = SplitterFun(SplitterData);

val split_tac        = Splitter.split_tac;
val split_inside_tac = Splitter.split_inside_tac;
val split_asm_tac    = Splitter.split_asm_tac;
val op addsplits     = Splitter.addsplits;
val op delsplits     = Splitter.delsplits;
val Addsplits        = Splitter.Addsplits;
val Delsplits        = Splitter.Delsplits;

(*In general it seems wrong to add distributive laws by default: they
  might cause exponential blow-up.  But imp_disjL has been in for a while
  and cannot be removed without affecting existing proofs.  Moreover, 
  rewriting by "(P|Q --> R) = ((P-->R)&(Q-->R))" might be justified on the
  grounds that it allows simplification of R in the two cases.*)

fun gen_all th = forall_elim_vars (#maxidx(rep_thm th)+1) th;

val mksimps_pairs =
  [("op -->", [mp]), ("op &", [conjunct1,conjunct2]),
   ("All", [spec]), ("True", []), ("False", []),
   ("If", [if_bool_eq_conj RS iffD1])];

(* ###FIXME: move to Provers/simplifier.ML
val mk_atomize:      (string * thm list) list -> thm -> thm list
*)
(* ###FIXME: move to Provers/simplifier.ML *)
fun mk_atomize pairs =
  let fun atoms th =
        (case concl_of th of
           Const("Trueprop",_) $ p =>
             (case head_of p of
                Const(a,_) =>
                  (case assoc(pairs,a) of
                     Some(rls) => flat (map atoms ([th] RL rls))
                   | None => [th])
              | _ => [th])
         | _ => [th])
  in atoms end;

fun mksimps pairs = (map mk_eq o mk_atomize pairs o gen_all);

fun unsafe_solver_tac prems =
  FIRST'[resolve_tac(reflexive_thm::TrueI::refl::prems), atac, etac FalseE];
val unsafe_solver = mk_solver "HOL unsafe" unsafe_solver_tac;

(*No premature instantiation of variables during simplification*)
fun safe_solver_tac prems =
  FIRST'[match_tac(reflexive_thm::TrueI::refl::prems),
         eq_assume_tac, ematch_tac [FalseE]];
val safe_solver = mk_solver "HOL safe" safe_solver_tac;

val HOL_basic_ss = empty_ss setsubgoaler asm_simp_tac
			    setSSolver safe_solver
			    setSolver  unsafe_solver
			    setmksimps (mksimps mksimps_pairs)
			    setmkeqTrue mk_eq_True;

val HOL_ss = 
    HOL_basic_ss addsimps 
     ([triv_forall_equality, (* prunes params *)
       True_implies_equals, (* prune asms `True' *)
       eta_contract_eq, (* prunes eta-expansions *)
       if_True, if_False, if_cancel, if_eq_cancel,
       imp_disjL, conj_assoc, disj_assoc,
       de_Morgan_conj, de_Morgan_disj, imp_disj1, imp_disj2, not_imp,
       disj_not1, not_all, not_ex, cases_simp, Eps_eq, Eps_sym_eq,
       thm"plus_ac0.zero", thm"plus_ac0_zero_right"]
     @ ex_simps @ all_simps @ simp_thms)
     addsimprocs [defALL_regroup,defEX_regroup]
     addcongs [imp_cong]
     addsplits [split_if];

(*Simplifies x assuming c and y assuming ~c*)
val prems = Goalw [if_def]
  "[| b=c; c ==> x=u; ~c ==> y=v |] ==> \
\  (if b then x else y) = (if c then u else v)";
by (asm_simp_tac (HOL_ss addsimps prems) 1);
qed "if_cong";

(*Prevents simplification of x and y: faster and allows the execution
  of functional programs. NOW THE DEFAULT.*)
Goal "b=c ==> (if b then x else y) = (if c then x else y)";
by (etac arg_cong 1);
qed "if_weak_cong";

(*Prevents simplification of t: much faster*)
Goal "a = b ==> (let x=a in t(x)) = (let x=b in t(x))";
by (etac arg_cong 1);
qed "let_weak_cong";

Goal "f(if c then x else y) = (if c then f x else f y)";
by (simp_tac (HOL_ss setloop (split_tac [split_if])) 1);
qed "if_distrib";

(*For expand_case_tac*)
val prems = Goal "[| P ==> Q(True); ~P ==> Q(False) |] ==> Q(P)";
by (case_tac "P" 1);
by (ALLGOALS (asm_simp_tac (HOL_ss addsimps prems)));
qed "expand_case";

(*Used in Auth proofs.  Typically P contains Vars that become instantiated
  during unification.*)
fun expand_case_tac P i =
    res_inst_tac [("P",P)] expand_case i THEN
    Simp_tac (i+1) THEN 
    Simp_tac i;

(*This lemma restricts the effect of the rewrite rule u=v to the left-hand
  side of an equality.  Used in {Integ,Real}/simproc.ML*)
Goal "x=y ==> (x=z) = (y=z)";
by (asm_simp_tac HOL_ss 1);
qed "restrict_to_left";

(* default simpset *)
val simpsetup = 
    [fn thy => (simpset_ref_of thy := HOL_ss addcongs [if_weak_cong]; 
		thy)];


(*** integration of simplifier with classical reasoner ***)

structure Clasimp = ClasimpFun
 (structure Simplifier = Simplifier and Splitter = Splitter
   and Classical  = Classical and Blast = Blast);
open Clasimp;

val HOL_css = (HOL_cs, HOL_ss);


(* "iff" attribute *)

val iff_add_global = Clasimp.change_global_css (op addIffs);
val iff_add_local = Clasimp.change_local_css (op addIffs);

val iff_attrib_setup =
  [Attrib.add_attributes [("iff", (Attrib.no_args iff_add_global, Attrib.no_args iff_add_local),
    "add rules to simpset and claset simultaneously")]];



(*** A general refutation procedure ***)
 
(* Parameters:

   test: term -> bool
   tests if a term is at all relevant to the refutation proof;
   if not, then it can be discarded. Can improve performance,
   esp. if disjunctions can be discarded (no case distinction needed!).

   prep_tac: int -> tactic
   A preparation tactic to be applied to the goal once all relevant premises
   have been moved to the conclusion.

   ref_tac: int -> tactic
   the actual refutation tactic. Should be able to deal with goals
   [| A1; ...; An |] ==> False
   where the Ai are atomic, i.e. no top-level &, | or ?
*)

fun refute_tac test prep_tac ref_tac =
  let val nnf_simps =
        [imp_conv_disj,iff_conv_conj_imp,de_Morgan_disj,de_Morgan_conj,
         not_all,not_ex,not_not];
      val nnf_simpset =
        empty_ss setmkeqTrue mk_eq_True
                 setmksimps (mksimps mksimps_pairs)
                 addsimps nnf_simps;
      val prem_nnf_tac = full_simp_tac nnf_simpset;

      val refute_prems_tac =
        REPEAT(eresolve_tac [conjE, exE] 1 ORELSE
               filter_prems_tac test 1 ORELSE
               etac disjE 1) THEN
        ref_tac 1;
  in EVERY'[TRY o filter_prems_tac test,
            DETERM o REPEAT o etac rev_mp, prep_tac, rtac ccontr, prem_nnf_tac,
            SELECT_GOAL (DEPTH_SOLVE refute_prems_tac)]
  end;

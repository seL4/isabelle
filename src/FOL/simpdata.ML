(*  Title:      FOL/simpdata
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Simplification data for FOL
*)

(*** Rewrite rules ***)

fun int_prove_fun s = 
 (writeln s;  
  prove_goal IFOL.thy s
   (fn prems => [ (cut_facts_tac prems 1), 
                  (IntPr.fast_tac 1) ]));

val conj_simps = map int_prove_fun
 ["P & True <-> P",      "True & P <-> P",
  "P & False <-> False", "False & P <-> False",
  "P & P <-> P", "P & P & Q <-> P & Q",
  "P & ~P <-> False",    "~P & P <-> False",
  "(P & Q) & R <-> P & (Q & R)"];

val disj_simps = map int_prove_fun
 ["P | True <-> True",  "True | P <-> True",
  "P | False <-> P",    "False | P <-> P",
  "P | P <-> P", "P | P | Q <-> P | Q",
  "(P | Q) | R <-> P | (Q | R)"];

val not_simps = map int_prove_fun
 ["~(P|Q)  <-> ~P & ~Q",
  "~ False <-> True",   "~ True <-> False"];

val imp_simps = map int_prove_fun
 ["(P --> False) <-> ~P",       "(P --> True) <-> True",
  "(False --> P) <-> True",     "(True --> P) <-> P", 
  "(P --> P) <-> True",         "(P --> ~P) <-> ~P"];

val iff_simps = map int_prove_fun
 ["(True <-> P) <-> P",         "(P <-> True) <-> P",
  "(P <-> P) <-> True",
  "(False <-> P) <-> ~P",       "(P <-> False) <-> ~P"];

(*The x=t versions are needed for the simplification procedures*)
val quant_simps = map int_prove_fun
 ["(ALL x. P) <-> P",   
  "(ALL x. x=t --> P(x)) <-> P(t)",
  "(ALL x. t=x --> P(x)) <-> P(t)",
  "(EX x. P) <-> P",
  "(EX x. x=t & P(x)) <-> P(t)", 
  "(EX x. t=x & P(x)) <-> P(t)"];

(*These are NOT supplied by default!*)
val distrib_simps  = map int_prove_fun
 ["P & (Q | R) <-> P&Q | P&R", 
  "(Q | R) & P <-> Q&P | R&P",
  "(P | Q --> R) <-> (P --> R) & (Q --> R)"];

(** Conversion into rewrite rules **)

fun gen_all th = forall_elim_vars (#maxidx(rep_thm th)+1) th;

(*Make atomic rewrite rules*)
fun atomize r =
  case concl_of r of
    Const("Trueprop",_) $ p =>
      (case p of
         Const("op -->",_)$_$_ => atomize(r RS mp)
       | Const("op &",_)$_$_   => atomize(r RS conjunct1) @
                                  atomize(r RS conjunct2)
       | Const("All",_)$_      => atomize(r RS spec)
       | Const("True",_)       => []    (*True is DELETED*)
       | Const("False",_)      => []    (*should False do something?*)
       | _                     => [r])
  | _ => [r];


val P_iff_F = int_prove_fun "~P ==> (P <-> False)";
val iff_reflection_F = P_iff_F RS iff_reflection;

val P_iff_T = int_prove_fun "P ==> (P <-> True)";
val iff_reflection_T = P_iff_T RS iff_reflection;

(*Make meta-equalities.  The operator below is Trueprop*)
fun mk_meta_eq th = case concl_of th of
    Const("==",_)$_$_           => th
  | _ $ (Const("op =",_)$_$_)   => th RS eq_reflection
  | _ $ (Const("op <->",_)$_$_) => th RS iff_reflection
  | _ $ (Const("Not",_)$_)      => th RS iff_reflection_F
  | _                           => th RS iff_reflection_T;


(*** Classical laws ***)

fun prove_fun s = 
 (writeln s;  
  prove_goal FOL.thy s
   (fn prems => [ (cut_facts_tac prems 1), 
                  (Cla.fast_tac FOL_cs 1) ]));

(*Avoids duplication of subgoals after expand_if, when the true and false 
  cases boil down to the same thing.*) 
val cases_simp = prove_fun "(P --> Q) & (~P --> Q) <-> Q";


(*** Miniscoping: pushing quantifiers in
     We do NOT distribute of ALL over &, or dually that of EX over |
     Baaz and Leitsch, On Skolemization and Proof Complexity (1994) 
     show that this step can increase proof length!
***)

(*existential miniscoping*)
val int_ex_simps = map int_prove_fun 
		     ["(EX x. P(x) & Q) <-> (EX x. P(x)) & Q",
		      "(EX x. P & Q(x)) <-> P & (EX x. Q(x))",
		      "(EX x. P(x) | Q) <-> (EX x. P(x)) | Q",
		      "(EX x. P | Q(x)) <-> P | (EX x. Q(x))"];

(*classical rules*)
val cla_ex_simps = map prove_fun 
                     ["(EX x. P(x) --> Q) <-> (ALL x. P(x)) --> Q",
		      "(EX x. P --> Q(x)) <-> P --> (EX x. Q(x))"];

val ex_simps = int_ex_simps @ cla_ex_simps;

(*universal miniscoping*)
val int_all_simps = map int_prove_fun
		      ["(ALL x. P(x) & Q) <-> (ALL x. P(x)) & Q",
		       "(ALL x. P & Q(x)) <-> P & (ALL x. Q(x))",
		       "(ALL x. P(x) --> Q) <-> (EX x. P(x)) --> Q",
		       "(ALL x. P --> Q(x)) <-> P --> (ALL x. Q(x))"];

(*classical rules*)
val cla_all_simps = map prove_fun
                      ["(ALL x. P(x) | Q) <-> (ALL x. P(x)) | Q",
		       "(ALL x. P | Q(x)) <-> P | (ALL x. Q(x))"];

val all_simps = int_all_simps @ cla_all_simps;


(*** Named rewrite rules proved for IFOL ***)

fun int_prove nm thm  = qed_goal nm IFOL.thy thm
    (fn prems => [ (cut_facts_tac prems 1), 
                   (IntPr.fast_tac 1) ]);

fun prove nm thm  = qed_goal nm FOL.thy thm (fn _ => [Blast_tac 1]);

int_prove "conj_commute" "P&Q <-> Q&P";
int_prove "conj_left_commute" "P&(Q&R) <-> Q&(P&R)";
val conj_comms = [conj_commute, conj_left_commute];

int_prove "disj_commute" "P|Q <-> Q|P";
int_prove "disj_left_commute" "P|(Q|R) <-> Q|(P|R)";
val disj_comms = [disj_commute, disj_left_commute];

int_prove "conj_disj_distribL" "P&(Q|R) <-> (P&Q | P&R)";
int_prove "conj_disj_distribR" "(P|Q)&R <-> (P&R | Q&R)";

int_prove "disj_conj_distribL" "P|(Q&R) <-> (P|Q) & (P|R)";
int_prove "disj_conj_distribR" "(P&Q)|R <-> (P|R) & (Q|R)";

int_prove "imp_conj_distrib" "(P --> (Q&R)) <-> (P-->Q) & (P-->R)";
int_prove "imp_conj"         "((P&Q)-->R)   <-> (P --> (Q --> R))";
int_prove "imp_disj"         "(P|Q --> R)   <-> (P-->R) & (Q-->R)";

prove "imp_disj1" "(P-->Q) | R <-> (P-->Q | R)";
prove "imp_disj2" "Q | (P-->R) <-> (P-->Q | R)";

int_prove "de_Morgan_disj" "(~(P | Q)) <-> (~P & ~Q)";
prove     "de_Morgan_conj" "(~(P & Q)) <-> (~P | ~Q)";

prove     "not_iff" "~(P <-> Q) <-> (P <-> ~Q)";

prove     "not_all" "(~ (ALL x. P(x))) <-> (EX x.~P(x))";
prove     "imp_all" "((ALL x. P(x)) --> Q) <-> (EX x. P(x) --> Q)";
int_prove "not_ex"  "(~ (EX x. P(x))) <-> (ALL x.~P(x))";
int_prove "imp_ex" "((EX x. P(x)) --> Q) <-> (ALL x. P(x) --> Q)";

int_prove "ex_disj_distrib"
    "(EX x. P(x) | Q(x)) <-> ((EX x. P(x)) | (EX x. Q(x)))";
int_prove "all_conj_distrib"
    "(ALL x. P(x) & Q(x)) <-> ((ALL x. P(x)) & (ALL x. Q(x)))";


(*Used in ZF, perhaps elsewhere?*)
val meta_eq_to_obj_eq = prove_goal IFOL.thy "x==y ==> x=y"
  (fn [prem] => [rewtac prem, rtac refl 1]);


open Simplifier;

(** make simplification procedures for quantifier elimination **)
structure Quantifier1 = Quantifier1Fun(
struct
  (*abstract syntax*)
  fun dest_eq((c as Const("op =",_)) $ s $ t) = Some(c,s,t)
    | dest_eq _ = None;
  fun dest_conj((c as Const("op &",_)) $ s $ t) = Some(c,s,t)
    | dest_conj _ = None;
  val conj = FOLogic.conj
  val imp  = FOLogic.imp
  (*rules*)
  val iff_reflection = iff_reflection
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
  read_cterm (sign_of FOL.thy) ("EX x. P(x) & Q(x)", FOLogic.oT)

val all_pattern =
  read_cterm (sign_of FOL.thy) ("ALL x. P(x) & P'(x) --> Q(x)", FOLogic.oT)

in
val defEX_regroup =
  mk_simproc "defined EX" [ex_pattern] Quantifier1.rearrange_ex;
val defALL_regroup =
  mk_simproc "defined ALL" [all_pattern] Quantifier1.rearrange_all;
end;


(*** Case splitting ***)

qed_goal "meta_iffD" IFOL.thy "[| P==Q; Q |] ==> P"
        (fn [prem1,prem2] => [rewtac prem1, rtac prem2 1]);

local val mktac = mk_case_split_tac meta_iffD
in
fun split_tac splits = mktac (map mk_meta_eq splits)
end;

local val mktac = mk_case_split_inside_tac meta_iffD
in
fun split_inside_tac splits = mktac (map mk_meta_eq splits)
end;

val split_asm_tac = mk_case_split_asm_tac split_tac 
			(disjE,conjE,exE,contrapos,contrapos2,notnotD);



(*** Standard simpsets ***)

structure Induction = InductionFun(struct val spec=IFOL.spec end);

open Induction;

(*Add congruence rules for = or <-> (instead of ==) *)
infix 4 addcongs delcongs;
fun ss addcongs congs =
        ss addeqcongs (map standard (congs RL [eq_reflection,iff_reflection]));
fun ss delcongs congs =
        ss deleqcongs (map standard (congs RL [eq_reflection,iff_reflection]));

fun Addcongs congs = (simpset_ref() := simpset() addcongs congs);
fun Delcongs congs = (simpset_ref() := simpset() delcongs congs);

infix 4 addsplits;
fun ss addsplits splits = ss addloop (split_tac splits);

val IFOL_simps =
   [refl RS P_iff_T] @ conj_simps @ disj_simps @ not_simps @ 
    imp_simps @ iff_simps @ quant_simps;

val notFalseI = int_prove_fun "~False";
val triv_rls = [TrueI,refl,iff_refl,notFalseI];

fun unsafe_solver prems = FIRST'[resolve_tac (triv_rls@prems),
				 atac, etac FalseE];
(*No premature instantiation of variables during simplification*)
fun   safe_solver prems = FIRST'[match_tac (triv_rls@prems),
				 eq_assume_tac, ematch_tac [FalseE]];

(*No simprules, but basic infastructure for simplification*)
val FOL_basic_ss = empty_ss setsubgoaler asm_simp_tac
                            addsimprocs [defALL_regroup,defEX_regroup]
			    setSSolver   safe_solver
			    setSolver  unsafe_solver
			    setmksimps (map mk_meta_eq o atomize o gen_all);

(*intuitionistic simprules only*)
val IFOL_ss = FOL_basic_ss addsimps (IFOL_simps @ int_ex_simps @ int_all_simps)
			   addcongs [imp_cong];

val cla_simps = 
    [de_Morgan_conj, de_Morgan_disj, imp_disj1, imp_disj2,
     not_all, not_ex, cases_simp] @
    map prove_fun
     ["~(P&Q)  <-> ~P | ~Q",
      "P | ~P",             "~P | P",
      "~ ~ P <-> P",        "(~P --> P) <-> P",
      "(~P <-> ~Q) <-> (P<->Q)"];

(*classical simprules too*)
val FOL_ss = IFOL_ss addsimps (cla_simps @ cla_ex_simps @ cla_all_simps);

simpset_ref() := FOL_ss;



(*** Integration of simplifier with classical reasoner ***)

(* rot_eq_tac rotates the first equality premise of subgoal i to the front,
   fails if there is no equaliy or if an equality is already at the front *)
local
  fun is_eq (Const ("Trueprop", _) $ (Const("op ="  ,_) $ _ $ _)) = true
    | is_eq (Const ("Trueprop", _) $ (Const("op <->",_) $ _ $ _)) = true
    | is_eq _ = false;
  val find_eq = find_index is_eq;
in
val rot_eq_tac = 
     SUBGOAL (fn (Bi,i) => let val n = find_eq (Logic.strip_assums_hyp Bi) in
		if n>0 then rotate_tac n i else no_tac end)
end;


fun safe_asm_more_full_simp_tac ss = TRY o rot_eq_tac THEN' 
				     safe_asm_full_simp_tac ss;
(*an unsatisfactory fix for the incomplete asm_full_simp_tac!
  better: asm_really_full_simp_tac, a yet to be implemented version of
			asm_full_simp_tac that applies all equalities in the
			premises to all the premises *)

(*Add a simpset to a classical set!*)
infix 4 addSss addss;
fun cs addSss ss = cs addSaltern (CHANGED o (safe_asm_more_full_simp_tac ss));
fun cs addss  ss = cs addbefore                        asm_full_simp_tac ss;

fun Addss ss = (claset_ref() := claset() addss ss);

(*Designed to be idempotent, except if best_tac instantiates variables
  in some of the subgoals*)

type clasimpset = (claset * simpset);

val FOL_css = (FOL_cs, FOL_ss);

fun pair_upd1 f ((a,b),x) = (f(a,x), b);
fun pair_upd2 f ((a,b),x) = (a, f(b,x));

infix 4 addSIs2 addSEs2 addSDs2 addIs2 addEs2 addDs2
	addsimps2 delsimps2 addcongs2 delcongs2;
fun op addSIs2   arg = pair_upd1 (op addSIs) arg;
fun op addSEs2   arg = pair_upd1 (op addSEs) arg;
fun op addSDs2   arg = pair_upd1 (op addSDs) arg;
fun op addIs2    arg = pair_upd1 (op addIs ) arg;
fun op addEs2    arg = pair_upd1 (op addEs ) arg;
fun op addDs2    arg = pair_upd1 (op addDs ) arg;
fun op addsimps2 arg = pair_upd2 (op addsimps) arg;
fun op delsimps2 arg = pair_upd2 (op delsimps) arg;
fun op addcongs2 arg = pair_upd2 (op addcongs) arg;
fun op delcongs2 arg = pair_upd2 (op delcongs) arg;


fun mk_auto_tac (cs, ss) m n =
    let val cs' = cs addss ss 
	val bdt = Blast.depth_tac cs m;
	fun blast_depth_tac i thm = bdt i thm handle Blast.TRANS s => 
		(warning ("Blast_tac: " ^ s); Seq.empty);
        val maintac = 
          blast_depth_tac	   (*fast but can't use addss*)
          ORELSE'
          depth_tac cs' n;         (*slower but general*)
    in  EVERY [ALLGOALS (asm_full_simp_tac ss),
	       TRY (safe_tac cs'),
	       REPEAT (FIRSTGOAL maintac),
               TRY (safe_tac (cs addSss ss)),
	       prune_params_tac] 
    end;

fun auto_tac (cs,ss) = mk_auto_tac (cs,ss) 4 2;

fun Auto_tac st = auto_tac (claset(), simpset()) st;

fun auto () = by Auto_tac;

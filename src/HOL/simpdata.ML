(*  Title:      HOL/simpdata.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1991  University of Cambridge

Instantiation of the generic simplifier
*)

section "Simplifier";

open Simplifier;

(*** Addition of rules to simpsets and clasets simultaneously ***)

(*Takes UNCONDITIONAL theorems of the form A<->B to 
        the Safe Intr     rule B==>A and 
        the Safe Destruct rule A==>B.
  Also ~A goes to the Safe Elim rule A ==> ?R
  Failing other cases, A is added as a Safe Intr rule*)
local
  val iff_const = HOLogic.eq_const HOLogic.boolT;

  fun addIff th = 
      (case HOLogic.dest_Trueprop (#prop(rep_thm th)) of
                (Const("Not",_) $ A) =>
                    AddSEs [zero_var_indexes (th RS notE)]
              | (con $ _ $ _) =>
                    if con=iff_const
                    then (AddSIs [zero_var_indexes (th RS iffD2)];  
                          AddSDs [zero_var_indexes (th RS iffD1)])
                    else  AddSIs [th]
              | _ => AddSIs [th];
       Addsimps [th])
      handle _ => error ("AddIffs: theorem must be unconditional\n" ^ 
                         string_of_thm th)

  fun delIff th = 
      (case HOLogic.dest_Trueprop (#prop(rep_thm th)) of
                (Const("Not",_) $ A) =>
                    Delrules [zero_var_indexes (th RS notE)]
              | (con $ _ $ _) =>
                    if con=iff_const
                    then Delrules [zero_var_indexes (th RS iffD2),
                                   make_elim (zero_var_indexes (th RS iffD1))]
                    else Delrules [th]
              | _ => Delrules [th];
       Delsimps [th])
      handle _ => warning("DelIffs: ignoring conditional theorem\n" ^ 
                          string_of_thm th)
in
val AddIffs = seq addIff
val DelIffs = seq delIff
end;


local

  fun prover s = prove_goal HOL.thy s (fn _ => [blast_tac HOL_cs 1]);

  val P_imp_P_iff_True = prover "P --> (P = True)" RS mp;
  val P_imp_P_eq_True = P_imp_P_iff_True RS eq_reflection;

  val not_P_imp_P_iff_F = prover "~P --> (P = False)" RS mp;
  val not_P_imp_P_eq_False = not_P_imp_P_iff_F RS eq_reflection;

  fun atomize pairs =
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

  fun gen_all th = forall_elim_vars (#maxidx(rep_thm th)+1) th;

in

  fun mk_meta_eq r = case concl_of r of
          Const("==",_)$_$_ => r
      |   _$(Const("op =",_)$_$_) => r RS eq_reflection
      |   _$(Const("Not",_)$_) => r RS not_P_imp_P_eq_False
      |   _ => r RS P_imp_P_eq_True;
  (* last 2 lines requires all formulae to be of the from Trueprop(.) *)

val simp_thms = map prover
 [ "(x=x) = True",
   "(~True) = False", "(~False) = True", "(~ ~ P) = P",
   "(~P) ~= P", "P ~= (~P)", "(P ~= Q) = (P = (~Q))",
   "(True=P) = P", "(P=True) = P",
   "(True --> P) = P", "(False --> P) = True", 
   "(P --> True) = True", "(P --> P) = True",
   "(P --> False) = (~P)", "(P --> ~P) = (~P)",
   "(P & True) = P", "(True & P) = P", 
   "(P & False) = False", "(False & P) = False",
   "(P & P) = P", "(P & (P & Q)) = (P & Q)",
   "(P | True) = True", "(True | P) = True", 
   "(P | False) = P", "(False | P) = P",
   "(P | P) = P", "(P | (P | Q)) = (P | Q)",
   "((~P) = (~Q)) = (P=Q)",
   "(!x. P) = P", "(? x. P) = P", "? x. x=t", "? x. t=x", 
   "(? x. x=t & P(x)) = P(t)",
   "(! x. t=x --> P(x)) = P(t)" ];

(*Add congruence rules for = (instead of ==) *)
infix 4 addcongs delcongs;
fun ss addcongs congs = ss addeqcongs (map standard (congs RL [eq_reflection]));
fun ss delcongs congs = ss deleqcongs (map standard (congs RL [eq_reflection]));

fun Addcongs congs = (simpset := !simpset addcongs congs);
fun Delcongs congs = (simpset := !simpset delcongs congs);

fun mksimps pairs = map mk_meta_eq o atomize pairs o gen_all;

val imp_cong = impI RSN
    (2, prove_goal HOL.thy "(P=P')--> (P'--> (Q=Q'))--> ((P-->Q) = (P'-->Q'))"
        (fn _=> [blast_tac HOL_cs 1]) RS mp RS mp);

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

(*** Simplification procedure for turning  ? x. ... & x = t & ...
     into                                  ? x. x = t & ... & ...
     where the latter can be rewritten via (? x. x = t & P(x)) = P(t)
 ***)

local

fun def(eq as (c as Const("op =",_)) $ s $ t) =
      if s = Bound 0 andalso not(loose_bvar1(t,0)) then Some eq else
      if t = Bound 0 andalso not(loose_bvar1(s,0)) then Some(c$t$s)
      else None
  | def _ = None;

fun extract(Const("op &",_) $ P $ Q) =
      (case def P of
         Some eq => Some(eq,Q)
       | None => (case def Q of
                   Some eq => Some(eq,P)
                 | None =>
       (case extract P of
         Some(eq,P') => Some(eq, HOLogic.conj $ P' $ Q)
       | None => (case extract Q of
                   Some(eq,Q') => Some(eq,HOLogic.conj $ P $ Q')
                 | None => None))))
  | extract _ = None;

fun prove_eq(ceqt) =
  let val tac = rtac eq_reflection 1 THEN rtac iffI 1 THEN
                ALLGOALS(EVERY'[etac exE, REPEAT o (etac conjE),
                 rtac exI, REPEAT o (ares_tac [conjI] ORELSE' etac sym)])
  in rule_by_tactic tac (trivial ceqt) end;

fun rearrange sg _ (F as ex $ Abs(x,T,P)) =
     (case extract P of
        None => None
      | Some(eq,Q) =>
          let val ceqt = cterm_of sg
                       (Logic.mk_equals(F,ex $ Abs(x,T,HOLogic.conj$eq$Q)))
          in Some(prove_eq ceqt) end)
  | rearrange _ _ _ = None;

val pattern = read_cterm (sign_of HOL.thy) ("? x. P(x) & Q(x)",HOLogic.boolT)

in
val defEX_regroup = mk_simproc "defined EX" [pattern] rearrange;
end;


(* elimination of existential quantifiers in assumptions *)

val ex_all_equiv =
  let val lemma1 = prove_goal HOL.thy
        "(? x. P(x) ==> PROP Q) ==> (!!x. P(x) ==> PROP Q)"
        (fn prems => [resolve_tac prems 1, etac exI 1]);
      val lemma2 = prove_goalw HOL.thy [Ex_def]
        "(!!x. P(x) ==> PROP Q) ==> (? x. P(x) ==> PROP Q)"
        (fn prems => [REPEAT(resolve_tac prems 1)])
  in equal_intr lemma1 lemma2 end;

end;

(* Elimination of True from asumptions: *)

val True_implies_equals = prove_goal HOL.thy
 "(True ==> PROP P) == PROP P"
(fn _ => [rtac equal_intr_rule 1, atac 2,
          METAHYPS (fn prems => resolve_tac prems 1) 1,
          rtac TrueI 1]);

fun prove nm thm  = qed_goal nm HOL.thy thm (fn _ => [blast_tac HOL_cs 1]);

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
prove "imp_disj_not1" "((P --> Q | R)) = (~Q --> P --> R)";
prove "imp_disj_not2" "((P --> Q | R)) = (~R --> P --> Q)";

prove "de_Morgan_disj" "(~(P | Q)) = (~P & ~Q)";
prove "de_Morgan_conj" "(~(P & Q)) = (~P | ~Q)";
prove "not_imp" "(~(P --> Q)) = (P & ~Q)";
prove "not_iff" "(P~=Q) = (P = (~Q))";

(*Avoids duplication of subgoals after expand_if, when the true and false 
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

let val th = prove_goal HOL.thy 
                "(P=P')--> (P'--> (Q=Q'))--> ((P&Q) = (P'&Q'))"
                (fn _=> [blast_tac HOL_cs 1])
in  bind_thm("conj_cong",standard (impI RSN (2, th RS mp RS mp)))  end;

let val th = prove_goal HOL.thy 
                "(Q=Q')--> (Q'--> (P=P'))--> ((P&Q) = (P'&Q'))"
                (fn _=> [blast_tac HOL_cs 1])
in  bind_thm("rev_conj_cong",standard (impI RSN (2, th RS mp RS mp)))  end;

(* '|' congruence rule: not included by default! *)

let val th = prove_goal HOL.thy 
                "(P=P')--> (~P'--> (Q=Q'))--> ((P|Q) = (P'|Q'))"
                (fn _=> [blast_tac HOL_cs 1])
in  bind_thm("disj_cong",standard (impI RSN (2, th RS mp RS mp)))  end;

prove "eq_sym_conv" "(x=y) = (y=x)";

qed_goalw "o_apply" HOL.thy [o_def] "(f o g) x = f (g x)"
 (fn _ => [rtac refl 1]);

qed_goal "meta_eq_to_obj_eq" HOL.thy "x==y ==> x=y"
  (fn [prem] => [rewtac prem, rtac refl 1]);

qed_goalw "if_True" HOL.thy [if_def] "(if True then x else y) = x"
 (fn _=>[blast_tac (HOL_cs addIs [select_equality]) 1]);

qed_goalw "if_False" HOL.thy [if_def] "(if False then x else y) = y"
 (fn _=>[blast_tac (HOL_cs addIs [select_equality]) 1]);

qed_goal "if_P" HOL.thy "P ==> (if P then x else y) = x"
 (fn [prem] => [ stac (prem RS eqTrueI) 1, rtac if_True 1 ]);
(*
qed_goal "if_not_P" HOL.thy "~P ==> (if P then x else y) = y"
 (fn [prem] => [ stac (prem RS not_P_imp_P_iff_F) 1, rtac if_False 1 ]);
*)
qed_goalw "if_not_P" HOL.thy [if_def] "!!P. ~P ==> (if P then x else y) = y"
 (fn _ => [blast_tac (HOL_cs addIs [select_equality]) 1]);

qed_goal "expand_if" HOL.thy
    "P(if Q then x else y) = ((Q --> P(x)) & (~Q --> P(y)))"
 (fn _=> [ (res_inst_tac [("Q","Q")] (excluded_middle RS disjE) 1),
         stac if_P 2,
         stac if_not_P 1,
         REPEAT(blast_tac HOL_cs 1) ]);

qed_goal "if_bool_eq" HOL.thy
                   "(if P then Q else R) = ((P-->Q) & (~P-->R))"
                   (fn _ => [rtac expand_if 1]);

local val mktac = mk_case_split_tac (meta_eq_to_obj_eq RS iffD2)
in
fun split_tac splits = mktac (map mk_meta_eq splits)
end;

local val mktac = mk_case_split_inside_tac (meta_eq_to_obj_eq RS iffD2)
in
fun split_inside_tac splits = mktac (map mk_meta_eq splits)
end;


qed_goal "if_cancel" HOL.thy "(if c then x else x) = x"
  (fn _ => [split_tac [expand_if] 1, blast_tac HOL_cs 1]);

(** 'if' congruence rules: neither included by default! *)

(*Simplifies x assuming c and y assuming ~c*)
qed_goal "if_cong" HOL.thy
  "[| b=c; c ==> x=u; ~c ==> y=v |] ==>\
\  (if b then x else y) = (if c then u else v)"
  (fn rew::prems =>
   [stac rew 1, stac expand_if 1, stac expand_if 1,
    blast_tac (HOL_cs addDs prems) 1]);

(*Prevents simplification of x and y: much faster*)
qed_goal "if_weak_cong" HOL.thy
  "b=c ==> (if b then x else y) = (if c then x else y)"
  (fn [prem] => [rtac (prem RS arg_cong) 1]);

(*Prevents simplification of t: much faster*)
qed_goal "let_weak_cong" HOL.thy
  "a = b ==> (let x=a in t(x)) = (let x=b in t(x))"
  (fn [prem] => [rtac (prem RS arg_cong) 1]);

(*In general it seems wrong to add distributive laws by default: they
  might cause exponential blow-up.  But imp_disjL has been in for a while
  and cannot be removed without affecting existing proofs.  Moreover, 
  rewriting by "(P|Q --> R) = ((P-->R)&(Q-->R))" might be justified on the
  grounds that it allows simplification of R in the two cases.*)

val mksimps_pairs =
  [("op -->", [mp]), ("op &", [conjunct1,conjunct2]),
   ("All", [spec]), ("True", []), ("False", []),
   ("If", [if_bool_eq RS iffD1])];

fun unsafe_solver prems = FIRST'[resolve_tac (TrueI::refl::prems),
				 atac, etac FalseE];
(*No premature instantiation of variables during simplification*)
fun   safe_solver prems = FIRST'[match_tac (TrueI::refl::prems),
				 eq_assume_tac, ematch_tac [FalseE]];

val HOL_basic_ss = empty_ss setsubgoaler asm_simp_tac
			    setSSolver   safe_solver
			    setSolver  unsafe_solver
			    setmksimps (mksimps mksimps_pairs);

val HOL_ss = 
    HOL_basic_ss addsimps 
     ([triv_forall_equality, (* prunes params *)
       True_implies_equals, (* prune asms `True' *)
       if_True, if_False, if_cancel,
       o_apply, imp_disjL, conj_assoc, disj_assoc,
       de_Morgan_conj, de_Morgan_disj, not_imp,
       not_all, not_ex, cases_simp]
     @ ex_simps @ all_simps @ simp_thms)
     addsimprocs [defEX_regroup]
     addcongs [imp_cong];

qed_goal "if_distrib" HOL.thy
  "f(if c then x else y) = (if c then f x else f y)" 
  (fn _ => [simp_tac (HOL_ss setloop (split_tac [expand_if])) 1]);

qed_goalw "o_assoc" HOL.thy [o_def] "f o (g o h) = f o g o h"
  (fn _ => [rtac ext 1, rtac refl 1]);


val prems = goal HOL.thy "[| P ==> Q(True); ~P ==> Q(False) |] ==> Q(P)";
by (case_tac "P" 1);
by (ALLGOALS (asm_simp_tac (HOL_ss addsimps prems)));
val expand_case = result();

fun expand_case_tac P i =
    res_inst_tac [("P",P)] expand_case i THEN
    Simp_tac (i+1) THEN 
    Simp_tac i;




(*** Install simpsets and datatypes in theory structure ***)

simpset := HOL_ss;

exception SS_DATA of simpset;

let fun merge [] = SS_DATA empty_ss
      | merge ss = let val ss = map (fn SS_DATA x => x) ss;
                   in SS_DATA (foldl merge_ss (hd ss, tl ss)) end;

    fun put (SS_DATA ss) = simpset := ss;

    fun get () = SS_DATA (!simpset);
in add_thydata "HOL"
     ("simpset", ThyMethods {merge = merge, put = put, get = get})
end;

fun simpset_of tname =
  case get_thydata tname "simpset" of
      None => empty_ss
    | Some (SS_DATA ss) => ss;

type dtype_info = {case_const:term,
                   case_rewrites:thm list,
                   constructors:term list,
                   induct_tac: string -> int -> tactic,
                   nchotomy: thm,
                   exhaustion: thm,
                   exhaust_tac: string -> int -> tactic,
                   case_cong:thm};

exception DT_DATA of (string * dtype_info) list;
val datatypes = ref [] : (string * dtype_info) list ref;

let fun merge [] = DT_DATA []
      | merge ds =
          let val ds = map (fn DT_DATA x => x) ds;
          in DT_DATA (foldl (gen_union eq_fst) (hd ds, tl ds)) end;

    fun put (DT_DATA ds) = datatypes := ds;

    fun get () = DT_DATA (!datatypes);
in add_thydata "HOL"
     ("datatypes", ThyMethods {merge = merge, put = put, get = get})
end;



(*** Integration of simplifier with classical reasoner ***)

(* rot_eq_tac rotates the first equality premise of subgoal i to the front,
   fails if there is no equaliy or if an equality is already at the front *)
local
  fun is_eq (Const ("Trueprop", _) $ (Const("op ="  ,_) $ _ $ _)) = true
    | is_eq _ = false;
  fun find_eq n [] = None
    | find_eq n (t :: ts) = if (is_eq t) then Some n 
			    else find_eq (n + 1) ts;
in
val rot_eq_tac = 
     SUBGOAL (fn (Bi,i) => 
	      case find_eq 0 (Logic.strip_assums_hyp Bi) of
		  None   => no_tac
		| Some 0 => no_tac
		| Some n => rotate_tac n i)
end;

(*an unsatisfactory fix for the incomplete asm_full_simp_tac!
  better: asm_really_full_simp_tac, a yet to be implemented version of
			asm_full_simp_tac that applies all equalities in the
			premises to all the premises *)
fun safe_asm_more_full_simp_tac ss = TRY o rot_eq_tac THEN' 
				     safe_asm_full_simp_tac ss;

(*Add a simpset to a classical set!*)
infix 4 addSss addss;
fun cs addSss ss = cs addSaltern (CHANGED o (safe_asm_more_full_simp_tac ss));
fun cs addss  ss = cs addbefore                        asm_full_simp_tac ss;

fun Addss ss = (claset := !claset addss ss);

(*Designed to be idempotent, except if best_tac instantiates variables
  in some of the subgoals*)

type clasimpset = (claset * simpset);

val HOL_css = (HOL_cs, HOL_ss);

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

fun auto_tac (cs,ss) = 
    let val cs' = cs addss ss 
    in  EVERY [TRY (safe_tac cs'),
	       REPEAT (FIRSTGOAL (fast_tac cs')),
               TRY (safe_tac (cs addSss ss)),
	       prune_params_tac] 
    end;

fun Auto_tac () = auto_tac (!claset, !simpset);

fun auto () = by (Auto_tac ());

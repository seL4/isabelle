(*  Title:      HOL/HOL_lemmas.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1991  University of Cambridge

Derived rules from Appendix of Mike Gordons HOL Report, Cambridge TR 68.
*)

(* ML bindings *)

val plusI = thm "plusI";
val minusI = thm "minusI";
val timesI = thm "timesI";
val powerI = thm "powerI";
val eq_reflection = thm "eq_reflection";
val refl = thm "refl";
val subst = thm "subst";
val ext = thm "ext";
val selectI = thm "selectI";
val impI = thm "impI";
val mp = thm "mp";
val True_def = thm "True_def";
val All_def = thm "All_def";
val Ex_def = thm "Ex_def";
val False_def = thm "False_def";
val not_def = thm "not_def";
val and_def = thm "and_def";
val or_def = thm "or_def";
val Ex1_def = thm "Ex1_def";
val iff = thm "iff";
val True_or_False = thm "True_or_False";
val Let_def = thm "Let_def";
val if_def = thm "if_def";
val arbitrary_def = thm "arbitrary_def";


(** Equality **)
section "=";

Goal "s=t ==> t=s";
by (etac subst 1);
by (rtac refl 1);
qed "sym";

(*calling "standard" reduces maxidx to 0*)
bind_thm ("ssubst", sym RS subst);

Goal "[| r=s; s=t |] ==> r=t";
by (etac subst 1 THEN assume_tac 1);
qed "trans";

val prems = goal (the_context ()) "(A == B) ==> A = B";
by (rewrite_goals_tac prems);
by (rtac refl 1);
qed "def_imp_eq";

(*Useful with eresolve_tac for proving equalties from known equalities.
        a = b
        |   |
        c = d   *)
Goal "[| a=b;  a=c;  b=d |] ==> c=d";
by (rtac trans 1);
by (rtac trans 1);
by (rtac sym 1);
by (REPEAT (assume_tac 1)) ;
qed "box_equals";

(** Congruence rules for meta-application **)
section "Congruence";

(*similar to AP_THM in Gordon's HOL*)
Goal "(f::'a=>'b) = g ==> f(x)=g(x)";
by (etac subst 1);
by (rtac refl 1);
qed "fun_cong";

(*similar to AP_TERM in Gordon's HOL and FOL's subst_context*)
Goal "x=y ==> f(x)=f(y)";
by (etac subst 1);
by (rtac refl 1);
qed "arg_cong";

Goal "[| f = g; (x::'a) = y |] ==> f(x) = g(y)";
by (etac subst 1);
by (etac subst 1);
by (rtac refl 1);
qed "cong";

(** Equality of booleans -- iff **)
section "iff";

val prems = Goal "[| P ==> Q;  Q ==> P |] ==> P=Q";
by (REPEAT (ares_tac (prems@[impI, iff RS mp RS mp]) 1));
qed "iffI";

Goal "[| P=Q; Q |] ==> P";
by (etac ssubst 1);
by (assume_tac 1);
qed "iffD2";

Goal "[| Q; P=Q |] ==> P";
by (etac iffD2 1);
by (assume_tac 1);
qed "rev_iffD2";

bind_thm ("iffD1", sym RS iffD2);
bind_thm ("rev_iffD1", sym RSN (2, rev_iffD2));

val [p1,p2] = Goal "[| P=Q; [| P --> Q; Q --> P |] ==> R |] ==> R";
by (REPEAT (ares_tac [p1 RS iffD2, p1 RS iffD1, p2, impI] 1));
qed "iffE";


(** True **)
section "True";

Goalw [True_def] "True";
by (rtac refl 1);
qed "TrueI";

Goal "P ==> P=True";
by (REPEAT (ares_tac [iffI,TrueI] 1));
qed "eqTrueI";

Goal "P=True ==> P";
by (etac iffD2 1);
by (rtac TrueI 1);
qed "eqTrueE";


(** Universal quantifier **)
section "!";

val prems = Goalw [All_def] "(!!x::'a. P(x)) ==> ! x. P(x)";
by (resolve_tac (prems RL [eqTrueI RS ext]) 1);
qed "allI";

Goalw [All_def] "! x::'a. P(x) ==> P(x)";
by (rtac eqTrueE 1);
by (etac fun_cong 1);
qed "spec";

val major::prems= goal (the_context ()) "[| ! x. P(x);  P(x) ==> R |] ==> R";
by (REPEAT (resolve_tac (prems @ [major RS spec]) 1)) ;
qed "allE";

val prems = goal (the_context ()) 
    "[| ! x. P(x);  [| P(x); ! x. P(x) |] ==> R |] ==> R";
by (REPEAT (resolve_tac (prems @ (prems RL [spec])) 1)) ;
qed "all_dupE";


(** False ** Depends upon spec; it is impossible to do propositional logic
             before quantifiers! **)
section "False";

Goalw [False_def] "False ==> P";
by (etac spec 1);
qed "FalseE";

Goal "False=True ==> P";
by (etac (eqTrueE RS FalseE) 1);
qed "False_neq_True";


(** Negation **)
section "~";

val prems = Goalw [not_def] "(P ==> False) ==> ~P";
by (rtac impI 1);
by (eresolve_tac prems 1);
qed "notI";

Goal "False ~= True";
by (rtac notI 1);
by (etac False_neq_True 1);
qed "False_not_True";

Goal "True ~= False";
by (rtac notI 1);
by (dtac sym 1);
by (etac False_neq_True 1);
qed "True_not_False";

Goalw [not_def] "[| ~P;  P |] ==> R";
by (etac (mp RS FalseE) 1);
by (assume_tac 1);
qed "notE";

bind_thm ("classical2", notE RS notI);

Goal "[| P; ~P |] ==> R";
by (etac notE 1);
by (assume_tac 1);
qed "rev_notE";


(** Implication **)
section "-->";

val prems = Goal "[| P-->Q;  P;  Q ==> R |] ==> R";
by (REPEAT (resolve_tac (prems@[mp]) 1));
qed "impE";

(* Reduces Q to P-->Q, allowing substitution in P. *)
Goal "[| P;  P --> Q |] ==> Q";
by (REPEAT (ares_tac [mp] 1)) ;
qed "rev_mp";

val [major,minor] = Goal "[| ~Q;  P==>Q |] ==> ~P";
by (rtac (major RS notE RS notI) 1);
by (etac minor 1) ;
qed "contrapos";

val [major,minor] = Goal "[| P==>Q; ~Q |] ==> ~P";
by (rtac (minor RS contrapos) 1);
by (etac major 1) ;
qed "rev_contrapos";

(* ~(?t = ?s) ==> ~(?s = ?t) *)
bind_thm("not_sym", sym COMP rev_contrapos);


(** Existential quantifier **)
section "?";

Goalw [Ex_def] "P x ==> ? x::'a. P x";
by (etac selectI 1) ;
qed "exI";

val [major,minor] = 
Goalw [Ex_def] "[| ? x::'a. P(x); !!x. P(x) ==> Q |] ==> Q";
by (rtac (major RS minor) 1);
qed "exE";


(** Conjunction **)
section "&";

Goalw [and_def] "[| P; Q |] ==> P&Q";
by (rtac (impI RS allI) 1);
by (etac (mp RS mp) 1);
by (REPEAT (assume_tac 1));
qed "conjI";

Goalw [and_def] "[| P & Q |] ==> P";
by (dtac spec 1) ;
by (etac mp 1);
by (REPEAT (ares_tac [impI] 1));
qed "conjunct1";

Goalw [and_def] "[| P & Q |] ==> Q";
by (dtac spec 1) ;
by (etac mp 1);
by (REPEAT (ares_tac [impI] 1));
qed "conjunct2";

val [major,minor] =
Goal "[| P&Q;  [| P; Q |] ==> R |] ==> R";
by (rtac minor 1);
by (rtac (major RS conjunct1) 1);
by (rtac (major RS conjunct2) 1);
qed "conjE";

val prems =
Goal "[| P; P ==> Q |] ==> P & Q";
by (REPEAT (resolve_tac (conjI::prems) 1));
qed "context_conjI";


(** Disjunction *)
section "|";

Goalw [or_def] "P ==> P|Q";
by (REPEAT (resolve_tac [allI,impI] 1));
by (etac mp 1 THEN assume_tac 1);
qed "disjI1";

Goalw [or_def] "Q ==> P|Q";
by (REPEAT (resolve_tac [allI,impI] 1));
by (etac mp 1 THEN assume_tac 1);
qed "disjI2";

val [major,minorP,minorQ] =
Goalw [or_def]  "[| P | Q; P ==> R; Q ==> R |] ==> R";
by (rtac (major RS spec RS mp RS mp) 1);
by (DEPTH_SOLVE (ares_tac [impI,minorP,minorQ] 1));
qed "disjE";


(** CCONTR -- classical logic **)
section "classical logic";

val [prem] = Goal  "(~P ==> P) ==> P";
by (rtac (True_or_False RS disjE RS eqTrueE) 1);
by (assume_tac 1);
by (rtac (notI RS prem RS eqTrueI) 1);
by (etac subst 1);
by (assume_tac 1);
qed "classical";

bind_thm ("ccontr", FalseE RS classical);

(*Double negation law*)
Goal "~~P ==> P";
by (rtac classical 1);
by (etac notE 1);
by (assume_tac 1);
qed "notnotD";

val [p1,p2] = Goal "[| Q; ~ P ==> ~ Q |] ==> P";
by (rtac classical 1);
by (dtac p2 1);
by (etac notE 1);
by (rtac p1 1);
qed "contrapos2";

val [p1,p2] = Goal "[| P;  Q ==> ~ P |] ==> ~ Q";
by (rtac notI 1);
by (dtac p2 1);
by (etac notE 1);
by (rtac p1 1);
qed "swap2";

(** Unique existence **)
section "?!";

val prems = Goalw [Ex1_def] "[| P(a);  !!x. P(x) ==> x=a |] ==> ?! x. P(x)";
by (REPEAT (ares_tac (prems@[exI,conjI,allI,impI]) 1));
qed "ex1I";

(*Sometimes easier to use: the premises have no shared variables.  Safe!*)
val [ex_prem,eq] = Goal
    "[| ? x. P(x);  !!x y. [| P(x); P(y) |] ==> x=y |] ==> ?! x. P(x)";
by (rtac (ex_prem RS exE) 1);
by (REPEAT (ares_tac [ex1I,eq] 1)) ;
qed "ex_ex1I";

val major::prems = Goalw [Ex1_def]
    "[| ?! x. P(x);  !!x. [| P(x);  ! y. P(y) --> y=x |] ==> R |] ==> R";
by (rtac (major RS exE) 1);
by (REPEAT (etac conjE 1 ORELSE ares_tac prems 1));
qed "ex1E";

Goal "?! x. P x ==> ? x. P x";
by (etac ex1E 1);
by (rtac exI 1);
by (assume_tac 1);
qed "ex1_implies_ex";


(** Select: Hilbert's Epsilon-operator **)
section "@";

(*Easier to apply than selectI: conclusion has only one occurrence of P*)
val prems = Goal
    "[| P a;  !!x. P x ==> Q x |] ==> Q (@x. P x)";
by (resolve_tac prems 1);
by (rtac selectI 1);
by (resolve_tac prems 1) ;
qed "selectI2";

(*Easier to apply than selectI2 if witness ?a comes from an EX-formula*)
val [major,minor] = Goal "[| ? a. P a;  !!x. P x ==> Q x |] ==> Q (Eps P)";
by (rtac (major RS exE) 1);
by (etac selectI2 1 THEN etac minor 1);
qed "selectI2EX";

val prems = Goal
    "[| P a;  !!x. P x ==> x=a |] ==> (@x. P x) = a";
by (rtac selectI2 1);
by (REPEAT (ares_tac prems 1)) ;
qed "select_equality";

Goalw [Ex1_def] "[| ?!x. P x; P a |] ==> (@x. P x) = a";
by (rtac select_equality 1);
by (atac 1);
by (etac exE 1);
by (etac conjE 1);
by (rtac allE 1);
by (atac 1);
by (etac impE 1);
by (atac 1);
by (etac ssubst 1);
by (etac allE 1);
by (etac mp 1);
by (atac 1);
qed "select1_equality";

Goal "P (@ x. P x) =  (? x. P x)";
by (rtac iffI 1);
by (etac exI 1);
by (etac exE 1);
by (etac selectI 1);
qed "select_eq_Ex";

Goal "(@y. y=x) = x";
by (rtac select_equality 1);
by (rtac refl 1);
by (atac 1);
qed "Eps_eq";

Goal "(Eps (op = x)) = x";
by (rtac select_equality 1);
by (rtac refl 1);
by (etac sym 1);
qed "Eps_sym_eq";

(** Classical intro rules for disjunction and existential quantifiers *)
section "classical intro rules";

val prems= Goal "(~Q ==> P) ==> P|Q";
by (rtac classical 1);
by (REPEAT (ares_tac (prems@[disjI1,notI]) 1));
by (REPEAT (ares_tac (prems@[disjI2,notE]) 1)) ;
qed "disjCI";

Goal "~P | P";
by (REPEAT (ares_tac [disjCI] 1)) ;
qed "excluded_middle";

(*For disjunctive case analysis*)
fun excluded_middle_tac sP =
    res_inst_tac [("Q",sP)] (excluded_middle RS disjE);

(*Classical implies (-->) elimination. *)
val major::prems = Goal "[| P-->Q; ~P ==> R; Q ==> R |] ==> R";
by (rtac (excluded_middle RS disjE) 1);
by (REPEAT (DEPTH_SOLVE_1 (ares_tac (prems @ [major RS mp]) 1)));
qed "impCE";

(*This version of --> elimination works on Q before P.  It works best for
  those cases in which P holds "almost everywhere".  Can't install as
  default: would break old proofs.*)
val major::prems = Goal
    "[| P-->Q;  Q ==> R;  ~P ==> R |] ==> R";
by (resolve_tac [excluded_middle RS disjE] 1);
by (DEPTH_SOLVE (ares_tac (prems@[major RS mp]) 1)) ;
qed "impCE'";

(*Classical <-> elimination. *)
val major::prems = Goal
    "[| P=Q;  [| P; Q |] ==> R;  [| ~P; ~Q |] ==> R |] ==> R";
by (rtac (major RS iffE) 1);
by (REPEAT (DEPTH_SOLVE_1 
	    (eresolve_tac ([asm_rl,impCE,notE]@prems) 1)));
qed "iffCE";

val prems = Goal "(! x. ~P(x) ==> P(a)) ==> ? x. P(x)";
by (rtac ccontr 1);
by (REPEAT (ares_tac (prems@[exI,allI,notI,notE]) 1))  ;
qed "exCI";

Goal "x + (y+z) = y + ((x+z)::'a::plus_ac0)";
by (rtac (thm"plus_ac0.commute" RS trans) 1);
by (rtac (thm"plus_ac0.assoc" RS trans) 1);
by (rtac (thm"plus_ac0.commute" RS arg_cong) 1);
qed "plus_ac0_left_commute";

Goal "x + 0 = (x ::'a::plus_ac0)";
by (rtac (thm"plus_ac0.commute" RS trans) 1);
by (rtac (thm"plus_ac0.zero") 1);
qed "plus_ac0_zero_right";

bind_thms ("plus_ac0", [thm"plus_ac0.assoc", thm"plus_ac0.commute", 
			plus_ac0_left_commute,
			thm"plus_ac0.zero", plus_ac0_zero_right]);

(* case distinction *)

val [prem1,prem2] = Goal "[| P ==> Q; ~P ==> Q |] ==> Q";
by (rtac (excluded_middle RS disjE) 1);
by (etac prem2 1);
by (etac prem1 1);
qed "case_split_thm";

fun case_tac a = res_inst_tac [("P",a)] case_split_thm;


(** Standard abbreviations **)

(*Apply an equality or definition ONCE.
  Fails unless the substitution has an effect*)
fun stac th = 
  let val th' = th RS def_imp_eq handle THM _ => th
  in  CHANGED_GOAL (rtac (th' RS ssubst))
  end;

(* combination of (spec RS spec RS ...(j times) ... spec RS mp *) 
local
  fun wrong_prem (Const ("All", _) $ (Abs (_, _, t))) = wrong_prem t
  |   wrong_prem (Bound _) = true
  |   wrong_prem _ = false;
  val filter_right = filter (fn t => not (wrong_prem (HOLogic.dest_Trueprop (hd (Thm.prems_of t)))));
in
  fun smp i = funpow i (fn m => filter_right ([spec] RL m)) ([mp]);
  fun smp_tac j = EVERY'[dresolve_tac (smp j), atac]
end;


fun strip_tac i = REPEAT(resolve_tac [impI,allI] i); 

(** strip ! and --> from proved goal while preserving !-bound var names **)

(** THIS CODE IS A MESS!!! **)

local

(* Use XXX to avoid forall_intr failing because of duplicate variable name *)
val myspec = read_instantiate [("P","?XXX")] spec;
val _ $ (_ $ (vx as Var(_,vxT))) = concl_of myspec;
val cvx = cterm_of (#sign(rep_thm myspec)) vx;
val aspec = forall_intr cvx myspec;

in

fun RSspec th =
  (case concl_of th of
     _ $ (Const("All",_) $ Abs(a,_,_)) =>
         let val ca = cterm_of (#sign(rep_thm th)) (Var((a,0),vxT))
         in th RS forall_elim ca aspec end
  | _ => raise THM("RSspec",0,[th]));

fun RSmp th =
  (case concl_of th of
     _ $ (Const("op -->",_)$_$_) => th RS mp
  | _ => raise THM("RSmp",0,[th]));

fun normalize_thm funs =
  let fun trans [] th = th
	| trans (f::fs) th = (trans funs (f th)) handle THM _ => trans fs th
  in zero_var_indexes o trans funs end;

fun qed_spec_mp name =
  let val thm = normalize_thm [RSspec,RSmp] (result())
  in ThmDatabase.ml_store_thm(name, thm) end;

fun qed_goal_spec_mp name thy s p = 
	bind_thm (name, normalize_thm [RSspec,RSmp] (prove_goal thy s p));

fun qed_goalw_spec_mp name thy defs s p = 
	bind_thm (name, normalize_thm [RSspec,RSmp] (prove_goalw thy defs s p));

end;


(* attributes *)

local

fun gen_rulify x =
  Attrib.no_args (Drule.rule_attribute (fn _ => (normalize_thm [RSspec, RSmp]))) x;

in

val attrib_setup =
 [Attrib.add_attributes
  [("rulify", (gen_rulify, gen_rulify), "put theorem into standard rule form")]];

end;

(*  Title:      HOL/Lex/RegExp2NAe.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

(******************************************************)
(*                       atom                         *)
(******************************************************)

Goalw [atom_def] "(fin (atom a) q) = (q = [False])";
by (Simp_tac 1);
qed "fin_atom";

Goalw [atom_def] "start (atom a) = [True]";
by (Simp_tac 1);
qed "start_atom";

(* Use {x. False} = {}? *)

Goalw [atom_def,step_def]
 "eps(atom a) = {}";
by (Simp_tac 1);
qed "eps_atom";
Addsimps [eps_atom];

Goalw [atom_def,step_def]
 "(p,q) : step (atom a) (Some b) = (p=[True] & q=[False] & b=a)";
by (Simp_tac 1);
qed "in_step_atom_Some";
Addsimps [in_step_atom_Some];

Goal "([False],[False]) : steps (atom a) w = (w = [])";
by (induct_tac "w" 1);
 by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [rel_comp_def]) 1);
qed "False_False_in_steps_atom";

Goal "(start (atom a), [False]) : steps (atom a) w = (w = [a])";
by (induct_tac "w" 1);
 by (asm_simp_tac (simpset() addsimps [start_atom,thm"rtrancl_empty"]) 1);
by (asm_full_simp_tac (simpset()
     addsimps [False_False_in_steps_atom,rel_comp_def,start_atom]) 1);
qed "start_fin_in_steps_atom";

Goal "accepts (atom a) w = (w = [a])";
by (simp_tac(simpset() addsimps
       [accepts_def,start_fin_in_steps_atom,fin_atom]) 1);
qed "accepts_atom";


(******************************************************)
(*                      or                            *)
(******************************************************)

(***** True/False ueber fin anheben *****)

Goalw [or_def] 
 "!L R. fin (or L R) (True#p) = fin L p";
by (Simp_tac 1);
qed_spec_mp "fin_or_True";

Goalw [or_def] 
 "!L R. fin (or L R) (False#p) = fin R p";
by (Simp_tac 1);
qed_spec_mp "fin_or_False";

AddIffs [fin_or_True,fin_or_False];

(***** True/False ueber step anheben *****)

Goalw [or_def,step_def]
"!L R. (True#p,q) : step (or L R) a = (? r. q = True#r & (p,r) : step L a)";
by (Simp_tac 1);
by (Blast_tac 1);
qed_spec_mp "True_in_step_or";

Goalw [or_def,step_def]
"!L R. (False#p,q) : step (or L R) a = (? r. q = False#r & (p,r) : step R a)";
by (Simp_tac 1);
by (Blast_tac 1);
qed_spec_mp "False_in_step_or";

AddIffs [True_in_step_or,False_in_step_or];

(***** True/False ueber epsclosure anheben *****)

Goal
 "(tp,tq) : (eps(or L R))^* ==> \
\ !p. tp = True#p --> (? q. (p,q) : (eps L)^* & tq = True#q)";
by (etac rtrancl_induct 1);
 by (Blast_tac 1);
by (Clarify_tac 1);
by (Asm_full_simp_tac 1);
by (blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
val lemma1a = result();

Goal
 "(tp,tq) : (eps(or L R))^* ==> \
\ !p. tp = False#p --> (? q. (p,q) : (eps R)^* & tq = False#q)";
by (etac rtrancl_induct 1);
 by (Blast_tac 1);
by (Clarify_tac 1);
by (Asm_full_simp_tac 1);
by (blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
val lemma1b = result();

Goal
 "(p,q) : (eps L)^*  ==> (True#p, True#q) : (eps(or L R))^*";
by (etac rtrancl_induct 1);
 by (Blast_tac 1);
by (blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
val lemma2a = result();

Goal
 "(p,q) : (eps R)^*  ==> (False#p, False#q) : (eps(or L R))^*";
by (etac rtrancl_induct 1);
 by (Blast_tac 1);
by (blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
val lemma2b = result();

Goal
 "(True#p,q) : (eps(or L R))^* = (? r. q = True#r & (p,r) : (eps L)^*)";
by (blast_tac (claset() addDs [lemma1a,lemma2a]) 1);
qed "True_epsclosure_or";

Goal
 "(False#p,q) : (eps(or L R))^* = (? r. q = False#r & (p,r) : (eps R)^*)";
by (blast_tac (claset() addDs [lemma1b,lemma2b]) 1);
qed "False_epsclosure_or";

AddIffs [True_epsclosure_or,False_epsclosure_or];

(***** True/False ueber steps anheben *****)

Goal
 "!p. (True#p,q):steps (or L R) w = (? r. q = True # r & (p,r):steps L w)";
by (induct_tac "w" 1);
 by Auto_tac;
by (Force_tac 1);
qed_spec_mp "lift_True_over_steps_or";

Goal 
 "!p. (False#p,q):steps (or L R) w = (? r. q = False#r & (p,r):steps R w)";
by (induct_tac "w" 1);
 by Auto_tac;
by (Force_tac 1);
qed_spec_mp "lift_False_over_steps_or";

AddIffs [lift_True_over_steps_or,lift_False_over_steps_or];


(***** Epsilonhuelle des Startzustands  *****)

Goal
 "R^* = Id Un (R^* O R)";
by (rtac set_ext 1);
by (split_all_tac 1);
by (rtac iffI 1);
 by (etac rtrancl_induct 1);
  by (Blast_tac 1);
 by (blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
by (blast_tac (claset() addIs [converse_rtrancl_into_rtrancl]) 1);
qed "unfold_rtrancl2";

Goal
 "(p,q) : R^* = (q = p | (? r. (p,r) : R & (r,q) : R^*))";
by (rtac (unfold_rtrancl2 RS equalityE) 1);
by (Blast_tac 1);
qed "in_unfold_rtrancl2";

val epsclosure_start_step_or =
  read_instantiate [("p","start(or L R)")] in_unfold_rtrancl2;
AddIffs [epsclosure_start_step_or];

Goalw [or_def,step_def]
 "!L R. (start(or L R),q) : eps(or L R) = \
\       (q = True#start L | q = False#start R)";
by (Simp_tac 1);
qed_spec_mp "start_eps_or";
AddIffs [start_eps_or];

Goalw [or_def,step_def]
 "!L R. (start(or L R),q) ~: step (or L R) (Some a)";
by (Simp_tac 1);
qed_spec_mp "not_start_step_or_Some";
AddIffs [not_start_step_or_Some];

Goal
 "(start(or L R), q) : steps (or L R) w = \
\ ( (w = [] & q = start(or L R)) | \
\   (? p.  q = True  # p & (start L,p) : steps L w | \
\          q = False # p & (start R,p) : steps R w) )";
by (case_tac "w" 1);
 by (Asm_simp_tac 1);
 by (Blast_tac 1);
by (Asm_simp_tac 1);
by (Blast_tac 1);
qed "steps_or";

Goalw [or_def]
 "!L R. ~ fin (or L R) (start(or L R))";
by (Simp_tac 1);
qed_spec_mp "start_or_not_final";
AddIffs [start_or_not_final];

Goalw [accepts_def]
 "accepts (or L R) w = (accepts L w | accepts R w)";
by (simp_tac (simpset() addsimps [steps_or]) 1);
by Auto_tac;
qed "accepts_or";


(******************************************************)
(*                      conc                          *)
(******************************************************)

(** True/False in fin **)

Goalw [conc_def]
 "!L R. fin (conc L R) (True#p) = False";
by (Simp_tac 1);
qed_spec_mp "fin_conc_True";

Goalw [conc_def] 
 "!L R. fin (conc L R) (False#p) = fin R p";
by (Simp_tac 1);
qed "fin_conc_False";

AddIffs [fin_conc_True,fin_conc_False];

(** True/False in step **)

Goalw [conc_def,step_def]
 "!L R. (True#p,q) : step (conc L R) a = \
\       ((? r. q=True#r & (p,r): step L a) | \
\        (fin L p & a=None & q=False#start R))";
by (Simp_tac 1);
by (Blast_tac 1);
qed_spec_mp "True_step_conc";

Goalw [conc_def,step_def]
 "!L R. (False#p,q) : step (conc L R) a = \
\       (? r. q = False#r & (p,r) : step R a)";
by (Simp_tac 1);
by (Blast_tac 1);
qed_spec_mp "False_step_conc";

AddIffs [True_step_conc, False_step_conc];

(** False in epsclosure **)

Goal
 "(tp,tq) : (eps(conc L R))^* ==> \
\ !p. tp = False#p --> (? q. (p,q) : (eps R)^* & tq = False#q)";
by (etac rtrancl_induct 1);
 by (Blast_tac 1);
by (blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
qed "lemma1b";

Goal
 "(p,q) : (eps R)^* ==> (False#p, False#q) : (eps(conc L R))^*";
by (etac rtrancl_induct 1);
 by (Blast_tac 1);
by (blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
val lemma2b = result();

Goal
 "((False # p, q) : (eps (conc L R))^*) = \
\ (? r. q = False # r & (p, r) : (eps R)^*)";
by (rtac iffI 1);
 by (blast_tac (claset() addDs [lemma1b]) 1);
by (blast_tac (claset() addDs [lemma2b]) 1);
qed "False_epsclosure_conc";
AddIffs [False_epsclosure_conc];

(** False in steps **)

Goal
 "!p. (False#p,q): steps (conc L R) w = (? r. q=False#r & (p,r): steps R w)";
by (induct_tac "w" 1);
 by (Simp_tac 1);
by (Simp_tac 1);
by (Fast_tac 1);  (*MUCH faster than Blast_tac*)
qed_spec_mp "False_steps_conc";
AddIffs [False_steps_conc];

(** True in epsclosure **)

Goal
 "(p,q): (eps L)^* ==> (True#p,True#q) : (eps(conc L R))^*";
by (etac rtrancl_induct 1);
 by (Blast_tac 1);
by (blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
qed "True_True_eps_concI";

Goal
 "!p. (p,q) : steps L w --> (True#p,True#q) : steps (conc L R) w";
by (induct_tac "w" 1);
 by (simp_tac (simpset() addsimps [True_True_eps_concI]) 1);
by (Simp_tac 1);
by (blast_tac (claset() addIs [True_True_eps_concI]) 1);
qed_spec_mp "True_True_steps_concI";

Goal
 "(tp,tq) : (eps(conc L R))^* ==> \
\ !p. tp = True#p --> \
\ (? q. tq = True#q & (p,q) : (eps L)^*) | \
\ (? q r. tq = False#q & (p,r):(eps L)^* & fin L r & (start R,q) : (eps R)^*)";
by (etac rtrancl_induct 1);
 by (Blast_tac 1);
by (blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
val lemma1a = result();

Goal
 "(p, q) : (eps L)^* ==> (True#p, True#q) : (eps(conc L R))^*";
by (etac rtrancl_induct 1);
 by (Blast_tac 1);
by (blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
val lemma2a = result();

Goalw [conc_def,step_def]
 "!!L R. (p,q) : step R None ==> (False#p, False#q) : step (conc L R) None";
by (split_all_tac 1);
by (Asm_full_simp_tac 1);
val lemma = result();

Goal
 "(p,q) : (eps R)^* ==> (False#p, False#q) : (eps(conc L R))^*";
by (etac rtrancl_induct 1);
 by (Blast_tac 1);
by (dtac lemma 1);
by (blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
val lemma2b = result();

Goalw [conc_def,step_def]
 "!!L R. fin L p ==> (True#p, False#start R) : eps(conc L R)";
by (split_all_tac 1);
by (Asm_full_simp_tac 1);
qed "True_False_eps_concI";

Goal
 "((True#p,q) : (eps(conc L R))^*) = \
\ ((? r. (p,r) : (eps L)^* & q = True#r) | \
\  (? r. (p,r) : (eps L)^* & fin L r & \
\        (? s. (start R, s) : (eps R)^* & q = False#s)))";
by (rtac iffI 1);
 by (blast_tac (claset() addDs [lemma1a]) 1);
by (etac disjE 1);
 by (blast_tac (claset() addIs [lemma2a]) 1);
by (Clarify_tac 1);
by (rtac (rtrancl_trans) 1);
by (etac lemma2a 1);
by (rtac converse_rtrancl_into_rtrancl 1);
by (etac True_False_eps_concI 1);
by (etac lemma2b 1);
qed "True_epsclosure_conc";
AddIffs [True_epsclosure_conc];

(** True in steps **)

Goal
 "!p. (True#p,q) : steps (conc L R) w --> \
\     ((? r. (p,r) : steps L w & q = True#r)  | \
\      (? u v. w = u@v & (? r. (p,r) : steps L u & fin L r & \
\              (? s. (start R,s) : steps R v & q = False#s))))";
by (induct_tac "w" 1);
 by (Simp_tac 1);
by (Simp_tac 1);
by (clarify_tac (claset() delrules [disjCI]) 1);
 by (etac disjE 1);
 by (clarify_tac (claset() delrules [disjCI]) 1);
 by (etac disjE 1);
  by (clarify_tac (claset() delrules [disjCI]) 1);
  by (etac allE 1 THEN mp_tac 1);
  by (etac disjE 1);
   by (Blast_tac 1);
  by (rtac disjI2 1);
  by (Clarify_tac 1);
  by (Simp_tac 1);
  by (res_inst_tac[("x","a#u")] exI 1);
  by (Simp_tac 1);
  by (Blast_tac 1);
 by (Blast_tac 1);
by (rtac disjI2 1);
by (Clarify_tac 1);
by (Simp_tac 1);
by (res_inst_tac[("x","[]")] exI 1);
by (Simp_tac 1);
by (Blast_tac 1);
qed_spec_mp "True_steps_concD";

Goal
 "(True#p,q) : steps (conc L R) w = \
\ ((? r. (p,r) : steps L w & q = True#r)  | \
\  (? u v. w = u@v & (? r. (p,r) : steps L u & fin L r & \
\          (? s. (start R,s) : steps R v & q = False#s))))";
by (blast_tac (claset() addDs [True_steps_concD]
     addIs [True_True_steps_concI,in_steps_epsclosure]) 1);
qed "True_steps_conc";

(** starting from the start **)

Goalw [conc_def]
  "!L R. start(conc L R) = True#start L";
by (Simp_tac 1);
qed_spec_mp "start_conc";

Goalw [conc_def]
 "!L R. fin(conc L R) p = (? s. p = False#s & fin R s)";
by (simp_tac (simpset() addsplits [thm"list.split"]) 1);
qed_spec_mp "final_conc";

Goal
 "accepts (conc L R) w = (? u v. w = u@v & accepts L u & accepts R v)";
by (simp_tac (simpset() addsimps
     [accepts_def,True_steps_conc,final_conc,start_conc]) 1);
by (Blast_tac 1);
qed "accepts_conc";

(******************************************************)
(*                       star                         *)
(******************************************************)

Goalw [star_def,step_def]
 "!A. (True#p,q) : eps(star A) = \
\     ( (? r. q = True#r & (p,r) : eps A) | (fin A p & q = True#start A) )";
by (Simp_tac 1);
by (Blast_tac 1);
qed_spec_mp "True_in_eps_star";
AddIffs [True_in_eps_star];

Goalw [star_def,step_def]
  "!A. (p,q) : step A a --> (True#p, True#q) : step (star A) a";
by (Simp_tac 1);
qed_spec_mp "True_True_step_starI";

Goal
  "(p,r) : (eps A)^* ==> (True#p, True#r) : (eps(star A))^*";
by (etac rtrancl_induct 1);
 by (Blast_tac 1);
by (blast_tac (claset() addIs [True_True_step_starI,rtrancl_into_rtrancl]) 1);
qed_spec_mp "True_True_eps_starI";

Goalw [star_def,step_def]
 "!A. fin A p --> (True#p,True#start A) : eps(star A)";
by (Simp_tac 1);
qed_spec_mp "True_start_eps_starI";

Goal
 "(tp,s) : (eps(star A))^* ==> (! p. tp = True#p --> \
\ (? r. ((p,r) : (eps A)^* | \
\        (? q. (p,q) : (eps A)^* & fin A q & (start A,r) : (eps A)^*)) & \
\       s = True#r))";
by (etac rtrancl_induct 1);
 by (Simp_tac 1);
by (Clarify_tac 1);
by (Asm_full_simp_tac 1);
by (blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
val lemma = result();

Goal
 "((True#p,s) : (eps(star A))^*) = \
\ (? r. ((p,r) : (eps A)^* | \
\        (? q. (p,q) : (eps A)^* & fin A q & (start A,r) : (eps A)^*)) & \
\       s = True#r)";
by (rtac iffI 1);
 by (dtac lemma 1);
 by (Blast_tac 1);
(* Why can't blast_tac do the rest? *)
by (Clarify_tac 1);
by (etac disjE 1);
by (etac True_True_eps_starI 1);
by (Clarify_tac 1);
by (rtac rtrancl_trans 1);
by (etac True_True_eps_starI 1);
by (rtac rtrancl_trans 1);
by (rtac r_into_rtrancl 1);
by (etac True_start_eps_starI 1);
by (etac True_True_eps_starI 1);
qed "True_eps_star";
AddIffs [True_eps_star];

(** True in step Some **)

Goalw [star_def,step_def]
 "!A. (True#p,r): step (star A) (Some a) = \
\     (? q. (p,q): step A (Some a) & r=True#q)";
by (Simp_tac 1);
by (Blast_tac 1);
qed_spec_mp "True_step_star";
AddIffs [True_step_star];


(** True in steps **)

(* reverse list induction! Complicates matters for conc? *)
Goal
 "!rr. (True#start A,rr) : steps (star A) w --> \
\ (? us v. w = concat us @ v & \
\             (!u:set us. accepts A u) & \
\             (? r. (start A,r) : steps A v & rr = True#r))";
by (res_inst_tac [("xs","w")] rev_induct 1);
 by (Asm_full_simp_tac 1);
 by (Clarify_tac 1);
 by (res_inst_tac [("x","[]")] exI 1);
 by (etac disjE 1);
  by (Asm_simp_tac 1);
 by (Clarify_tac 1);
 by (Asm_simp_tac 1);
by (simp_tac (simpset() addsimps [O_assoc,epsclosure_steps]) 1);
by (Clarify_tac 1);
by (etac allE 1 THEN mp_tac 1);
by (Clarify_tac 1);
by (etac disjE 1);
 by (res_inst_tac [("x","us")] exI 1);
 by (res_inst_tac [("x","v@[x]")] exI 1);
 by (asm_simp_tac (simpset() addsimps [O_assoc,epsclosure_steps]) 1);
 by (Blast_tac 1);
by (Clarify_tac 1);
by (res_inst_tac [("x","us@[v@[x]]")] exI 1);
by (res_inst_tac [("x","[]")] exI 1);
by (asm_full_simp_tac (simpset() addsimps [accepts_def]) 1);
by (Blast_tac 1);
qed_spec_mp "True_start_steps_starD";

Goal "!p. (p,q) : steps A w --> (True#p,True#q) : steps (star A) w";
by (induct_tac "w" 1);
 by (Simp_tac 1);
by (Simp_tac 1);
by (blast_tac (claset() addIs [True_True_eps_starI,True_True_step_starI]) 1);
qed_spec_mp "True_True_steps_starI";

Goalw [accepts_def]
 "(!u : set us. accepts A u) --> \
\ (True#start A,True#start A) : steps (star A) (concat us)";
by (induct_tac "us" 1);
 by (Simp_tac 1);
by (Simp_tac 1);
by (blast_tac (claset() addIs [True_True_steps_starI,True_start_eps_starI,in_epsclosure_steps]) 1);
qed_spec_mp "steps_star_cycle";

(* Better stated directly with start(star A)? Loop in star A back to start(star A)?*)
Goal
 "(True#start A,rr) : steps (star A) w = \
\ (? us v. w = concat us @ v & \
\             (!u:set us. accepts A u) & \
\             (? r. (start A,r) : steps A v & rr = True#r))";
by (rtac iffI 1);
 by (etac True_start_steps_starD 1);
by (Clarify_tac 1);
by (Asm_simp_tac 1);
by (blast_tac (claset() addIs [True_True_steps_starI,steps_star_cycle]) 1);
qed "True_start_steps_star";

(** the start state **)

Goalw [star_def,step_def]
  "!A. (start(star A),r) : step (star A) a = (a=None & r = True#start A)";
by (Simp_tac 1);
qed_spec_mp "start_step_star";
AddIffs [start_step_star];

val epsclosure_start_step_star =
  read_instantiate [("p","start(star A)")] in_unfold_rtrancl2;

Goal
 "(start(star A),r) : steps (star A) w = \
\ ((w=[] & r= start(star A)) | (True#start A,r) : steps (star A) w)";
by (rtac iffI 1);
 by (case_tac "w" 1);
  by (asm_full_simp_tac (simpset() addsimps
    [epsclosure_start_step_star]) 1);
 by (Asm_full_simp_tac 1);
 by (Clarify_tac 1);
 by (asm_full_simp_tac (simpset() addsimps
    [epsclosure_start_step_star]) 1);
 by (Blast_tac 1);
by (etac disjE 1);
 by (Asm_simp_tac 1);
by (blast_tac (claset() addIs [in_steps_epsclosure]) 1);
qed "start_steps_star";

Goalw [star_def] "!A. fin (star A) (True#p) = fin A p";
by (Simp_tac 1);
qed_spec_mp "fin_star_True";
AddIffs [fin_star_True];

Goalw [star_def] "!A. fin (star A) (start(star A))";
by (Simp_tac 1);
qed_spec_mp "fin_star_start";
AddIffs [fin_star_start];

(* too complex! Simpler if loop back to start(star A)? *)
Goalw [accepts_def]
 "accepts (star A) w = \
\ (? us. (!u : set(us). accepts A u) & (w = concat us) )";
by (simp_tac (simpset() addsimps [start_steps_star,True_start_steps_star]) 1);
by (rtac iffI 1);
 by (Clarify_tac 1);
 by (etac disjE 1);
  by (Clarify_tac 1);
  by (Simp_tac 1);
  by (res_inst_tac [("x","[]")] exI 1);
  by (Simp_tac 1);
 by (Clarify_tac 1);
 by (res_inst_tac [("x","us@[v]")] exI 1);
 by (asm_full_simp_tac (simpset() addsimps [accepts_def]) 1);
 by (Blast_tac 1);
by (Clarify_tac 1);
by (res_inst_tac [("xs","us")] rev_exhaust 1);
 by (Asm_simp_tac 1);
 by (Blast_tac 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [accepts_def]) 1);
by (Blast_tac 1);
qed "accepts_star";


(***** Correctness of r2n *****)

Goal
 "!w. accepts (rexp2nae r) w = (w : lang r)";
by (induct_tac "r" 1);
    by (simp_tac (simpset() addsimps [accepts_def]) 1);
   by (simp_tac(simpset() addsimps [accepts_atom]) 1);
  by (asm_simp_tac (simpset() addsimps [accepts_or]) 1);
 by (asm_simp_tac (simpset() addsimps [accepts_conc,RegSet.conc_def]) 1);
by (asm_simp_tac (simpset() addsimps [accepts_star,in_star]) 1);
qed "accepts_rexp2nae";

(*  Title:      HOL/Lex/NAe_of_RegExp.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

(******************************************************)
(*                       atom                         *)
(******************************************************)

goalw thy [atom_def] "(fin (atom a) q) = (q = [False])";
by(Simp_tac 1);
qed "fin_atom";

goalw thy [atom_def] "start (atom a) = [True]";
by(Simp_tac 1);
qed "start_atom";

(* Use {x. False} = {}? *)

goalw thy [atom_def,step_def]
 "eps(atom a) = {}";
by(Simp_tac 1);
by (Blast_tac 1);
qed "eps_atom";
Addsimps [eps_atom];

goalw thy [atom_def,step_def]
 "(p,q) : step (atom a) (Some b) = (p=[True] & q=[False] & b=a)";
by(Simp_tac 1);
qed "in_step_atom_Some";
Addsimps [in_step_atom_Some];

goal thy
 "([False],[False]) : steps (atom a) w = (w = [])";
by (induct_tac "w" 1);
 by(Simp_tac 1);
by(asm_simp_tac (simpset() addsimps [comp_def]) 1);
qed "False_False_in_steps_atom";

goal thy
 "(start (atom a), [False]) : steps (atom a) w = (w = [a])";
by (induct_tac "w" 1);
 by(asm_simp_tac (simpset() addsimps [start_atom,rtrancl_empty]) 1);
by(asm_full_simp_tac (simpset()
     addsimps [False_False_in_steps_atom,comp_def,start_atom]) 1);
qed "start_fin_in_steps_atom";

(******************************************************)
(*                      union                         *)
(******************************************************)

(***** True/False ueber fin anheben *****)

goalw thy [union_def] 
 "!L R. fin (union L R) (True#p) = fin L p";
by (Simp_tac 1);
qed_spec_mp "fin_union_True";

goalw thy [union_def] 
 "!L R. fin (union L R) (False#p) = fin R p";
by (Simp_tac 1);
qed_spec_mp "fin_union_False";

AddIffs [fin_union_True,fin_union_False];

(***** True/False ueber step anheben *****)

goalw thy [union_def,step_def]
"!L R. (True#p,q) : step (union L R) a = (? r. q = True#r & (p,r) : step L a)";
by (Simp_tac 1);
by(Blast_tac 1);
qed_spec_mp "True_in_step_union";

goalw thy [union_def,step_def]
"!L R. (False#p,q) : step (union L R) a = (? r. q = False#r & (p,r) : step R a)";
by (Simp_tac 1);
by(Blast_tac 1);
qed_spec_mp "False_in_step_union";

AddIffs [True_in_step_union,False_in_step_union];

(***** True/False ueber epsclosure anheben *****)

goal thy
 "!!d. (tp,tq) : (eps(union L R))^* ==> \
\ !p. tp = True#p --> (? q. (p,q) : (eps L)^* & tq = True#q)";
be rtrancl_induct 1;
 by(Blast_tac 1);
by(Clarify_tac 1);
by(Asm_full_simp_tac 1);
by(blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
val lemma1a = result();

goal thy
 "!!d. (tp,tq) : (eps(union L R))^* ==> \
\ !p. tp = False#p --> (? q. (p,q) : (eps R)^* & tq = False#q)";
be rtrancl_induct 1;
 by(Blast_tac 1);
by(Clarify_tac 1);
by(Asm_full_simp_tac 1);
by(blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
val lemma1b = result();

goal thy
 "!!p. (p,q) : (eps L)^*  ==> (True#p, True#q) : (eps(union L R))^*";
be rtrancl_induct 1;
 by(Blast_tac 1);
by(blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
val lemma2a = result();

goal thy
 "!!p. (p,q) : (eps R)^*  ==> (False#p, False#q) : (eps(union L R))^*";
be rtrancl_induct 1;
 by(Blast_tac 1);
by(blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
val lemma2b = result();

goal thy
 "(True#p,q) : (eps(union L R))^* = (? r. q = True#r & (p,r) : (eps L)^*)";
by(blast_tac (claset() addDs [lemma1a,lemma2a]) 1);
qed "True_epsclosure_union";

goal thy
 "(False#p,q) : (eps(union L R))^* = (? r. q = False#r & (p,r) : (eps R)^*)";
by(blast_tac (claset() addDs [lemma1b,lemma2b]) 1);
qed "False_epsclosure_union";

AddIffs [True_epsclosure_union,False_epsclosure_union];

(***** True/False ueber steps anheben *****)

goal thy
 "!p. (True#p,q):steps (union L R) w = (? r. q = True # r & (p,r):steps L w)";
by (induct_tac "w" 1);
by (ALLGOALS Asm_simp_tac);
(* Blast_tac produces PROOF FAILED for depth 8 *)
by(Fast_tac 1);
qed_spec_mp "lift_True_over_steps_union";

goal thy 
 "!p. (False#p,q):steps (union L R) w = (? r. q = False#r & (p,r):steps R w)";
by (induct_tac "w" 1);
by (ALLGOALS Asm_simp_tac);
(* Blast_tac produces PROOF FAILED for depth 8 *)
by(Fast_tac 1);
qed_spec_mp "lift_False_over_steps_union";

AddIffs [lift_True_over_steps_union,lift_False_over_steps_union];


(***** Epsilonhuelle des Startzustands  *****)

goal thy
 "R^* = id Un (R^* O R)";
by(rtac set_ext 1);
by(split_all_tac 1);
by(rtac iffI 1);
 be rtrancl_induct 1;
  by(Blast_tac 1);
 by(blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
by(blast_tac (claset() addIs [rtrancl_into_rtrancl2]) 1);
qed "unfold_rtrancl2";

goal thy
 "(p,q) : R^* = (q = p | (? r. (p,r) : R & (r,q) : R^*))";
by(rtac (unfold_rtrancl2 RS equalityE) 1);
by(Blast_tac 1);
qed "in_unfold_rtrancl2";

val epsclosure_start_step_union =
  read_instantiate [("p","start(union L R)")] in_unfold_rtrancl2;
AddIffs [epsclosure_start_step_union];

goalw thy [union_def,step_def]
 "!L R. (start(union L R),q) : eps(union L R) = \
\       (q = True#start L | q = False#start R)";
by(Simp_tac 1);
qed_spec_mp "start_eps_union";
AddIffs [start_eps_union];

goalw thy [union_def,step_def]
 "!L R. (start(union L R),q) ~: step (union L R) (Some a)";
by(Simp_tac 1);
qed_spec_mp "not_start_step_union_Some";
AddIffs [not_start_step_union_Some];

goal thy
 "(start(union L R), q) : steps (union L R) w = \
\ ( (w = [] & q = start(union L R)) | \
\   (? p.  q = True  # p & (start L,p) : steps L w | \
\          q = False # p & (start R,p) : steps R w) )";
by (exhaust_tac "w" 1);
 by (Asm_simp_tac 1);
 (* Blast_tac produces PROOF FAILED! *)
 by(Fast_tac 1);
by (Asm_simp_tac 1);
(* The goal is now completely dual to the first one.
   Fast/Best_tac don't return. Blast_tac produces PROOF FAILED!
   The lemmas used in the explicit proof are part of the claset already!
*)
br iffI 1;
 by(Blast_tac 1);
by(Clarify_tac 1);
be disjE 1;
 by(Blast_tac 1);
by(Clarify_tac 1);
br compI 1;
br compI 1;
br (epsclosure_start_step_union RS iffD2) 1;
br disjI2 1;
br exI 1;
br conjI 1;
br (start_eps_union RS iffD2) 1;
br disjI2 1;
br refl 1;
by(Clarify_tac 1);
br exI 1;
br conjI 1;
br refl 1;
ba 1;
by(Clarify_tac 1);
br exI 1;
br conjI 1;
br refl 1;
ba 1;
by(Clarify_tac 1);
br exI 1;
br conjI 1;
br refl 1;
ba 1;
qed "steps_union";

goalw thy [union_def]
 "!L R. ~ fin (union L R) (start(union L R))";
by(Simp_tac 1);
qed_spec_mp "start_union_not_final";
AddIffs [start_union_not_final];

goalw thy [accepts_def]
 "accepts (union L R) w = (accepts L w | accepts R w)";
by (simp_tac (simpset() addsimps [steps_union]) 1);
auto();
qed "final_union";


(******************************************************)
(*                      conc                        *)
(******************************************************)

(** True/False in fin **)

goalw thy [conc_def]
 "!L R. fin (conc L R) (True#p) = False";
by (Simp_tac 1);
qed_spec_mp "fin_conc_True";

goalw thy [conc_def] 
 "!L R. fin (conc L R) (False#p) = fin R p";
by (Simp_tac 1);
qed "fin_conc_False";

AddIffs [fin_conc_True,fin_conc_False];

(** True/False in step **)

goalw thy [conc_def,step_def]
 "!L R. (True#p,q) : step (conc L R) a = \
\       ((? r. q=True#r & (p,r): step L a) | \
\        (fin L p & a=None & q=False#start R))";
by (Simp_tac 1);
by(Blast_tac 1);
qed_spec_mp "True_step_conc";

goalw thy [conc_def,step_def]
 "!L R. (False#p,q) : step (conc L R) a = \
\       (? r. q = False#r & (p,r) : step R a)";
by (Simp_tac 1);
by(Blast_tac 1);
qed_spec_mp "False_step_conc";

AddIffs [True_step_conc, False_step_conc];

(** False in epsclosure **)

goal thy
 "!!d. (tp,tq) : (eps(conc L R))^* ==> \
\ !p. tp = False#p --> (? q. (p,q) : (eps R)^* & tq = False#q)";
by(etac rtrancl_induct 1);
 by(Blast_tac 1);
by(blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
qed "lemma1b";

goal thy
 "!!p. (p,q) : (eps R)^* ==> (False#p, False#q) : (eps(conc L R))^*";
by(etac rtrancl_induct 1);
 by(Blast_tac 1);
by(blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
val lemma2b = result();

goal thy
 "((False # p, q) : (eps (conc L R))^*) = \
\ (? r. q = False # r & (p, r) : (eps R)^*)";
by (rtac iffI 1);
 by(blast_tac (claset() addDs [lemma1b]) 1);
by(blast_tac (claset() addDs [lemma2b]) 1);
qed "False_epsclosure_conc";
AddIffs [False_epsclosure_conc];

(** False in steps **)

goal thy
 "!p. (False#p,q): steps (conc L R) w = (? r. q=False#r & (p,r): steps R w)";
by (induct_tac "w" 1);
 by (Simp_tac 1);
by (Simp_tac 1);
(* Blast_tac produces PROOF FAILED for depth 8 *)
by(Fast_tac 1);
qed_spec_mp "False_steps_conc";
AddIffs [False_steps_conc];

(** True in epsclosure **)

goal thy
 "!!L R. (p,q): (eps L)^* ==> (True#p,True#q) : (eps(conc L R))^*";
be rtrancl_induct 1;
 by(Blast_tac 1);
by(blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
qed "True_True_eps_concI";

goal thy
 "!!L R. !p. (p,q) : steps L w --> (True#p,True#q) : steps (conc L R) w";
by(induct_tac "w" 1);
 by (simp_tac (simpset() addsimps [True_True_eps_concI]) 1);
by (Simp_tac 1);
by(blast_tac (claset() addIs [True_True_eps_concI]) 1);
qed_spec_mp "True_True_steps_concI";

goal thy
 "!!d. (tp,tq) : (eps(conc L R))^* ==> \
\ !p. tp = True#p --> \
\ (? q. tq = True#q & (p,q) : (eps L)^*) | \
\ (? q r. tq = False#q & (p,r):(eps L)^* & fin L r & (start R,q) : (eps R)^*)";
by(etac rtrancl_induct 1);
 by(Blast_tac 1);
by(blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
val lemma1a = result();

goal thy
 "!!p. (p, q) : (eps L)^* ==> (True#p, True#q) : (eps(conc L R))^*";
by(etac rtrancl_induct 1);
 by(Blast_tac 1);
by(blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
val lemma2a = result();

goalw thy [conc_def,step_def]
 "!!L R. (p,q) : step R None ==> (False#p, False#q) : step (conc L R) None";
by(split_all_tac 1);
by (Asm_full_simp_tac 1);
val lemma = result();

goal thy
 "!!L R. (p,q) : (eps R)^* ==> (False#p, False#q) : (eps(conc L R))^*";
by(etac rtrancl_induct 1);
 by(Blast_tac 1);
by (dtac lemma 1);
by(blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
val lemma2b = result();

goalw thy [conc_def,step_def]
 "!!L R. fin L p ==> (True#p, False#start R) : eps(conc L R)";
by(split_all_tac 1);
by(Asm_full_simp_tac 1);
qed "True_False_eps_concI";

goal thy
 "((True#p,q) : (eps(conc L R))^*) = \
\ ((? r. (p,r) : (eps L)^* & q = True#r) | \
\  (? r. (p,r) : (eps L)^* & fin L r & \
\        (? s. (start R, s) : (eps R)^* & q = False#s)))";
by(rtac iffI 1);
 by(blast_tac (claset() addDs [lemma1a]) 1);
be disjE 1;
 by(blast_tac (claset() addIs [lemma2a]) 1);
by(Clarify_tac 1);
br (rtrancl_trans) 1;
be lemma2a 1;
br (rtrancl_into_rtrancl2) 1;
be True_False_eps_concI 1;
be lemma2b 1;
qed "True_epsclosure_conc";
AddIffs [True_epsclosure_conc];

(** True in steps **)

goal thy
 "!p. (True#p,q) : steps (conc L R) w --> \
\     ((? r. (p,r) : steps L w & q = True#r)  | \
\      (? u v. w = u@v & (? r. (p,r) : steps L u & fin L r & \
\              (? s. (start R,s) : steps R v & q = False#s))))";
by(induct_tac "w" 1);
 by(Simp_tac 1);
by(Simp_tac 1);
by(clarify_tac (claset() delrules [disjCI]) 1);
 be disjE 1;
 by(clarify_tac (claset() delrules [disjCI]) 1);
 be disjE 1;
  by(clarify_tac (claset() delrules [disjCI]) 1);
  by(etac allE 1 THEN mp_tac 1);
  be disjE 1;
   by (Blast_tac 1);
  br disjI2 1;
  by (Clarify_tac 1);
  by(Simp_tac 1);
  by(res_inst_tac[("x","a#u")] exI 1);
  by(Simp_tac 1);
  by (Blast_tac 1);
 by (Blast_tac 1);
br disjI2 1;
by (Clarify_tac 1);
by(Simp_tac 1);
by(res_inst_tac[("x","[]")] exI 1);
by(Simp_tac 1);
by (Blast_tac 1);
qed_spec_mp "True_steps_concD";

goal thy
 "(True#p,q) : steps (conc L R) w = \
\ ((? r. (p,r) : steps L w & q = True#r)  | \
\  (? u v. w = u@v & (? r. (p,r) : steps L u & fin L r & \
\          (? s. (start R,s) : steps R v & q = False#s))))";
by(blast_tac (claset() addDs [True_steps_concD]
     addIs [True_True_steps_concI,in_steps_epsclosure,r_into_rtrancl]) 1);
qed "True_steps_conc";

(** starting from the start **)

goalw thy [conc_def]
  "!L R. start(conc L R) = True#start L";
by(Simp_tac 1);
qed_spec_mp "start_conc";

goalw thy [conc_def]
 "!L R. fin(conc L R) p = (? s. p = False#s & fin R s)";
by (simp_tac (simpset() addsplits [split_list_case]) 1);
qed_spec_mp "final_conc";


(******************************************************)
(*                       star                         *)
(******************************************************)

goalw thy [star_def,step_def]
 "!A. (True#p,q) : eps(star A) = \
\     ( (? r. q = True#r & (p,r) : eps A) | (fin A p & q = True#start A) )";
by(Simp_tac 1);
by(Blast_tac 1);
qed_spec_mp "True_in_eps_star";
AddIffs [True_in_eps_star];

goalw thy [star_def,step_def]
  "!A. (p,q) : step A a --> (True#p, True#q) : step (star A) a";
by(Simp_tac 1);
qed_spec_mp "True_True_step_starI";

goal thy
  "!!A. (p,r) : (eps A)^* ==> (True#p, True#r) : (eps(star A))^*";
be rtrancl_induct 1;
 by(Blast_tac 1);
by(blast_tac (claset() addIs [True_True_step_starI,rtrancl_into_rtrancl]) 1);
qed_spec_mp "True_True_eps_starI";

goalw thy [star_def,step_def]
 "!A. fin A p --> (True#p,True#start A) : eps(star A)";
by(Simp_tac 1);
qed_spec_mp "True_start_eps_starI";

goal thy
 "!!dummy. (tp,s) : (eps(star A))^* ==> (! p. tp = True#p --> \
\ (? r. ((p,r) : (eps A)^* | \
\        (? q. (p,q) : (eps A)^* & fin A q & (start A,r) : (eps A)^*)) & \
\       s = True#r))";
be rtrancl_induct 1;
 by(Simp_tac 1);
by (Clarify_tac 1);
by (Asm_full_simp_tac 1);
by(blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
val lemma = result();

goal thy
 "((True#p,s) : (eps(star A))^*) = \
\ (? r. ((p,r) : (eps A)^* | \
\        (? q. (p,q) : (eps A)^* & fin A q & (start A,r) : (eps A)^*)) & \
\       s = True#r)";
br iffI 1;
 bd lemma 1;
 by(Blast_tac 1);
(* Why can't blast_tac do the rest? *)
by (Clarify_tac 1);
be disjE 1;
be True_True_eps_starI 1;
by (Clarify_tac 1);
br rtrancl_trans 1;
be True_True_eps_starI 1;
br rtrancl_trans 1;
br r_into_rtrancl 1;
be True_start_eps_starI 1;
be True_True_eps_starI 1;
qed "True_eps_star";
AddIffs [True_eps_star];

(** True in step Some **)

goalw thy [star_def,step_def]
 "!A. (True#p,r): step (star A) (Some a) = \
\     (? q. (p,q): step A (Some a) & r=True#q)";
by(Simp_tac 1);
by(Blast_tac 1);
qed_spec_mp "True_step_star";
AddIffs [True_step_star];


(** True in steps **)

(* reverse list induction! Complicates matters for conc? *)
goal thy
 "!rr. (True#start A,rr) : steps (star A) w --> \
\ (? us v. w = concat us @ v & \
\             (!u:set us. accepts A u) & \
\             (? r. (start A,r) : steps A v & rr = True#r))";
by(res_inst_tac [("xs","w")] snoc_induct 1);
 by (Asm_full_simp_tac 1);
 by (Clarify_tac 1);
 by(res_inst_tac [("x","[]")] exI 1);
 be disjE 1;
  by (Asm_simp_tac 1);
 by (Clarify_tac 1);
 by (Asm_simp_tac 1);
by(simp_tac (simpset() addsimps [O_assoc,epsclosure_steps]) 1);
by (Clarify_tac 1);
by(etac allE 1 THEN mp_tac 1);
by (Clarify_tac 1);
be disjE 1;
 by(res_inst_tac [("x","us")] exI 1);
 by(res_inst_tac [("x","v@[x]")] exI 1);
 by(asm_simp_tac (simpset() addsimps [O_assoc,epsclosure_steps]) 1);
 by(Blast_tac 1);
by (Clarify_tac 1);
by(res_inst_tac [("x","us@[v@[x]]")] exI 1);
by(res_inst_tac [("x","[]")] exI 1);
by(asm_full_simp_tac (simpset() addsimps [accepts_def]) 1);
by(Blast_tac 1);
qed_spec_mp "True_start_steps_starD";

goal thy "!p. (p,q) : steps A w --> (True#p,True#q) : steps (star A) w";
by(induct_tac "w" 1);
 by(Simp_tac 1);
by(Simp_tac 1);
by(blast_tac (claset() addIs [True_True_eps_starI,True_True_step_starI]) 1);
qed_spec_mp "True_True_steps_starI";

goalw thy [accepts_def]
 "(!u : set us. accepts A u) --> \
\ (True#start A,True#start A) : steps (star A) (concat us)";
by(induct_tac "us" 1);
 by(Simp_tac 1);
by(Simp_tac 1);
by(blast_tac (claset() addIs [True_True_steps_starI,True_start_eps_starI,r_into_rtrancl,in_epsclosure_steps]) 1);
qed_spec_mp "steps_star_cycle";

(* Better stated directly with start(star A)? Loop in star A back to start(star A)?*)
goal thy
 "(True#start A,rr) : steps (star A) w = \
\ (? us v. w = concat us @ v & \
\             (!u:set us. accepts A u) & \
\             (? r. (start A,r) : steps A v & rr = True#r))";
br iffI 1;
 be True_start_steps_starD 1;
by (Clarify_tac 1);
by(Asm_simp_tac 1);
by(blast_tac (claset() addIs [True_True_steps_starI,steps_star_cycle]) 1);
qed "True_start_steps_star";

(** the start state **)

goalw thy [star_def,step_def]
  "!A. (start(star A),r) : step (star A) a = (a=None & r = True#start A)";
by(Simp_tac 1);
qed_spec_mp "start_step_star";
AddIffs [start_step_star];

val epsclosure_start_step_star =
  read_instantiate [("p","start(star A)")] in_unfold_rtrancl2;

goal thy
 "(start(star A),r) : steps (star A) w = \
\ ((w=[] & r= start(star A)) | (True#start A,r) : steps (star A) w)";
br iffI 1;
 by(exhaust_tac "w" 1);
  by(asm_full_simp_tac (simpset() addsimps
    [epsclosure_start_step_star]) 1);
 by(Asm_full_simp_tac 1);
 by (Clarify_tac 1);
 by(asm_full_simp_tac (simpset() addsimps
    [epsclosure_start_step_star]) 1);
 by(Blast_tac 1);
be disjE 1;
 by(Asm_simp_tac 1);
by(blast_tac (claset() addIs [in_steps_epsclosure,r_into_rtrancl]) 1);
qed "start_steps_star";

goalw thy [star_def] "!A. fin (star A) (True#p) = fin A p";
by(Simp_tac 1);
qed_spec_mp "fin_star_True";
AddIffs [fin_star_True];

goalw thy [star_def] "!A. fin (star A) (start(star A))";
by(Simp_tac 1);
qed_spec_mp "fin_star_start";
AddIffs [fin_star_start];

(* too complex! Simpler if loop back to start(star A)? *)
goalw thy [accepts_def]
 "accepts (star A) w = \
\ (? us. (!u : set(us). accepts A u) & (w = concat us) )";
by(simp_tac (simpset() addsimps [start_steps_star,True_start_steps_star]) 1);
br iffI 1;
 by (Clarify_tac 1);
 be disjE 1;
  by (Clarify_tac 1);
  by(Simp_tac 1);
  by(res_inst_tac [("x","[]")] exI 1);
  by(Simp_tac 1);
 by (Clarify_tac 1);
 by(res_inst_tac [("x","us@[v]")] exI 1);
 by(asm_full_simp_tac (simpset() addsimps [accepts_def]) 1);
 by(Blast_tac 1);
by (Clarify_tac 1);
by(res_inst_tac [("xs","us")] snoc_exhaust 1);
 by(Asm_simp_tac 1);
 by(Blast_tac 1);
by (Clarify_tac 1);
by(asm_full_simp_tac (simpset() addsimps [accepts_def]) 1);
by(Blast_tac 1);
qed "accepts_star";


(***** Correctness of r2n *****)

goal thy
 "!w. w:(lang r) = accepts (r2n r) w";
by(induct_tac "r" 1);
    by(simp_tac (simpset() addsimps [accepts_def]) 1);
   by(simp_tac(simpset() addsimps
       [accepts_def,start_fin_in_steps_atom,fin_atom]) 1);
  (* 3. Fall: Union *)
  by (asm_simp_tac (simpset() addsimps [final_union]) 1);
  (* 4. Fall: Concat *)
 by (asm_simp_tac (simpset() addsimps
     [accepts_def,True_steps_conc,final_conc,start_conc,RegSet.conc_def]) 1);
 by(Blast_tac 1);
by (asm_simp_tac (simpset() addsimps [in_star,accepts_star]) 1);
qed "Rexp_Automata";

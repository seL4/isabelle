(*  Title:      HOL/Lex/RegExp2NA.ML
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

Goalw [atom_def,step_def]
 "(p,q) : step (atom a) b = (p=[True] & q=[False] & b=a)";
by (Simp_tac 1);
qed "in_step_atom_Some";
Addsimps [in_step_atom_Some];

Goal
 "([False],[False]) : steps (atom a) w = (w = [])";
by (induct_tac "w" 1);
 by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [rel_comp_def]) 1);
qed "False_False_in_steps_atom";

Goal
 "(start (atom a), [False]) : steps (atom a) w = (w = [a])";
by (induct_tac "w" 1);
 by (asm_simp_tac (simpset() addsimps [start_atom]) 1);
by (asm_full_simp_tac (simpset()
     addsimps [False_False_in_steps_atom,rel_comp_def,start_atom]) 1);
qed "start_fin_in_steps_atom";

Goal
 "accepts (atom a) w = (w = [a])";
by (simp_tac(simpset() addsimps
       [accepts_conv_steps,start_fin_in_steps_atom,fin_atom]) 1);
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


(***** True/False ueber steps anheben *****)

Goal
 "!p. (True#p,q):steps (or L R) w = (? r. q = True # r & (p,r):steps L w)";
by (induct_tac "w" 1);
by (ALLGOALS Force_tac);
qed_spec_mp "lift_True_over_steps_or";

Goal 
 "!p. (False#p,q):steps (or L R) w = (? r. q = False#r & (p,r):steps R w)";
by (induct_tac "w" 1);
by (ALLGOALS Force_tac);
qed_spec_mp "lift_False_over_steps_or";

AddIffs [lift_True_over_steps_or,lift_False_over_steps_or];


(** From the start  **)

Goalw [or_def,step_def]
 "!L R. (start(or L R),q) : step(or L R) a = \
\       (? p. (q = True#p & (start L,p) : step L a) | \
\             (q = False#p & (start R,p) : step R a))";
by (Simp_tac 1);
by (Blast_tac 1);
qed_spec_mp "start_step_or";
AddIffs [start_step_or];

Goal
 "(start(or L R), q) : steps (or L R) w = \
\ ( (w = [] & q = start(or L R)) | \
\   (w ~= [] & (? p.  q = True  # p & (start L,p) : steps L w | \
\                     q = False # p & (start R,p) : steps R w)))";
by (case_tac "w" 1);
 by (Asm_simp_tac 1);
 by (Blast_tac 1);
by (Asm_simp_tac 1);
by (Blast_tac 1);
qed "steps_or";

Goalw [or_def]
 "!L R. fin (or L R) (start(or L R)) = \
\       (fin L (start L) | fin R (start R))";
by (Simp_tac 1);
qed_spec_mp "fin_start_or";
AddIffs [fin_start_or];

Goal
 "accepts (or L R) w = (accepts L w | accepts R w)";
by (simp_tac (simpset() addsimps [accepts_conv_steps,steps_or]) 1);
(* get rid of case_tac: *)
by (case_tac "w = []" 1);
by (Auto_tac);
qed "accepts_or";
AddIffs [accepts_or];

(******************************************************)
(*                      conc                        *)
(******************************************************)

(** True/False in fin **)

Goalw [conc_def]
 "!L R. fin (conc L R) (True#p) = (fin L p & fin R (start R))";
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
\        (fin L p & (? r. q=False#r & (start R,r) : step R a)))";
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

(** False in steps **)

Goal
 "!p. (False#p,q): steps (conc L R) w = (? r. q=False#r & (p,r): steps R w)";
by (induct_tac "w" 1);
by (ALLGOALS Force_tac);
qed_spec_mp "False_steps_conc";
AddIffs [False_steps_conc];

(** True in steps **)

Goal
 "!!L R. !p. (p,q) : steps L w --> (True#p,True#q) : steps (conc L R) w";
by (induct_tac "w" 1);
 by (Simp_tac 1);
by (Simp_tac 1);
by (Blast_tac 1);
qed_spec_mp "True_True_steps_concI";

Goal
 "!L R. (True#p,False#q) : step (conc L R) a = \
\       (fin L p & (start R,q) : step R a)";
by (Simp_tac 1);
qed "True_False_step_conc";
AddIffs [True_False_step_conc];

Goal
 "!p. (True#p,q) : steps (conc L R) w --> \
\     ((? r. (p,r) : steps L w & q = True#r)  | \
\  (? u a v. w = u@a#v & \
\            (? r. (p,r) : steps L u & fin L r & \
\            (? s. (start R,s) : step R a & \
\            (? t. (s,t) : steps R v & q = False#t)))))";
by (induct_tac "w" 1);
 by (Simp_tac 1);
by (Simp_tac 1);
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
\  (? u a v. w = u@a#v & \
\            (? r. (p,r) : steps L u & fin L r & \
\            (? s. (start R,s) : step R a & \
\            (? t. (s,t) : steps R v & q = False#t)))))";
by (force_tac (claset() addDs [True_steps_concD]
     addIs [True_True_steps_concI],simpset()) 1);
qed "True_steps_conc";

(** starting from the start **)

Goalw [conc_def]
  "!L R. start(conc L R) = True#start L";
by (Simp_tac 1);
qed_spec_mp "start_conc";

Goalw [conc_def]
 "!L R. fin(conc L R) p = ((fin R (start R) & (? s. p = True#s & fin L s)) | \
\                          (? s. p = False#s & fin R s))";
by (simp_tac (simpset() addsplits [list.split]) 1);
by (Blast_tac 1);
qed_spec_mp "final_conc";

Goal
 "accepts (conc L R) w = (? u v. w = u@v & accepts L u & accepts R v)";
by (simp_tac (simpset() addsimps
     [accepts_conv_steps,True_steps_conc,final_conc,start_conc]) 1);
by (rtac iffI 1);
 by (Clarify_tac 1);
 by (etac disjE 1);
  by (Clarify_tac 1);
  by (etac disjE 1);
   by (res_inst_tac [("x","w")] exI 1);
   by (Simp_tac 1);
   by (Blast_tac 1);
  by (Blast_tac 1);
 by (etac disjE 1);
  by (Blast_tac 1);
 by (Clarify_tac 1);
 by (res_inst_tac [("x","u")] exI 1);
 by (Simp_tac 1);
 by (Blast_tac 1);
by (Clarify_tac 1);
by (case_tac "v" 1);
 by (Asm_full_simp_tac 1);
 by (Blast_tac 1);
by (Asm_full_simp_tac 1);
by (Blast_tac 1);
qed "accepts_conc";

(******************************************************)
(*                     epsilon                        *)
(******************************************************)

Goalw [epsilon_def,step_def] "step epsilon a = {}";
by (Simp_tac 1);
qed "step_epsilon";
Addsimps [step_epsilon];

Goal "((p,q) : steps epsilon w) = (w=[] & p=q)";
by (induct_tac "w" 1);
by (Auto_tac);
qed "steps_epsilon";

Goal "accepts epsilon w = (w = [])";
by (simp_tac (simpset() addsimps [steps_epsilon,accepts_conv_steps]) 1);
by (simp_tac (simpset() addsimps [epsilon_def]) 1);
qed "accepts_epsilon";
AddIffs [accepts_epsilon];

(******************************************************)
(*                       plus                         *)
(******************************************************)

Goalw [plus_def] "!A. start (plus A) = start A";
by (Simp_tac 1);
qed_spec_mp "start_plus";
Addsimps [start_plus];

Goalw [plus_def] "!A. fin (plus A) = fin A";
by (Simp_tac 1);
qed_spec_mp "fin_plus";
AddIffs [fin_plus];

Goalw [plus_def,step_def]
  "!A. (p,q) : step A a --> (p,q) : step (plus A) a";
by (Simp_tac 1);
qed_spec_mp "step_plusI";

Goal "!p. (p,q) : steps A w --> (p,q) : steps (plus A) w";
by (induct_tac "w" 1);
 by (Simp_tac 1);
by (Simp_tac 1);
by (blast_tac (claset() addIs [step_plusI]) 1);
qed_spec_mp "steps_plusI";

Goalw [plus_def,step_def]
 "!A. (p,r): step (plus A) a = \
\     ( (p,r): step A a | fin A p & (start A,r) : step A a )";
by (Simp_tac 1);
qed_spec_mp "step_plus_conv";
AddIffs [step_plus_conv];

Goal
 "[| (start A,q) : steps A u; u ~= []; fin A p |] \
\ ==> (p,q) : steps (plus A) u";
by (case_tac "u" 1);
 by (Blast_tac 1);
by (Asm_full_simp_tac 1);
by (blast_tac (claset() addIs [steps_plusI]) 1);
qed "fin_steps_plusI";

(* reverse list induction! Complicates matters for conc? *)
Goal
 "!r. (start A,r) : steps (plus A) w --> \
\     (? us v. w = concat us @ v & \
\              (!u:set us. accepts A u) & \
\              (start A,r) : steps A v)";
by (res_inst_tac [("xs","w")] rev_induct 1);
 by (Simp_tac 1);
 by (res_inst_tac [("x","[]")] exI 1);
 by (Simp_tac 1);
by (Simp_tac 1);
by (Clarify_tac 1);
by (etac allE 1 THEN mp_tac 1);
by (Clarify_tac 1);
by (etac disjE 1);
 by (res_inst_tac [("x","us")] exI 1);
 by (Asm_simp_tac 1);
 by (Blast_tac 1);
by (res_inst_tac [("x","us@[v]")] exI 1);
by (asm_full_simp_tac (simpset() addsimps [accepts_conv_steps]) 1);
by (Blast_tac 1);
qed_spec_mp "start_steps_plusD";

Goal
 "us ~= [] --> (!u : set us. accepts A u) --> accepts (plus A) (concat us)";
by (simp_tac (simpset() addsimps [accepts_conv_steps]) 1);
by (res_inst_tac [("xs","us")] rev_induct 1);
 by (Simp_tac 1);
by (rename_tac "u us" 1);
by (Simp_tac 1);
by (Clarify_tac 1);
by (case_tac "us = []" 1);
 by (Asm_full_simp_tac 1);
 by (blast_tac (claset() addIs [steps_plusI,fin_steps_plusI]) 1);
by (Clarify_tac 1);
by (case_tac "u = []" 1);
 by (Asm_full_simp_tac 1);
 by (blast_tac (claset() addIs [steps_plusI,fin_steps_plusI]) 1);
by (Asm_full_simp_tac 1);
by (blast_tac (claset() addIs [steps_plusI,fin_steps_plusI]) 1);
qed_spec_mp "steps_star_cycle";

Goal
 "accepts (plus A) w = \
\ (? us. us ~= [] & w = concat us & (!u : set us. accepts A u))";
by (rtac iffI 1);
 by (asm_full_simp_tac (simpset() addsimps [accepts_conv_steps]) 1);
 by (Clarify_tac 1);
 by (dtac start_steps_plusD 1);
 by (Clarify_tac 1);
 by (res_inst_tac [("x","us@[v]")] exI 1);
 by (asm_full_simp_tac (simpset() addsimps [accepts_conv_steps]) 1);
 by (Blast_tac 1);
by (blast_tac (claset() addIs [steps_star_cycle]) 1);
qed "accepts_plus";
AddIffs [accepts_plus];

(******************************************************)
(*                       star                         *)
(******************************************************)

Goalw [star_def]
"accepts (star A) w = \
\ (? us. (!u : set us. accepts A u) & w = concat us)";
by (rtac iffI 1);
 by (Clarify_tac 1);
 by (etac disjE 1);
  by (res_inst_tac [("x","[]")] exI 1);
  by (Simp_tac 1);
  by (Blast_tac 1);
 by (Blast_tac 1);
by (Force_tac 1);
qed "accepts_star";

(***** Correctness of r2n *****)

Goal
 "!w. accepts (rexp2na r) w = (w : lang r)";
by (induct_tac "r" 1);
    by (simp_tac (simpset() addsimps [accepts_conv_steps]) 1);
   by (simp_tac(simpset() addsimps [accepts_atom]) 1);
  by (Asm_simp_tac 1);
 by (asm_simp_tac (simpset() addsimps [accepts_conc,RegSet.conc_def]) 1);
by (asm_simp_tac (simpset() addsimps [accepts_star,in_star]) 1);
qed_spec_mp "accepts_rexp2na";

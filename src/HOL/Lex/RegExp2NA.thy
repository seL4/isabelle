(*  Title:      HOL/Lex/RegExp2NA.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM

Conversion of regular expressions *directly*
into nondeterministic automata *without* epsilon transitions
*)

theory RegExp2NA = RegExp + NA:

types 'a bitsNA = "('a,bool list)na"

syntax "##" :: "'a => 'a list set => 'a list set" (infixr 65)
translations "x ## S" == "Cons x ` S"

constdefs
 atom  :: "'a => 'a bitsNA"
"atom a == ([True],
            %b s. if s=[True] & b=a then {[False]} else {},
            %s. s=[False])"

 or :: "'a bitsNA => 'a bitsNA => 'a bitsNA"
"or == %(ql,dl,fl)(qr,dr,fr).
   ([],
    %a s. case s of
            [] => (True ## dl a ql) Un (False ## dr a qr)
          | left#s => if left then True ## dl a s
                              else False ## dr a s,
    %s. case s of [] => (fl ql | fr qr)
                | left#s => if left then fl s else fr s)"

 conc :: "'a bitsNA => 'a bitsNA => 'a bitsNA"
"conc == %(ql,dl,fl)(qr,dr,fr).
   (True#ql,
    %a s. case s of
            [] => {}
          | left#s => if left then (True ## dl a s) Un
                                   (if fl s then False ## dr a qr else {})
                              else False ## dr a s,
    %s. case s of [] => False | left#s => left & fl s & fr qr | ~left & fr s)"

 epsilon :: "'a bitsNA"
"epsilon == ([],%a s. {}, %s. s=[])"

 plus :: "'a bitsNA => 'a bitsNA"
"plus == %(q,d,f). (q, %a s. d a s Un (if f s then d a q else {}), f)"

 star :: "'a bitsNA => 'a bitsNA"
"star A == or epsilon (plus A)"

consts rexp2na :: "'a rexp => 'a bitsNA"
primrec
"rexp2na Empty      = ([], %a s. {}, %s. False)"
"rexp2na(Atom a)    = atom a"
"rexp2na(Or r s)    = or   (rexp2na r) (rexp2na s)"
"rexp2na(Conc r s)  = conc (rexp2na r) (rexp2na s)"
"rexp2na(Star r)    = star (rexp2na r)"

declare split_paired_all[simp]

(******************************************************)
(*                       atom                         *)
(******************************************************)

lemma fin_atom: "(fin (atom a) q) = (q = [False])"
by(simp add:atom_def)

lemma start_atom: "start (atom a) = [True]"
by(simp add:atom_def)

lemma in_step_atom_Some[simp]:
 "(p,q) : step (atom a) b = (p=[True] & q=[False] & b=a)"
by (simp add: atom_def step_def)

lemma False_False_in_steps_atom:
 "([False],[False]) : steps (atom a) w = (w = [])"
apply (induct "w")
 apply simp
apply (simp add: rel_comp_def)
done

lemma start_fin_in_steps_atom:
 "(start (atom a), [False]) : steps (atom a) w = (w = [a])"
apply (induct "w")
 apply (simp add: start_atom)
apply (simp add: False_False_in_steps_atom rel_comp_def start_atom)
done

lemma accepts_atom:
 "accepts (atom a) w = (w = [a])"
by (simp add: accepts_conv_steps start_fin_in_steps_atom fin_atom)

(******************************************************)
(*                      or                            *)
(******************************************************)

(***** lift True/False over fin *****)

lemma fin_or_True[iff]:
 "!!L R. fin (or L R) (True#p) = fin L p"
by(simp add:or_def)

lemma fin_or_False[iff]:
 "!!L R. fin (or L R) (False#p) = fin R p"
by(simp add:or_def)

(***** lift True/False over step *****)

lemma True_in_step_or[iff]:
"!!L R. (True#p,q) : step (or L R) a = (? r. q = True#r & (p,r) : step L a)"
apply (simp add:or_def step_def)
apply blast
done

lemma False_in_step_or[iff]:
"!!L R. (False#p,q) : step (or L R) a = (? r. q = False#r & (p,r) : step R a)"
apply (simp add:or_def step_def)
apply blast
done


(***** lift True/False over steps *****)

lemma lift_True_over_steps_or[iff]:
 "!!p. (True#p,q):steps (or L R) w = (? r. q = True # r & (p,r):steps L w)"
apply (induct "w")
 apply force
apply force
done

lemma lift_False_over_steps_or[iff]:
 "!!p. (False#p,q):steps (or L R) w = (? r. q = False#r & (p,r):steps R w)"
apply (induct "w")
 apply force
apply force
done

(** From the start  **)

lemma start_step_or[iff]:
 "!!L R. (start(or L R),q) : step(or L R) a = 
         (? p. (q = True#p & (start L,p) : step L a) | 
               (q = False#p & (start R,p) : step R a))"
apply (simp add:or_def step_def)
apply blast
done

lemma steps_or:
 "(start(or L R), q) : steps (or L R) w = 
  ( (w = [] & q = start(or L R)) | 
    (w ~= [] & (? p.  q = True  # p & (start L,p) : steps L w | 
                      q = False # p & (start R,p) : steps R w)))"
apply (case_tac "w")
 apply (simp)
 apply blast
apply (simp)
apply blast
done

lemma fin_start_or[iff]:
 "!!L R. fin (or L R) (start(or L R)) = (fin L (start L) | fin R (start R))"
by (simp add:or_def)

lemma accepts_or[iff]:
 "accepts (or L R) w = (accepts L w | accepts R w)"
apply (simp add: accepts_conv_steps steps_or)
(* get rid of case_tac: *)
apply (case_tac "w = []")
 apply auto
done

(******************************************************)
(*                      conc                        *)
(******************************************************)

(** True/False in fin **)

lemma fin_conc_True[iff]:
 "!!L R. fin (conc L R) (True#p) = (fin L p & fin R (start R))"
by(simp add:conc_def)

lemma fin_conc_False[iff]:
 "!!L R. fin (conc L R) (False#p) = fin R p"
by(simp add:conc_def)


(** True/False in step **)

lemma True_step_conc[iff]:
 "!!L R. (True#p,q) : step (conc L R) a = 
        ((? r. q=True#r & (p,r): step L a) | 
         (fin L p & (? r. q=False#r & (start R,r) : step R a)))"
apply (simp add:conc_def step_def)
apply blast
done

lemma False_step_conc[iff]:
 "!!L R. (False#p,q) : step (conc L R) a = 
       (? r. q = False#r & (p,r) : step R a)"
apply (simp add:conc_def step_def)
apply blast
done

(** False in steps **)

lemma False_steps_conc[iff]:
 "!!p. (False#p,q): steps (conc L R) w = (? r. q=False#r & (p,r): steps R w)"
apply (induct "w")
 apply fastsimp
apply force
done

(** True in steps **)

lemma True_True_steps_concI:
 "!!L R p. (p,q) : steps L w ==> (True#p,True#q) : steps (conc L R) w"
apply (induct "w")
 apply simp
apply simp
apply fast
done

lemma True_False_step_conc[iff]:
 "!!L R. (True#p,False#q) : step (conc L R) a = 
         (fin L p & (start R,q) : step R a)"
by simp

lemma True_steps_concD[rule_format]:
 "!p. (True#p,q) : steps (conc L R) w --> 
     ((? r. (p,r) : steps L w & q = True#r)  | 
  (? u a v. w = u@a#v & 
            (? r. (p,r) : steps L u & fin L r & 
            (? s. (start R,s) : step R a & 
            (? t. (s,t) : steps R v & q = False#t)))))"
apply (induct "w")
 apply simp
apply simp
apply (clarify del:disjCI)
apply (erule disjE)
 apply (clarify del:disjCI)
 apply (erule allE, erule impE, assumption)
 apply (erule disjE)
  apply blast
 apply (rule disjI2)
 apply (clarify)
 apply simp
 apply (rule_tac x = "a#u" in exI)
 apply simp
 apply blast
apply (rule disjI2)
apply (clarify)
apply simp
apply (rule_tac x = "[]" in exI)
apply simp
apply blast
done

lemma True_steps_conc:
 "(True#p,q) : steps (conc L R) w = 
 ((? r. (p,r) : steps L w & q = True#r)  | 
  (? u a v. w = u@a#v & 
            (? r. (p,r) : steps L u & fin L r & 
            (? s. (start R,s) : step R a & 
            (? t. (s,t) : steps R v & q = False#t)))))"
by(force dest!: True_steps_concD intro!: True_True_steps_concI)

(** starting from the start **)

lemma start_conc:
  "!!L R. start(conc L R) = True#start L"
by (simp add:conc_def)

lemma final_conc:
 "!!L R. fin(conc L R) p = ((fin R (start R) & (? s. p = True#s & fin L s)) | 
                           (? s. p = False#s & fin R s))"
apply (simp add:conc_def split: list.split)
apply blast
done

lemma accepts_conc:
 "accepts (conc L R) w = (? u v. w = u@v & accepts L u & accepts R v)"
apply (simp add: accepts_conv_steps True_steps_conc final_conc start_conc)
apply (rule iffI)
 apply (clarify)
 apply (erule disjE)
  apply (clarify)
  apply (erule disjE)
   apply (rule_tac x = "w" in exI)
   apply simp
   apply blast
  apply blast
 apply (erule disjE)
  apply blast
 apply (clarify)
 apply (rule_tac x = "u" in exI)
 apply simp
 apply blast
apply (clarify)
apply (case_tac "v")
 apply simp
 apply blast
apply simp
apply blast
done

(******************************************************)
(*                     epsilon                        *)
(******************************************************)

lemma step_epsilon[simp]: "step epsilon a = {}"
by(simp add:epsilon_def step_def)

lemma steps_epsilon: "((p,q) : steps epsilon w) = (w=[] & p=q)"
by (induct "w") auto

lemma accepts_epsilon[iff]: "accepts epsilon w = (w = [])"
apply (simp add: steps_epsilon accepts_conv_steps)
apply (simp add: epsilon_def)
done

(******************************************************)
(*                       plus                         *)
(******************************************************)

lemma start_plus[simp]: "!!A. start (plus A) = start A"
by(simp add:plus_def)

lemma fin_plus[iff]: "!!A. fin (plus A) = fin A"
by(simp add:plus_def)

lemma step_plusI:
  "!!A. (p,q) : step A a ==> (p,q) : step (plus A) a"
by(simp add:plus_def step_def)

lemma steps_plusI: "!!p. (p,q) : steps A w ==> (p,q) : steps (plus A) w"
apply (induct "w")
 apply simp
apply simp
apply (blast intro: step_plusI)
done

lemma step_plus_conv[iff]:
 "!!A. (p,r): step (plus A) a = 
       ( (p,r): step A a | fin A p & (start A,r) : step A a )"
by(simp add:plus_def step_def)

lemma fin_steps_plusI:
 "[| (start A,q) : steps A u; u ~= []; fin A p |] 
 ==> (p,q) : steps (plus A) u"
apply (case_tac "u")
 apply blast
apply simp
apply (blast intro: steps_plusI)
done

(* reverse list induction! Complicates matters for conc? *)
lemma start_steps_plusD[rule_format]:
 "!r. (start A,r) : steps (plus A) w --> 
     (? us v. w = concat us @ v & 
              (!u:set us. accepts A u) & 
              (start A,r) : steps A v)"
apply (induct w rule: rev_induct)
 apply simp
 apply (rule_tac x = "[]" in exI)
 apply simp
apply simp
apply (clarify)
apply (erule allE, erule impE, assumption)
apply (clarify)
apply (erule disjE)
 apply (rule_tac x = "us" in exI)
 apply (simp)
 apply blast
apply (rule_tac x = "us@[v]" in exI)
apply (simp add: accepts_conv_steps)
apply blast
done

lemma steps_star_cycle[rule_format]:
 "us ~= [] --> (!u : set us. accepts A u) --> accepts (plus A) (concat us)"
apply (simp add: accepts_conv_steps)
apply (induct us rule: rev_induct)
 apply simp
apply (rename_tac u us)
apply simp
apply (clarify)
apply (case_tac "us = []")
 apply (simp)
 apply (blast intro: steps_plusI fin_steps_plusI)
apply (clarify)
apply (case_tac "u = []")
 apply (simp)
 apply (blast intro: steps_plusI fin_steps_plusI)
apply (blast intro: steps_plusI fin_steps_plusI)
done

lemma accepts_plus[iff]:
 "accepts (plus A) w = 
 (? us. us ~= [] & w = concat us & (!u : set us. accepts A u))"
apply (rule iffI)
 apply (simp add: accepts_conv_steps)
 apply (clarify)
 apply (drule start_steps_plusD)
 apply (clarify)
 apply (rule_tac x = "us@[v]" in exI)
 apply (simp add: accepts_conv_steps)
 apply blast
apply (blast intro: steps_star_cycle)
done

(******************************************************)
(*                       star                         *)
(******************************************************)

lemma accepts_star:
 "accepts (star A) w = (? us. (!u : set us. accepts A u) & w = concat us)"
apply(unfold star_def)
apply (rule iffI)
 apply (clarify)
 apply (erule disjE)
  apply (rule_tac x = "[]" in exI)
  apply simp
 apply blast
apply force
done

(***** Correctness of r2n *****)

lemma accepts_rexp2na:
 "!!w. accepts (rexp2na r) w = (w : lang r)"
apply (induct "r")
    apply (simp add: accepts_conv_steps)
   apply (simp add: accepts_atom)
  apply (simp)
 apply (simp add: accepts_conc RegSet.conc_def)
apply (simp add: accepts_star in_star)
done

end

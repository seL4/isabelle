(*  Title:      ZF/Resid/Redex.thy
    Author:     Ole Rasmussen, University of Cambridge
*)

theory Redex imports ZF begin
consts
  redexes     :: i

datatype
  "redexes" = Var ("n \<in> nat")            
            | Fun ("t \<in> redexes")
            | App ("b \<in> bool","f \<in> redexes", "a \<in> redexes")


consts
  Ssub  :: "i"
  Scomp :: "i"
  Sreg  :: "i"

abbreviation
  Ssub_rel  (infixl "\<Longleftarrow>" 70) where
  "a \<Longleftarrow> b == <a,b> \<in> Ssub"

abbreviation
  Scomp_rel  (infixl "\<sim>" 70) where
  "a \<sim> b == <a,b> \<in> Scomp"

abbreviation
  "regular(a) == a \<in> Sreg"

consts union_aux        :: "i=>i"
primrec (*explicit lambda is required because both arguments of "\<squnion>" vary*)
  "union_aux(Var(n)) =
     (\<lambda>t \<in> redexes. redexes_case(%j. Var(n), %x. 0, %b x y.0, t))"

  "union_aux(Fun(u)) =
     (\<lambda>t \<in> redexes. redexes_case(%j. 0, %y. Fun(union_aux(u)`y),
                                  %b y z. 0, t))"

  "union_aux(App(b,f,a)) =
     (\<lambda>t \<in> redexes.
        redexes_case(%j. 0, %y. 0,
                     %c z u. App(b or c, union_aux(f)`z, union_aux(a)`u), t))"

definition
  union  (infixl "\<squnion>" 70) where
  "u \<squnion> v == union_aux(u)`v"


inductive
  domains       "Ssub" \<subseteq> "redexes*redexes"
  intros
    Sub_Var:     "n \<in> nat ==> Var(n) \<Longleftarrow> Var(n)"
    Sub_Fun:     "[|u \<Longleftarrow> v|]==> Fun(u) \<Longleftarrow> Fun(v)"
    Sub_App1:    "[|u1 \<Longleftarrow> v1; u2 \<Longleftarrow> v2; b \<in> bool|]==>   
                     App(0,u1,u2) \<Longleftarrow> App(b,v1,v2)"
    Sub_App2:    "[|u1 \<Longleftarrow> v1; u2 \<Longleftarrow> v2|]==> App(1,u1,u2) \<Longleftarrow> App(1,v1,v2)"
  type_intros    redexes.intros bool_typechecks

inductive
  domains       "Scomp" \<subseteq> "redexes*redexes"
  intros
    Comp_Var:    "n \<in> nat ==> Var(n) \<sim> Var(n)"
    Comp_Fun:    "[|u \<sim> v|]==> Fun(u) \<sim> Fun(v)"
    Comp_App:    "[|u1 \<sim> v1; u2 \<sim> v2; b1 \<in> bool; b2 \<in> bool|]
                  ==> App(b1,u1,u2) \<sim> App(b2,v1,v2)"
  type_intros    redexes.intros bool_typechecks

inductive
  domains       "Sreg" \<subseteq> redexes
  intros
    Reg_Var:     "n \<in> nat ==> regular(Var(n))"
    Reg_Fun:     "[|regular(u)|]==> regular(Fun(u))"
    Reg_App1:    "[|regular(Fun(u)); regular(v) |]==>regular(App(1,Fun(u),v))"
    Reg_App2:    "[|regular(u); regular(v) |]==>regular(App(0,u,v))"
  type_intros    redexes.intros bool_typechecks


declare redexes.intros [simp]

(* ------------------------------------------------------------------------- *)
(*    Specialisation of comp-rules                                           *)
(* ------------------------------------------------------------------------- *)

lemmas compD1 [simp] = Scomp.dom_subset [THEN subsetD, THEN SigmaD1]
lemmas compD2 [simp] = Scomp.dom_subset [THEN subsetD, THEN SigmaD2]
lemmas regD [simp] = Sreg.dom_subset [THEN subsetD]

(* ------------------------------------------------------------------------- *)
(*    Equality rules for union                                               *)
(* ------------------------------------------------------------------------- *)

lemma union_Var [simp]: "n \<in> nat ==> Var(n) \<squnion> Var(n)=Var(n)"
by (simp add: union_def)

lemma union_Fun [simp]: "v \<in> redexes ==> Fun(u) \<squnion> Fun(v) = Fun(u \<squnion> v)"
by (simp add: union_def)
 
lemma union_App [simp]:
     "[|b2 \<in> bool; u2 \<in> redexes; v2 \<in> redexes|]
      ==> App(b1,u1,v1) \<squnion> App(b2,u2,v2)=App(b1 or b2,u1 \<squnion> u2,v1 \<squnion> v2)"
by (simp add: union_def)


lemma or_1_right [simp]: "a or 1 = 1"
by (simp add: or_def cond_def) 

lemma or_0_right [simp]: "a \<in> bool \<Longrightarrow> a or 0 = a"
by (simp add: or_def cond_def bool_def, auto) 



declare Ssub.intros [simp]
declare bool_typechecks [simp]
declare Sreg.intros [simp]
declare Scomp.intros [simp]

declare Scomp.intros [intro]

inductive_cases [elim!]:
  "regular(App(b,f,a))"
  "regular(Fun(b))"
  "regular(Var(b))"
  "Fun(u) \<sim> Fun(t)"
  "u \<sim> Fun(t)"
  "u \<sim> Var(n)"
  "u \<sim> App(b,t,a)"
  "Fun(t) \<sim> v"
  "App(b,f,a) \<sim> v"
  "Var(n) \<sim> u"



(* ------------------------------------------------------------------------- *)
(*    comp proofs                                                            *)
(* ------------------------------------------------------------------------- *)

lemma comp_refl [simp]: "u \<in> redexes ==> u \<sim> u"
by (erule redexes.induct, blast+)

lemma comp_sym: "u \<sim> v ==> v \<sim> u"
by (erule Scomp.induct, blast+)

lemma comp_sym_iff: "u \<sim> v \<longleftrightarrow> v \<sim> u"
by (blast intro: comp_sym)

lemma comp_trans [rule_format]: "u \<sim> v ==> \<forall>w. v \<sim> w\<longrightarrow>u \<sim> w"
by (erule Scomp.induct, blast+)

(* ------------------------------------------------------------------------- *)
(*   union proofs                                                            *)
(* ------------------------------------------------------------------------- *)

lemma union_l: "u \<sim> v \<Longrightarrow> u \<Longleftarrow> (u \<squnion> v)"
apply (erule Scomp.induct)
apply (erule_tac [3] boolE, simp_all)
done

lemma union_r: "u \<sim> v \<Longrightarrow> v \<Longleftarrow> (u \<squnion> v)"
apply (erule Scomp.induct)
apply (erule_tac [3] c = b2 in boolE, simp_all)
done

lemma union_sym: "u \<sim> v \<Longrightarrow> u \<squnion> v = v \<squnion> u"
by (erule Scomp.induct, simp_all add: or_commute)

(* ------------------------------------------------------------------------- *)
(*      regular proofs                                                       *)
(* ------------------------------------------------------------------------- *)

lemma union_preserve_regular [rule_format]:
     "u \<sim> v \<Longrightarrow> regular(u) \<longrightarrow> regular(v) \<longrightarrow> regular(u \<squnion> v)"
  by (erule Scomp.induct, auto)

end


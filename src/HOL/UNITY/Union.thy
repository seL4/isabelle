(*  Title:      HOL/UNITY/Union.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Partly from Misra's Chapter 5: Asynchronous Compositions of Programs
*)

header{*Unions of Programs*}

theory Union = SubstAx + FP:

constdefs

  (*FIXME: conjoin Init F Int Init G ~= {} *) 
  ok :: "['a program, 'a program] => bool"      (infixl "ok" 65)
    "F ok G == Acts F <= AllowedActs G &
               Acts G <= AllowedActs F"

  (*FIXME: conjoin (INT i:I. Init (F i)) ~= {} *) 
  OK  :: "['a set, 'a => 'b program] => bool"
    "OK I F == (ALL i:I. ALL j: I-{i}. Acts (F i) <= AllowedActs (F j))"

  JOIN  :: "['a set, 'a => 'b program] => 'b program"
    "JOIN I F == mk_program (INT i:I. Init (F i), UN i:I. Acts (F i),
			     INT i:I. AllowedActs (F i))"

  Join :: "['a program, 'a program] => 'a program"      (infixl "Join" 65)
    "F Join G == mk_program (Init F Int Init G, Acts F Un Acts G,
			     AllowedActs F Int AllowedActs G)"

  SKIP :: "'a program"
    "SKIP == mk_program (UNIV, {}, UNIV)"

  (*Characterizes safety properties.  Used with specifying AllowedActs*)
  safety_prop :: "'a program set => bool"
    "safety_prop X == SKIP: X & (ALL G. Acts G <= UNION X Acts --> G : X)"

syntax
  "@JOIN1"     :: "[pttrns, 'b set] => 'b set"         ("(3JN _./ _)" 10)
  "@JOIN"      :: "[pttrn, 'a set, 'b set] => 'b set"  ("(3JN _:_./ _)" 10)

translations
  "JN x:A. B"   == "JOIN A (%x. B)"
  "JN x y. B"   == "JN x. JN y. B"
  "JN x. B"     == "JOIN UNIV (%x. B)"

syntax (xsymbols)
  SKIP      :: "'a program"                              ("\<bottom>")
  "op Join" :: "['a program, 'a program] => 'a program"  (infixl "\<squnion>" 65)
  "@JOIN1"  :: "[pttrns, 'b set] => 'b set"              ("(3\<Squnion> _./ _)" 10)
  "@JOIN"   :: "[pttrn, 'a set, 'b set] => 'b set"       ("(3\<Squnion> _:_./ _)" 10)


subsection{*SKIP*}

lemma Init_SKIP [simp]: "Init SKIP = UNIV"
by (simp add: SKIP_def)

lemma Acts_SKIP [simp]: "Acts SKIP = {Id}"
by (simp add: SKIP_def)

lemma AllowedActs_SKIP [simp]: "AllowedActs SKIP = UNIV"
by (auto simp add: SKIP_def)

lemma reachable_SKIP [simp]: "reachable SKIP = UNIV"
by (force elim: reachable.induct intro: reachable.intros)

subsection{*SKIP and safety properties*}

lemma SKIP_in_constrains_iff [iff]: "(SKIP : A co B) = (A<=B)"
by (unfold constrains_def, auto)

lemma SKIP_in_Constrains_iff [iff]: "(SKIP : A Co B) = (A<=B)"
by (unfold Constrains_def, auto)

lemma SKIP_in_stable [iff]: "SKIP : stable A"
by (unfold stable_def, auto)

declare SKIP_in_stable [THEN stable_imp_Stable, iff]


subsection{*Join*}

lemma Init_Join [simp]: "Init (F Join G) = Init F Int Init G"
by (simp add: Join_def)

lemma Acts_Join [simp]: "Acts (F Join G) = Acts F Un Acts G"
by (auto simp add: Join_def)

lemma AllowedActs_Join [simp]:
     "AllowedActs (F Join G) = AllowedActs F Int AllowedActs G"
by (auto simp add: Join_def)


subsection{*JN*}

lemma JN_empty [simp]: "(JN i:{}. F i) = SKIP"
by (unfold JOIN_def SKIP_def, auto)

lemma JN_insert [simp]: "(JN i:insert a I. F i) = (F a) Join (JN i:I. F i)"
apply (rule program_equalityI)
apply (auto simp add: JOIN_def Join_def)
done

lemma Init_JN [simp]: "Init (JN i:I. F i) = (INT i:I. Init (F i))"
by (simp add: JOIN_def)

lemma Acts_JN [simp]: "Acts (JN i:I. F i) = insert Id (UN i:I. Acts (F i))"
by (auto simp add: JOIN_def)

lemma AllowedActs_JN [simp]:
     "AllowedActs (JN i:I. F i) = (INT i:I. AllowedActs (F i))"
by (auto simp add: JOIN_def)


lemma JN_cong [cong]: 
    "[| I=J;  !!i. i:J ==> F i = G i |] ==> (JN i:I. F i) = (JN i:J. G i)"
by (simp add: JOIN_def)


subsection{*Algebraic laws*}

lemma Join_commute: "F Join G = G Join F"
by (simp add: Join_def Un_commute Int_commute)

lemma Join_assoc: "(F Join G) Join H = F Join (G Join H)"
by (simp add: Un_ac Join_def Int_assoc insert_absorb)
 
lemma Join_left_commute: "A Join (B Join C) = B Join (A Join C)"
by (simp add: Un_ac Int_ac Join_def insert_absorb)

lemma Join_SKIP_left [simp]: "SKIP Join F = F"
apply (unfold Join_def SKIP_def)
apply (rule program_equalityI)
apply (simp_all (no_asm) add: insert_absorb)
done

lemma Join_SKIP_right [simp]: "F Join SKIP = F"
apply (unfold Join_def SKIP_def)
apply (rule program_equalityI)
apply (simp_all (no_asm) add: insert_absorb)
done

lemma Join_absorb [simp]: "F Join F = F"
apply (unfold Join_def)
apply (rule program_equalityI, auto)
done

lemma Join_left_absorb: "F Join (F Join G) = F Join G"
apply (unfold Join_def)
apply (rule program_equalityI, auto)
done

(*Join is an AC-operator*)
lemmas Join_ac = Join_assoc Join_left_absorb Join_commute Join_left_commute


subsection{*JN laws*}

(*Also follows by JN_insert and insert_absorb, but the proof is longer*)
lemma JN_absorb: "k:I ==> F k Join (JN i:I. F i) = (JN i:I. F i)"
by (auto intro!: program_equalityI)

lemma JN_Un: "(JN i: I Un J. F i) = ((JN i: I. F i) Join (JN i:J. F i))"
by (auto intro!: program_equalityI)

lemma JN_constant: "(JN i:I. c) = (if I={} then SKIP else c)"
by (rule program_equalityI, auto)

lemma JN_Join_distrib:
     "(JN i:I. F i Join G i) = (JN i:I. F i)  Join  (JN i:I. G i)"
by (auto intro!: program_equalityI)

lemma JN_Join_miniscope:
     "i : I ==> (JN i:I. F i Join G) = ((JN i:I. F i) Join G)"
by (auto simp add: JN_Join_distrib JN_constant)

(*Used to prove guarantees_JN_I*)
lemma JN_Join_diff: "i: I ==> F i Join JOIN (I - {i}) F = JOIN I F"
apply (unfold JOIN_def Join_def)
apply (rule program_equalityI, auto)
done


subsection{*Safety: co, stable, FP*}

(*Fails if I={} because it collapses to SKIP : A co B, i.e. to A<=B.  So an
  alternative precondition is A<=B, but most proofs using this rule require
  I to be nonempty for other reasons anyway.*)
lemma JN_constrains: 
    "i : I ==> (JN i:I. F i) : A co B = (ALL i:I. F i : A co B)"
by (simp add: constrains_def JOIN_def, blast)

lemma Join_constrains [simp]:
     "(F Join G : A co B) = (F : A co B & G : A co B)"
by (auto simp add: constrains_def Join_def)

lemma Join_unless [simp]:
     "(F Join G : A unless B) = (F : A unless B & G : A unless B)"
by (simp add: Join_constrains unless_def)

(*Analogous weak versions FAIL; see Misra [1994] 5.4.1, Substitution Axiom.
  reachable (F Join G) could be much bigger than reachable F, reachable G
*)


lemma Join_constrains_weaken:
     "[| F : A co A';  G : B co B' |]  
      ==> F Join G : (A Int B) co (A' Un B')"
by (simp, blast intro: constrains_weaken)

(*If I={}, it degenerates to SKIP : UNIV co {}, which is false.*)
lemma JN_constrains_weaken:
     "[| ALL i:I. F i : A i co A' i;  i: I |]  
      ==> (JN i:I. F i) : (INT i:I. A i) co (UN i:I. A' i)"
apply (simp (no_asm_simp) add: JN_constrains)
apply (blast intro: constrains_weaken)
done

lemma JN_stable: "(JN i:I. F i) : stable A = (ALL i:I. F i : stable A)"
by (simp add: stable_def constrains_def JOIN_def)

lemma invariant_JN_I:
     "[| !!i. i:I ==> F i : invariant A;  i : I |]   
       ==> (JN i:I. F i) : invariant A"
by (simp add: invariant_def JN_stable, blast)

lemma Join_stable [simp]:
     "(F Join G : stable A) =  
      (F : stable A & G : stable A)"
by (simp add: stable_def)

lemma Join_increasing [simp]:
     "(F Join G : increasing f) =  
      (F : increasing f & G : increasing f)"
by (simp add: increasing_def Join_stable, blast)

lemma invariant_JoinI:
     "[| F : invariant A; G : invariant A |]   
      ==> F Join G : invariant A"
by (simp add: invariant_def, blast)

lemma FP_JN: "FP (JN i:I. F i) = (INT i:I. FP (F i))"
by (simp add: FP_def JN_stable INTER_def)


subsection{*Progress: transient, ensures*}

lemma JN_transient:
     "i : I ==>  
    (JN i:I. F i) : transient A = (EX i:I. F i : transient A)"
by (auto simp add: transient_def JOIN_def)

lemma Join_transient [simp]:
     "F Join G : transient A =  
      (F : transient A | G : transient A)"
by (auto simp add: bex_Un transient_def Join_def)

lemma Join_transient_I1: "F : transient A ==> F Join G : transient A"
by (simp add: Join_transient)

lemma Join_transient_I2: "G : transient A ==> F Join G : transient A"
by (simp add: Join_transient)

(*If I={} it degenerates to (SKIP : A ensures B) = False, i.e. to ~(A<=B) *)
lemma JN_ensures:
     "i : I ==>  
      (JN i:I. F i) : A ensures B =  
      ((ALL i:I. F i : (A-B) co (A Un B)) & (EX i:I. F i : A ensures B))"
by (auto simp add: ensures_def JN_constrains JN_transient)

lemma Join_ensures: 
     "F Join G : A ensures B =      
      (F : (A-B) co (A Un B) & G : (A-B) co (A Un B) &  
       (F : transient (A-B) | G : transient (A-B)))"
by (auto simp add: ensures_def Join_transient)

lemma stable_Join_constrains: 
    "[| F : stable A;  G : A co A' |]  
     ==> F Join G : A co A'"
apply (unfold stable_def constrains_def Join_def)
apply (simp add: ball_Un, blast)
done

(*Premise for G cannot use Always because  F: Stable A  is weaker than
  G : stable A *)
lemma stable_Join_Always1:
     "[| F : stable A;  G : invariant A |] ==> F Join G : Always A"
apply (simp (no_asm_use) add: Always_def invariant_def Stable_eq_stable)
apply (force intro: stable_Int)
done

(*As above, but exchanging the roles of F and G*)
lemma stable_Join_Always2:
     "[| F : invariant A;  G : stable A |] ==> F Join G : Always A"
apply (subst Join_commute)
apply (blast intro: stable_Join_Always1)
done

lemma stable_Join_ensures1:
     "[| F : stable A;  G : A ensures B |] ==> F Join G : A ensures B"
apply (simp (no_asm_simp) add: Join_ensures)
apply (simp add: stable_def ensures_def)
apply (erule constrains_weaken, auto)
done

(*As above, but exchanging the roles of F and G*)
lemma stable_Join_ensures2:
     "[| F : A ensures B;  G : stable A |] ==> F Join G : A ensures B"
apply (subst Join_commute)
apply (blast intro: stable_Join_ensures1)
done


subsection{*the ok and OK relations*}

lemma ok_SKIP1 [iff]: "SKIP ok F"
by (auto simp add: ok_def)

lemma ok_SKIP2 [iff]: "F ok SKIP"
by (auto simp add: ok_def)

lemma ok_Join_commute:
     "(F ok G & (F Join G) ok H) = (G ok H & F ok (G Join H))"
by (auto simp add: ok_def)

lemma ok_commute: "(F ok G) = (G ok F)"
by (auto simp add: ok_def)

lemmas ok_sym = ok_commute [THEN iffD1, standard]

lemma ok_iff_OK:
     "OK {(0::int,F),(1,G),(2,H)} snd = (F ok G & (F Join G) ok H)"
by (simp add: Ball_def conj_disj_distribR ok_def Join_def OK_def insert_absorb all_conj_distrib eq_commute, blast)

lemma ok_Join_iff1 [iff]: "F ok (G Join H) = (F ok G & F ok H)"
by (auto simp add: ok_def)

lemma ok_Join_iff2 [iff]: "(G Join H) ok F = (G ok F & H ok F)"
by (auto simp add: ok_def)

(*useful?  Not with the previous two around*)
lemma ok_Join_commute_I: "[| F ok G; (F Join G) ok H |] ==> F ok (G Join H)"
by (auto simp add: ok_def)

lemma ok_JN_iff1 [iff]: "F ok (JOIN I G) = (ALL i:I. F ok G i)"
by (auto simp add: ok_def)

lemma ok_JN_iff2 [iff]: "(JOIN I G) ok F =  (ALL i:I. G i ok F)"
by (auto simp add: ok_def)

lemma OK_iff_ok: "OK I F = (ALL i: I. ALL j: I-{i}. (F i) ok (F j))"
by (auto simp add: ok_def OK_def)

lemma OK_imp_ok: "[| OK I F; i: I; j: I; i ~= j|] ==> (F i) ok (F j)"
by (auto simp add: OK_iff_ok)


subsection{*Allowed*}

lemma Allowed_SKIP [simp]: "Allowed SKIP = UNIV"
by (auto simp add: Allowed_def)

lemma Allowed_Join [simp]: "Allowed (F Join G) = Allowed F Int Allowed G"
by (auto simp add: Allowed_def)

lemma Allowed_JN [simp]: "Allowed (JOIN I F) = (INT i:I. Allowed (F i))"
by (auto simp add: Allowed_def)

lemma ok_iff_Allowed: "F ok G = (F : Allowed G & G : Allowed F)"
by (simp add: ok_def Allowed_def)

lemma OK_iff_Allowed: "OK I F = (ALL i: I. ALL j: I-{i}. F i : Allowed(F j))"
by (auto simp add: OK_iff_ok ok_iff_Allowed)

subsection{*@{text safety_prop}, for reasoning about
 given instances of "ok"*}

lemma safety_prop_Acts_iff:
     "safety_prop X ==> (Acts G <= insert Id (UNION X Acts)) = (G : X)"
by (auto simp add: safety_prop_def)

lemma safety_prop_AllowedActs_iff_Allowed:
     "safety_prop X ==> (UNION X Acts <= AllowedActs F) = (X <= Allowed F)"
by (auto simp add: Allowed_def safety_prop_Acts_iff [symmetric])

lemma Allowed_eq:
     "safety_prop X ==> Allowed (mk_program (init, acts, UNION X Acts)) = X"
by (simp add: Allowed_def safety_prop_Acts_iff)

lemma def_prg_Allowed:
     "[| F == mk_program (init, acts, UNION X Acts) ; safety_prop X |]  
      ==> Allowed F = X"
by (simp add: Allowed_eq)

(*For safety_prop to hold, the property must be satisfiable!*)
lemma safety_prop_constrains [iff]: "safety_prop (A co B) = (A <= B)"
by (simp add: safety_prop_def constrains_def, blast)

lemma safety_prop_stable [iff]: "safety_prop (stable A)"
by (simp add: stable_def)

lemma safety_prop_Int [simp]:
     "[| safety_prop X; safety_prop Y |] ==> safety_prop (X Int Y)"
by (simp add: safety_prop_def, blast)

lemma safety_prop_INTER1 [simp]:
     "(!!i. safety_prop (X i)) ==> safety_prop (INT i. X i)"
by (auto simp add: safety_prop_def, blast)
							       
lemma safety_prop_INTER [simp]:
     "(!!i. i:I ==> safety_prop (X i)) ==> safety_prop (INT i:I. X i)"
by (auto simp add: safety_prop_def, blast)

lemma def_UNION_ok_iff:
     "[| F == mk_program(init,acts,UNION X Acts); safety_prop X |]  
      ==> F ok G = (G : X & acts <= AllowedActs G)"
by (auto simp add: ok_def safety_prop_Acts_iff)

end

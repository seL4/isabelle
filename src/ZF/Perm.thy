(*  Title:      ZF/Perm.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

The theory underlying permutation groups
  -- Composition of relations, the identity relation
  -- Injections, surjections, bijections
  -- Lemmas for the Schroeder-Bernstein Theorem
*)

header{*Injections, Surjections, Bijections, Composition*}

theory Perm imports func begin

definition
  (*composition of relations and functions; NOT Suppes's relative product*)
  comp     :: "[i,i]=>i"      (infixr "O" 60)  where
    "r O s == {xz : domain(s)*range(r) . 
               EX x y z. xz=<x,z> & <x,y>:s & <y,z>:r}"

definition
  (*the identity function for A*)
  id    :: "i=>i"  where
    "id(A) == (lam x:A. x)"

definition
  (*one-to-one functions from A to B*)
  inj   :: "[i,i]=>i"  where
    "inj(A,B) == { f: A->B. ALL w:A. ALL x:A. f`w=f`x --> w=x}"

definition
  (*onto functions from A to B*)
  surj  :: "[i,i]=>i"  where
    "surj(A,B) == { f: A->B . ALL y:B. EX x:A. f`x=y}"

definition
  (*one-to-one and onto functions*)
  bij   :: "[i,i]=>i"  where
    "bij(A,B) == inj(A,B) Int surj(A,B)"


subsection{*Surjective Function Space*}

lemma surj_is_fun: "f: surj(A,B) ==> f: A->B"
apply (unfold surj_def)
apply (erule CollectD1)
done

lemma fun_is_surj: "f : Pi(A,B) ==> f: surj(A,range(f))"
apply (unfold surj_def)
apply (blast intro: apply_equality range_of_fun domain_type)
done

lemma surj_range: "f: surj(A,B) ==> range(f)=B"
apply (unfold surj_def)
apply (best intro: apply_Pair elim: range_type)
done

text{* A function with a right inverse is a surjection *}

lemma f_imp_surjective: 
    "[| f: A->B;  !!y. y:B ==> d(y): A;  !!y. y:B ==> f`d(y) = y |]
     ==> f: surj(A,B)"
  by (simp add: surj_def, blast)

lemma lam_surjective: 
    "[| !!x. x:A ==> c(x): B;            
        !!y. y:B ==> d(y): A;            
        !!y. y:B ==> c(d(y)) = y         
     |] ==> (lam x:A. c(x)) : surj(A,B)"
apply (rule_tac d = d in f_imp_surjective) 
apply (simp_all add: lam_type)
done

text{*Cantor's theorem revisited*}
lemma cantor_surj: "f ~: surj(A,Pow(A))"
apply (unfold surj_def, safe)
apply (cut_tac cantor)
apply (best del: subsetI) 
done


subsection{*Injective Function Space*}

lemma inj_is_fun: "f: inj(A,B) ==> f: A->B"
apply (unfold inj_def)
apply (erule CollectD1)
done

text{*Good for dealing with sets of pairs, but a bit ugly in use [used in AC]*}
lemma inj_equality: 
    "[| <a,b>:f;  <c,b>:f;  f: inj(A,B) |] ==> a=c"
apply (unfold inj_def)
apply (blast dest: Pair_mem_PiD)
done

lemma inj_apply_equality: "[| f:inj(A,B);  f`a=f`b;  a:A;  b:A |] ==> a=b"
by (unfold inj_def, blast)

text{* A function with a left inverse is an injection *}

lemma f_imp_injective: "[| f: A->B;  ALL x:A. d(f`x)=x |] ==> f: inj(A,B)"
apply (simp (no_asm_simp) add: inj_def)
apply (blast intro: subst_context [THEN box_equals])
done

lemma lam_injective: 
    "[| !!x. x:A ==> c(x): B;            
        !!x. x:A ==> d(c(x)) = x |]
     ==> (lam x:A. c(x)) : inj(A,B)"
apply (rule_tac d = d in f_imp_injective)
apply (simp_all add: lam_type)
done

subsection{*Bijections*}

lemma bij_is_inj: "f: bij(A,B) ==> f: inj(A,B)"
apply (unfold bij_def)
apply (erule IntD1)
done

lemma bij_is_surj: "f: bij(A,B) ==> f: surj(A,B)"
apply (unfold bij_def)
apply (erule IntD2)
done

text{* f: bij(A,B) ==> f: A->B *}
lemmas bij_is_fun = bij_is_inj [THEN inj_is_fun]

lemma lam_bijective: 
    "[| !!x. x:A ==> c(x): B;            
        !!y. y:B ==> d(y): A;            
        !!x. x:A ==> d(c(x)) = x;        
        !!y. y:B ==> c(d(y)) = y         
     |] ==> (lam x:A. c(x)) : bij(A,B)"
apply (unfold bij_def)
apply (blast intro!: lam_injective lam_surjective)
done

lemma RepFun_bijective: "(ALL y : x. EX! y'. f(y') = f(y))   
      ==> (lam z:{f(y). y:x}. THE y. f(y) = z) : bij({f(y). y:x}, x)"
apply (rule_tac d = f in lam_bijective)
apply (auto simp add: the_equality2)
done


subsection{*Identity Function*}

lemma idI [intro!]: "a:A ==> <a,a> : id(A)"
apply (unfold id_def)
apply (erule lamI)
done

lemma idE [elim!]: "[| p: id(A);  !!x.[| x:A; p=<x,x> |] ==> P |] ==>  P"
by (simp add: id_def lam_def, blast)

lemma id_type: "id(A) : A->A"
apply (unfold id_def)
apply (rule lam_type, assumption)
done

lemma id_conv [simp]: "x:A ==> id(A)`x = x"
apply (unfold id_def)
apply (simp (no_asm_simp))
done

lemma id_mono: "A<=B ==> id(A) <= id(B)"
apply (unfold id_def)
apply (erule lam_mono)
done

lemma id_subset_inj: "A<=B ==> id(A): inj(A,B)"
apply (simp add: inj_def id_def)
apply (blast intro: lam_type) 
done

lemmas id_inj = subset_refl [THEN id_subset_inj]

lemma id_surj: "id(A): surj(A,A)"
apply (unfold id_def surj_def)
apply (simp (no_asm_simp))
done

lemma id_bij: "id(A): bij(A,A)"
apply (unfold bij_def)
apply (blast intro: id_inj id_surj)
done

lemma subset_iff_id: "A <= B <-> id(A) : A->B"
apply (unfold id_def)
apply (force intro!: lam_type dest: apply_type)
done

text{*@{term id} as the identity relation*}
lemma id_iff [simp]: "<x,y> \<in> id(A) <-> x=y & y \<in> A"
by auto


subsection{*Converse of a Function*}

lemma inj_converse_fun: "f: inj(A,B) ==> converse(f) : range(f)->A"
apply (unfold inj_def)
apply (simp (no_asm_simp) add: Pi_iff function_def)
apply (erule CollectE)
apply (simp (no_asm_simp) add: apply_iff)
apply (blast dest: fun_is_rel)
done

text{* Equations for converse(f) *}

text{*The premises are equivalent to saying that f is injective...*}
lemma left_inverse_lemma:
     "[| f: A->B;  converse(f): C->A;  a: A |] ==> converse(f)`(f`a) = a"
by (blast intro: apply_Pair apply_equality converseI)

lemma left_inverse [simp]: "[| f: inj(A,B);  a: A |] ==> converse(f)`(f`a) = a"
by (blast intro: left_inverse_lemma inj_converse_fun inj_is_fun)

lemma left_inverse_eq:
     "[|f \<in> inj(A,B); f ` x = y; x \<in> A|] ==> converse(f) ` y = x"
by auto

lemmas left_inverse_bij = bij_is_inj [THEN left_inverse]

lemma right_inverse_lemma:
     "[| f: A->B;  converse(f): C->A;  b: C |] ==> f`(converse(f)`b) = b"
by (rule apply_Pair [THEN converseD [THEN apply_equality]], auto) 

(*Should the premises be f:surj(A,B), b:B for symmetry with left_inverse?
  No: they would not imply that converse(f) was a function! *)
lemma right_inverse [simp]:
     "[| f: inj(A,B);  b: range(f) |] ==> f`(converse(f)`b) = b"
by (blast intro: right_inverse_lemma inj_converse_fun inj_is_fun)

lemma right_inverse_bij: "[| f: bij(A,B);  b: B |] ==> f`(converse(f)`b) = b"
by (force simp add: bij_def surj_range)

subsection{*Converses of Injections, Surjections, Bijections*}

lemma inj_converse_inj: "f: inj(A,B) ==> converse(f): inj(range(f), A)"
apply (rule f_imp_injective)
apply (erule inj_converse_fun, clarify) 
apply (rule right_inverse)
 apply assumption
apply blast 
done

lemma inj_converse_surj: "f: inj(A,B) ==> converse(f): surj(range(f), A)"
by (blast intro: f_imp_surjective inj_converse_fun left_inverse inj_is_fun 
                 range_of_fun [THEN apply_type])

text{*Adding this as an intro! rule seems to cause looping*}
lemma bij_converse_bij [TC]: "f: bij(A,B) ==> converse(f): bij(B,A)"
apply (unfold bij_def)
apply (fast elim: surj_range [THEN subst] inj_converse_inj inj_converse_surj)
done



subsection{*Composition of Two Relations*}

text{*The inductive definition package could derive these theorems for @term{r O s}*}

lemma compI [intro]: "[| <a,b>:s; <b,c>:r |] ==> <a,c> : r O s"
by (unfold comp_def, blast)

lemma compE [elim!]: 
    "[| xz : r O s;   
        !!x y z. [| xz=<x,z>;  <x,y>:s;  <y,z>:r |] ==> P |]
     ==> P"
by (unfold comp_def, blast)

lemma compEpair: 
    "[| <a,c> : r O s;   
        !!y. [| <a,y>:s;  <y,c>:r |] ==> P |]
     ==> P"
by (erule compE, simp)  

lemma converse_comp: "converse(R O S) = converse(S) O converse(R)"
by blast


subsection{*Domain and Range -- see Suppes, Section 3.1*}

text{*Boyer et al., Set Theory in First-Order Logic, JAR 2 (1986), 287-327*}
lemma range_comp: "range(r O s) <= range(r)"
by blast

lemma range_comp_eq: "domain(r) <= range(s) ==> range(r O s) = range(r)"
by (rule range_comp [THEN equalityI], blast)

lemma domain_comp: "domain(r O s) <= domain(s)"
by blast

lemma domain_comp_eq: "range(s) <= domain(r) ==> domain(r O s) = domain(s)"
by (rule domain_comp [THEN equalityI], blast)

lemma image_comp: "(r O s)``A = r``(s``A)"
by blast

lemma inj_inj_range: "f: inj(A,B) ==> f : inj(A,range(f))"
  by (auto simp add: inj_def Pi_iff function_def)

lemma inj_bij_range: "f: inj(A,B) ==> f : bij(A,range(f))"
  by (auto simp add: bij_def intro: inj_inj_range inj_is_fun fun_is_surj) 


subsection{*Other Results*}

lemma comp_mono: "[| r'<=r; s'<=s |] ==> (r' O s') <= (r O s)"
by blast

text{*composition preserves relations*}
lemma comp_rel: "[| s<=A*B;  r<=B*C |] ==> (r O s) <= A*C"
by blast

text{*associative law for composition*}
lemma comp_assoc: "(r O s) O t = r O (s O t)"
by blast

(*left identity of composition; provable inclusions are
        id(A) O r <= r       
  and   [| r<=A*B; B<=C |] ==> r <= id(C) O r *)
lemma left_comp_id: "r<=A*B ==> id(B) O r = r"
by blast

(*right identity of composition; provable inclusions are
        r O id(A) <= r
  and   [| r<=A*B; A<=C |] ==> r <= r O id(C) *)
lemma right_comp_id: "r<=A*B ==> r O id(A) = r"
by blast


subsection{*Composition Preserves Functions, Injections, and Surjections*}

lemma comp_function: "[| function(g);  function(f) |] ==> function(f O g)"
by (unfold function_def, blast)

text{*Don't think the premises can be weakened much*}
lemma comp_fun: "[| g: A->B;  f: B->C |] ==> (f O g) : A->C"
apply (auto simp add: Pi_def comp_function Pow_iff comp_rel)
apply (subst range_rel_subset [THEN domain_comp_eq], auto) 
done

(*Thanks to the new definition of "apply", the premise f: B->C is gone!*)
lemma comp_fun_apply [simp]:
     "[| g: A->B;  a:A |] ==> (f O g)`a = f`(g`a)"
apply (frule apply_Pair, assumption) 
apply (simp add: apply_def image_comp)
apply (blast dest: apply_equality) 
done

text{*Simplifies compositions of lambda-abstractions*}
lemma comp_lam: 
    "[| !!x. x:A ==> b(x): B |]
     ==> (lam y:B. c(y)) O (lam x:A. b(x)) = (lam x:A. c(b(x)))"
apply (subgoal_tac "(lam x:A. b(x)) : A -> B") 
 apply (rule fun_extension)
   apply (blast intro: comp_fun lam_funtype)
  apply (rule lam_funtype)
 apply simp 
apply (simp add: lam_type) 
done

lemma comp_inj:
     "[| g: inj(A,B);  f: inj(B,C) |] ==> (f O g) : inj(A,C)"
apply (frule inj_is_fun [of g]) 
apply (frule inj_is_fun [of f]) 
apply (rule_tac d = "%y. converse (g) ` (converse (f) ` y)" in f_imp_injective)
 apply (blast intro: comp_fun, simp)  
done

lemma comp_surj: 
    "[| g: surj(A,B);  f: surj(B,C) |] ==> (f O g) : surj(A,C)"
apply (unfold surj_def)
apply (blast intro!: comp_fun comp_fun_apply)
done

lemma comp_bij: 
    "[| g: bij(A,B);  f: bij(B,C) |] ==> (f O g) : bij(A,C)"
apply (unfold bij_def)
apply (blast intro: comp_inj comp_surj)
done


subsection{*Dual Properties of @{term inj} and @{term surj}*}

text{*Useful for proofs from
    D Pastre.  Automatic theorem proving in set theory. 
    Artificial Intelligence, 10:1--27, 1978.*}

lemma comp_mem_injD1: 
    "[| (f O g): inj(A,C);  g: A->B;  f: B->C |] ==> g: inj(A,B)"
by (unfold inj_def, force) 

lemma comp_mem_injD2: 
    "[| (f O g): inj(A,C);  g: surj(A,B);  f: B->C |] ==> f: inj(B,C)"
apply (unfold inj_def surj_def, safe)
apply (rule_tac x1 = x in bspec [THEN bexE])
apply (erule_tac [3] x1 = w in bspec [THEN bexE], assumption+, safe)
apply (rule_tac t = "op ` (g) " in subst_context)
apply (erule asm_rl bspec [THEN bspec, THEN mp])+
apply (simp (no_asm_simp))
done

lemma comp_mem_surjD1: 
    "[| (f O g): surj(A,C);  g: A->B;  f: B->C |] ==> f: surj(B,C)"
apply (unfold surj_def)
apply (blast intro!: comp_fun_apply [symmetric] apply_funtype)
done


lemma comp_mem_surjD2: 
    "[| (f O g): surj(A,C);  g: A->B;  f: inj(B,C) |] ==> g: surj(A,B)"
apply (unfold inj_def surj_def, safe)
apply (drule_tac x = "f`y" in bspec, auto)  
apply (blast intro: apply_funtype)
done

subsubsection{*Inverses of Composition*}

text{*left inverse of composition; one inclusion is
        @term{f: A->B ==> id(A) <= converse(f) O f} *}
lemma left_comp_inverse: "f: inj(A,B) ==> converse(f) O f = id(A)"
apply (unfold inj_def, clarify) 
apply (rule equalityI) 
 apply (auto simp add: apply_iff, blast)  
done

text{*right inverse of composition; one inclusion is
                @term{f: A->B ==> f O converse(f) <= id(B)} *}
lemma right_comp_inverse: 
    "f: surj(A,B) ==> f O converse(f) = id(B)"
apply (simp add: surj_def, clarify) 
apply (rule equalityI)
apply (best elim: domain_type range_type dest: apply_equality2)
apply (blast intro: apply_Pair)
done


subsubsection{*Proving that a Function is a Bijection*}

lemma comp_eq_id_iff: 
    "[| f: A->B;  g: B->A |] ==> f O g = id(B) <-> (ALL y:B. f`(g`y)=y)"
apply (unfold id_def, safe)
 apply (drule_tac t = "%h. h`y " in subst_context)
 apply simp
apply (rule fun_extension)
  apply (blast intro: comp_fun lam_type)
 apply auto
done

lemma fg_imp_bijective: 
    "[| f: A->B;  g: B->A;  f O g = id(B);  g O f = id(A) |] ==> f : bij(A,B)"
apply (unfold bij_def)
apply (simp add: comp_eq_id_iff)
apply (blast intro: f_imp_injective f_imp_surjective apply_funtype)
done

lemma nilpotent_imp_bijective: "[| f: A->A;  f O f = id(A) |] ==> f : bij(A,A)"
by (blast intro: fg_imp_bijective)

lemma invertible_imp_bijective:
     "[| converse(f): B->A;  f: A->B |] ==> f : bij(A,B)"
by (simp add: fg_imp_bijective comp_eq_id_iff 
              left_inverse_lemma right_inverse_lemma)

subsubsection{*Unions of Functions*}

text{*See similar theorems in func.thy*}

text{*Theorem by KG, proof by LCP*}
lemma inj_disjoint_Un:
     "[| f: inj(A,B);  g: inj(C,D);  B Int D = 0 |]  
      ==> (lam a: A Un C. if a:A then f`a else g`a) : inj(A Un C, B Un D)"
apply (rule_tac d = "%z. if z:B then converse (f) `z else converse (g) `z" 
       in lam_injective)
apply (auto simp add: inj_is_fun [THEN apply_type])
done

lemma surj_disjoint_Un: 
    "[| f: surj(A,B);  g: surj(C,D);  A Int C = 0 |]   
     ==> (f Un g) : surj(A Un C, B Un D)"
apply (simp add: surj_def fun_disjoint_Un) 
apply (blast dest!: domain_of_fun 
             intro!: fun_disjoint_apply1 fun_disjoint_apply2)
done

text{*A simple, high-level proof; the version for injections follows from it,
  using  @term{f:inj(A,B) <-> f:bij(A,range(f))}  *}
lemma bij_disjoint_Un:
     "[| f: bij(A,B);  g: bij(C,D);  A Int C = 0;  B Int D = 0 |]  
      ==> (f Un g) : bij(A Un C, B Un D)"
apply (rule invertible_imp_bijective)
apply (subst converse_Un)
apply (auto intro: fun_disjoint_Un bij_is_fun bij_converse_bij)
done


subsubsection{*Restrictions as Surjections and Bijections*}

lemma surj_image:
    "f: Pi(A,B) ==> f: surj(A, f``A)"
apply (simp add: surj_def) 
apply (blast intro: apply_equality apply_Pair Pi_type) 
done

lemma restrict_image [simp]: "restrict(f,A) `` B = f `` (A Int B)"
by (auto simp add: restrict_def)

lemma restrict_inj: 
    "[| f: inj(A,B);  C<=A |] ==> restrict(f,C): inj(C,B)"
apply (unfold inj_def)
apply (safe elim!: restrict_type2, auto) 
done

lemma restrict_surj: "[| f: Pi(A,B);  C<=A |] ==> restrict(f,C): surj(C, f``C)"
apply (insert restrict_type2 [THEN surj_image])
apply (simp add: restrict_image) 
done

lemma restrict_bij: 
    "[| f: inj(A,B);  C<=A |] ==> restrict(f,C): bij(C, f``C)"
apply (simp add: inj_def bij_def)
apply (blast intro: restrict_surj surj_is_fun)
done


subsubsection{*Lemmas for Ramsey's Theorem*}

lemma inj_weaken_type: "[| f: inj(A,B);  B<=D |] ==> f: inj(A,D)"
apply (unfold inj_def)
apply (blast intro: fun_weaken_type)
done

lemma inj_succ_restrict:
     "[| f: inj(succ(m), A) |] ==> restrict(f,m) : inj(m, A-{f`m})"
apply (rule restrict_bij [THEN bij_is_inj, THEN inj_weaken_type], assumption, blast)
apply (unfold inj_def)
apply (fast elim: range_type mem_irrefl dest: apply_equality)
done


lemma inj_extend: 
    "[| f: inj(A,B);  a~:A;  b~:B |]  
     ==> cons(<a,b>,f) : inj(cons(a,A), cons(b,B))"
apply (unfold inj_def)
apply (force intro: apply_type  simp add: fun_extend)
done

end

(*  Title:      ZF/perm
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

The theory underlying permutation groups
  -- Composition of relations, the identity relation
  -- Injections, surjections, bijections
  -- Lemmas for the Schroeder-Bernstein Theorem
*)

theory Perm = mono + func:

constdefs

  (*composition of relations and functions; NOT Suppes's relative product*)
  comp     :: "[i,i]=>i"      (infixr "O" 60)
    "r O s == {xz : domain(s)*range(r) . 
               EX x y z. xz=<x,z> & <x,y>:s & <y,z>:r}"

  (*the identity function for A*)
  id    :: "i=>i"
    "id(A) == (lam x:A. x)"

  (*one-to-one functions from A to B*)
  inj   :: "[i,i]=>i"
    "inj(A,B) == { f: A->B. ALL w:A. ALL x:A. f`w=f`x --> w=x}"

  (*onto functions from A to B*)
  surj  :: "[i,i]=>i"
    "surj(A,B) == { f: A->B . ALL y:B. EX x:A. f`x=y}"

  (*one-to-one and onto functions*)
  bij   :: "[i,i]=>i"
    "bij(A,B) == inj(A,B) Int surj(A,B)"


(** Surjective function space **)

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

(** A function with a right inverse is a surjection **)

lemma f_imp_surjective: 
    "[| f: A->B;  !!y. y:B ==> d(y): A;  !!y. y:B ==> f`d(y) = y |]
     ==> f: surj(A,B)"
apply (simp add: surj_def, blast)
done

lemma lam_surjective: 
    "[| !!x. x:A ==> c(x): B;            
        !!y. y:B ==> d(y): A;            
        !!y. y:B ==> c(d(y)) = y         
     |] ==> (lam x:A. c(x)) : surj(A,B)"
apply (rule_tac d = "d" in f_imp_surjective) 
apply (simp_all add: lam_type)
done

(*Cantor's theorem revisited*)
lemma cantor_surj: "f ~: surj(A,Pow(A))"
apply (unfold surj_def, safe)
apply (cut_tac cantor)
apply (best del: subsetI) 
done


(** Injective function space **)

lemma inj_is_fun: "f: inj(A,B) ==> f: A->B"
apply (unfold inj_def)
apply (erule CollectD1)
done

(*Good for dealing with sets of pairs, but a bit ugly in use [used in AC]*)
lemma inj_equality: 
    "[| <a,b>:f;  <c,b>:f;  f: inj(A,B) |] ==> a=c"
apply (unfold inj_def)
apply (blast dest: Pair_mem_PiD)
done

lemma inj_apply_equality: "[| f:inj(A,B);  a:A;  b:A;  f`a=f`b |] ==> a=b"
by (unfold inj_def, blast)

(** A function with a left inverse is an injection **)

lemma f_imp_injective: "[| f: A->B;  ALL x:A. d(f`x)=x |] ==> f: inj(A,B)"
apply (simp (no_asm_simp) add: inj_def)
apply (blast intro: subst_context [THEN box_equals])
done

lemma lam_injective: 
    "[| !!x. x:A ==> c(x): B;            
        !!x. x:A ==> d(c(x)) = x |]
     ==> (lam x:A. c(x)) : inj(A,B)"
apply (rule_tac d = "d" in f_imp_injective)
apply (simp_all add: lam_type)
done

(** Bijections **)

lemma bij_is_inj: "f: bij(A,B) ==> f: inj(A,B)"
apply (unfold bij_def)
apply (erule IntD1)
done

lemma bij_is_surj: "f: bij(A,B) ==> f: surj(A,B)"
apply (unfold bij_def)
apply (erule IntD2)
done

(* f: bij(A,B) ==> f: A->B *)
lemmas bij_is_fun = bij_is_inj [THEN inj_is_fun, standard]

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
apply (rule_tac d = "f" in lam_bijective)
apply (auto simp add: the_equality2)
done


(** Identity function **)

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

lemmas id_inj = subset_refl [THEN id_subset_inj, standard]

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


(*** Converse of a function ***)

lemma inj_converse_fun: "f: inj(A,B) ==> converse(f) : range(f)->A"
apply (unfold inj_def)
apply (simp (no_asm_simp) add: Pi_iff function_def)
apply (erule CollectE)
apply (simp (no_asm_simp) add: apply_iff)
apply (blast dest: fun_is_rel)
done

(** Equations for converse(f) **)

(*The premises are equivalent to saying that f is injective...*) 
lemma left_inverse_lemma:
     "[| f: A->B;  converse(f): C->A;  a: A |] ==> converse(f)`(f`a) = a"
by (blast intro: apply_Pair apply_equality converseI)

lemma left_inverse [simp]: "[| f: inj(A,B);  a: A |] ==> converse(f)`(f`a) = a"
by (blast intro: left_inverse_lemma inj_converse_fun inj_is_fun)

lemmas left_inverse_bij = bij_is_inj [THEN left_inverse, standard]

lemma right_inverse_lemma:
     "[| f: A->B;  converse(f): C->A;  b: C |] ==> f`(converse(f)`b) = b"
apply (rule apply_Pair [THEN converseD [THEN apply_equality]], auto) 
done

(*Should the premises be f:surj(A,B), b:B for symmetry with left_inverse?
  No: they would not imply that converse(f) was a function! *)
lemma right_inverse [simp]:
     "[| f: inj(A,B);  b: range(f) |] ==> f`(converse(f)`b) = b"
by (blast intro: right_inverse_lemma inj_converse_fun inj_is_fun)

lemma right_inverse_bij: "[| f: bij(A,B);  b: B |] ==> f`(converse(f)`b) = b"
by (force simp add: bij_def surj_range)

(** Converses of injections, surjections, bijections **)

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

(*Adding this as an intro! rule seems to cause looping*)
lemma bij_converse_bij [TC]: "f: bij(A,B) ==> converse(f): bij(B,A)"
apply (unfold bij_def)
apply (fast elim: surj_range [THEN subst] inj_converse_inj inj_converse_surj)
done



(** Composition of two relations **)

(*The inductive definition package could derive these theorems for (r O s)*)

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


(** Domain and Range -- see Suppes, section 3.1 **)

(*Boyer et al., Set Theory in First-Order Logic, JAR 2 (1986), 287-327*)
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


(** Other results **)

lemma comp_mono: "[| r'<=r; s'<=s |] ==> (r' O s') <= (r O s)"
by blast

(*composition preserves relations*)
lemma comp_rel: "[| s<=A*B;  r<=B*C |] ==> (r O s) <= A*C"
by blast

(*associative law for composition*)
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


(** Composition preserves functions, injections, and surjections **)

lemma comp_function: "[| function(g);  function(f) |] ==> function(f O g)"
by (unfold function_def, blast)

(*Don't think the premises can be weakened much*)
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

(*Simplifies compositions of lambda-abstractions*)
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


(** Dual properties of inj and surj -- useful for proofs from
    D Pastre.  Automatic theorem proving in set theory. 
    Artificial Intelligence, 10:1--27, 1978. **)

lemma comp_mem_injD1: 
    "[| (f O g): inj(A,C);  g: A->B;  f: B->C |] ==> g: inj(A,B)"
apply (unfold inj_def, force) 
done

lemma comp_mem_injD2: 
    "[| (f O g): inj(A,C);  g: surj(A,B);  f: B->C |] ==> f: inj(B,C)"
apply (unfold inj_def surj_def, safe)
apply (rule_tac x1 = "x" in bspec [THEN bexE])
apply (erule_tac [3] x1 = "w" in bspec [THEN bexE], assumption+)
apply safe
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

(** inverses of composition **)

(*left inverse of composition; one inclusion is
        f: A->B ==> id(A) <= converse(f) O f *)
lemma left_comp_inverse: "f: inj(A,B) ==> converse(f) O f = id(A)"
apply (unfold inj_def, clarify) 
apply (rule equalityI) 
 apply (auto simp add: apply_iff, blast)  
done

(*right inverse of composition; one inclusion is
                f: A->B ==> f O converse(f) <= id(B) *)
lemma right_comp_inverse: 
    "f: surj(A,B) ==> f O converse(f) = id(B)"
apply (simp add: surj_def, clarify) 
apply (rule equalityI)
apply (best elim: domain_type range_type dest: apply_equality2)
apply (blast intro: apply_Pair)
done


(** Proving that a function is a bijection **)

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

(** Unions of functions -- cf similar theorems on func.ML **)

(*Theorem by KG, proof by LCP*)
lemma inj_disjoint_Un:
     "[| f: inj(A,B);  g: inj(C,D);  B Int D = 0 |]  
      ==> (lam a: A Un C. if a:A then f`a else g`a) : inj(A Un C, B Un D)"
apply (rule_tac d = "%z. if z:B then converse (f) `z else converse (g) `z" 
       in lam_injective)
apply (auto simp add: inj_is_fun [THEN apply_type])
apply (blast intro: inj_is_fun [THEN apply_type])
done

lemma surj_disjoint_Un: 
    "[| f: surj(A,B);  g: surj(C,D);  A Int C = 0 |]   
     ==> (f Un g) : surj(A Un C, B Un D)"
apply (simp add: surj_def fun_disjoint_Un) 
apply (blast dest!: domain_of_fun 
	     intro!: fun_disjoint_apply1 fun_disjoint_apply2)
done

(*A simple, high-level proof; the version for injections follows from it,
  using  f:inj(A,B) <-> f:bij(A,range(f))  *)
lemma bij_disjoint_Un:
     "[| f: bij(A,B);  g: bij(C,D);  A Int C = 0;  B Int D = 0 |]  
      ==> (f Un g) : bij(A Un C, B Un D)"
apply (rule invertible_imp_bijective)
apply (subst converse_Un)
apply (auto intro: fun_disjoint_Un bij_is_fun bij_converse_bij)
done


(** Restrictions as surjections and bijections *)

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


(*** Lemmas for Ramsey's Theorem ***)

lemma inj_weaken_type: "[| f: inj(A,B);  B<=D |] ==> f: inj(A,D)"
apply (unfold inj_def)
apply (blast intro: fun_weaken_type)
done

lemma inj_succ_restrict:
     "[| f: inj(succ(m), A) |] ==> restrict(f,m) : inj(m, A-{f`m})"
apply (rule restrict_bij [THEN bij_is_inj, THEN inj_weaken_type], assumption)
apply blast
apply (unfold inj_def)
apply (fast elim: range_type mem_irrefl dest: apply_equality)
done


lemma inj_extend: 
    "[| f: inj(A,B);  a~:A;  b~:B |]  
     ==> cons(<a,b>,f) : inj(cons(a,A), cons(b,B))"
apply (unfold inj_def)
apply (force intro: apply_type  simp add: fun_extend)
done


ML
{*
val comp_def = thm "comp_def";
val id_def = thm "id_def";
val inj_def = thm "inj_def";
val surj_def = thm "surj_def";
val bij_def = thm "bij_def";

val surj_is_fun = thm "surj_is_fun";
val fun_is_surj = thm "fun_is_surj";
val surj_range = thm "surj_range";
val f_imp_surjective = thm "f_imp_surjective";
val lam_surjective = thm "lam_surjective";
val cantor_surj = thm "cantor_surj";
val inj_is_fun = thm "inj_is_fun";
val inj_equality = thm "inj_equality";
val inj_apply_equality = thm "inj_apply_equality";
val f_imp_injective = thm "f_imp_injective";
val lam_injective = thm "lam_injective";
val bij_is_inj = thm "bij_is_inj";
val bij_is_surj = thm "bij_is_surj";
val bij_is_fun = thm "bij_is_fun";
val lam_bijective = thm "lam_bijective";
val RepFun_bijective = thm "RepFun_bijective";
val idI = thm "idI";
val idE = thm "idE";
val id_type = thm "id_type";
val id_conv = thm "id_conv";
val id_mono = thm "id_mono";
val id_subset_inj = thm "id_subset_inj";
val id_inj = thm "id_inj";
val id_surj = thm "id_surj";
val id_bij = thm "id_bij";
val subset_iff_id = thm "subset_iff_id";
val inj_converse_fun = thm "inj_converse_fun";
val left_inverse = thm "left_inverse";
val left_inverse_bij = thm "left_inverse_bij";
val right_inverse = thm "right_inverse";
val right_inverse_bij = thm "right_inverse_bij";
val inj_converse_inj = thm "inj_converse_inj";
val inj_converse_surj = thm "inj_converse_surj";
val bij_converse_bij = thm "bij_converse_bij";
val compI = thm "compI";
val compE = thm "compE";
val compEpair = thm "compEpair";
val converse_comp = thm "converse_comp";
val range_comp = thm "range_comp";
val range_comp_eq = thm "range_comp_eq";
val domain_comp = thm "domain_comp";
val domain_comp_eq = thm "domain_comp_eq";
val image_comp = thm "image_comp";
val comp_mono = thm "comp_mono";
val comp_rel = thm "comp_rel";
val comp_assoc = thm "comp_assoc";
val left_comp_id = thm "left_comp_id";
val right_comp_id = thm "right_comp_id";
val comp_function = thm "comp_function";
val comp_fun = thm "comp_fun";
val comp_fun_apply = thm "comp_fun_apply";
val comp_lam = thm "comp_lam";
val comp_inj = thm "comp_inj";
val comp_surj = thm "comp_surj";
val comp_bij = thm "comp_bij";
val comp_mem_injD1 = thm "comp_mem_injD1";
val comp_mem_injD2 = thm "comp_mem_injD2";
val comp_mem_surjD1 = thm "comp_mem_surjD1";
val comp_mem_surjD2 = thm "comp_mem_surjD2";
val left_comp_inverse = thm "left_comp_inverse";
val right_comp_inverse = thm "right_comp_inverse";
val comp_eq_id_iff = thm "comp_eq_id_iff";
val fg_imp_bijective = thm "fg_imp_bijective";
val nilpotent_imp_bijective = thm "nilpotent_imp_bijective";
val invertible_imp_bijective = thm "invertible_imp_bijective";
val inj_disjoint_Un = thm "inj_disjoint_Un";
val surj_disjoint_Un = thm "surj_disjoint_Un";
val bij_disjoint_Un = thm "bij_disjoint_Un";
val surj_image = thm "surj_image";
val restrict_image = thm "restrict_image";
val restrict_inj = thm "restrict_inj";
val restrict_surj = thm "restrict_surj";
val restrict_bij = thm "restrict_bij";
val inj_weaken_type = thm "inj_weaken_type";
val inj_succ_restrict = thm "inj_succ_restrict";
val inj_extend = thm "inj_extend";
*}

end

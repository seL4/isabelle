(* Title:     HOL/MiniML/Type.thy
   ID:        $Id$
   Author:    Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen

MiniML-types and type substitutions.
*)

theory Type = Maybe:

(* new class for structures containing type variables *)
axclass  type_struct < type


(* type expressions *)
datatype "typ" = TVar nat | "->" "typ" "typ" (infixr 70)

(* type schemata *)
datatype type_scheme = FVar nat | BVar nat | "=->" type_scheme type_scheme (infixr 70)


(* embedding types into type schemata *)    
consts
  mk_scheme :: "typ => type_scheme"

primrec
  "mk_scheme (TVar n) = (FVar n)"
  "mk_scheme (t1 -> t2) = ((mk_scheme t1) =-> (mk_scheme t2))"


instance  "typ"::type_struct ..
instance  type_scheme::type_struct ..  
instance  list::(type_struct)type_struct ..
instance  fun::(type,type_struct)type_struct ..


(* free_tv s: the type variables occuring freely in the type structure s *)

consts
  free_tv :: "['a::type_struct] => nat set"

primrec (free_tv_typ)
  free_tv_TVar:    "free_tv (TVar m) = {m}"
  free_tv_Fun:     "free_tv (t1 -> t2) = (free_tv t1) Un (free_tv t2)"

primrec (free_tv_type_scheme)
  "free_tv (FVar m) = {m}"
  "free_tv (BVar m) = {}"
  "free_tv (S1 =-> S2) = (free_tv S1) Un (free_tv S2)"

primrec (free_tv_list)
  "free_tv [] = {}"
  "free_tv (x#l) = (free_tv x) Un (free_tv l)"

  
(* executable version of free_tv: Implementation with lists *)
consts
  free_tv_ML :: "['a::type_struct] => nat list"

primrec (free_tv_ML_type_scheme)
  "free_tv_ML (FVar m) = [m]"
  "free_tv_ML (BVar m) = []"
  "free_tv_ML (S1 =-> S2) = (free_tv_ML S1) @ (free_tv_ML S2)"

primrec (free_tv_ML_list)
  "free_tv_ML [] = []"
  "free_tv_ML (x#l) = (free_tv_ML x) @ (free_tv_ML l)"

  
(* new_tv s n computes whether n is a new type variable w.r.t. a type 
   structure s, i.e. whether n is greater than any type variable 
   occuring in the type structure *)
constdefs
        new_tv :: "[nat,'a::type_struct] => bool"
        "new_tv n ts == ! m. m:(free_tv ts) --> m<n"

  
(* bound_tv s: the type variables occuring bound in the type structure s *)

consts
  bound_tv :: "['a::type_struct] => nat set"

primrec (bound_tv_type_scheme)
  "bound_tv (FVar m) = {}"
  "bound_tv (BVar m) = {m}"
  "bound_tv (S1 =-> S2) = (bound_tv S1) Un (bound_tv S2)"

primrec (bound_tv_list)
  "bound_tv [] = {}"
  "bound_tv (x#l) = (bound_tv x) Un (bound_tv l)"


(* minimal new free / bound variable *)

consts
  min_new_bound_tv :: "'a::type_struct => nat"

primrec (min_new_bound_tv_type_scheme)
  "min_new_bound_tv (FVar n) = 0"
  "min_new_bound_tv (BVar n) = Suc n"
  "min_new_bound_tv (sch1 =-> sch2) = max (min_new_bound_tv sch1) (min_new_bound_tv sch2)"


(* substitutions *)

(* type variable substitution *) 
types
        subst = "nat => typ"

(* identity *)
constdefs
        id_subst :: subst
        "id_subst == (%n. TVar n)"

(* extension of substitution to type structures *)
consts
  app_subst :: "[subst, 'a::type_struct] => 'a::type_struct" ("$")

primrec (app_subst_typ)
  app_subst_TVar: "$ S (TVar n) = S n" 
  app_subst_Fun:  "$ S (t1 -> t2) = ($ S t1) -> ($ S t2)" 

primrec (app_subst_type_scheme)
  "$ S (FVar n) = mk_scheme (S n)"
  "$ S (BVar n) = (BVar n)"
  "$ S (sch1 =-> sch2) = ($ S sch1) =-> ($ S sch2)"

defs
  app_subst_list: "$ S == map ($ S)"

(* domain of a substitution *)
constdefs
        dom :: "subst => nat set"
        "dom S == {n. S n ~= TVar n}" 

(* codomain of a substitution: the introduced variables *)

constdefs
        cod :: "subst => nat set"
        "cod S == (UN m:dom S. (free_tv (S m)))"

defs
        free_tv_subst:   "free_tv S == (dom S) Un (cod S)" 

  
(* unification algorithm mgu *)
consts
        mgu :: "[typ,typ] => subst option"
axioms
        mgu_eq:   "mgu t1 t2 = Some U ==> $U t1 = $U t2"
        mgu_mg:   "[| (mgu t1 t2) = Some U; $S t1 = $S t2 |] ==> ? R. S = $R o U"
        mgu_Some:   "$S t1 = $S t2 ==> ? U. mgu t1 t2 = Some U"
        mgu_free: "mgu t1 t2 = Some U ==> (free_tv U) <= (free_tv t1) Un (free_tv t2)"


declare mgu_eq [simp] mgu_mg [simp] mgu_free [simp]


(* lemmata for make scheme *)

lemma mk_scheme_Fun [rule_format (no_asm)]: "mk_scheme t = sch1 =-> sch2 --> (? t1 t2. sch1 = mk_scheme t1 & sch2 = mk_scheme t2)"
apply (induct_tac "t")
apply (simp (no_asm))
apply simp
apply fast
done

lemma mk_scheme_injective [rule_format (no_asm)]: "!t'. mk_scheme t = mk_scheme t' --> t=t'"
apply (induct_tac "t")
 apply (rule allI)
 apply (induct_tac "t'")
  apply (simp (no_asm))
 apply simp
apply (rule allI)
apply (induct_tac "t'")
 apply (simp (no_asm))
apply simp
done

lemma free_tv_mk_scheme: "free_tv (mk_scheme t) = free_tv t"
apply (induct_tac "t")
apply (simp_all (no_asm_simp))
done

declare free_tv_mk_scheme [simp]

lemma subst_mk_scheme: "$ S (mk_scheme t) = mk_scheme ($ S t)"
apply (induct_tac "t")
apply (simp_all (no_asm_simp))
done

declare subst_mk_scheme [simp]


(* constructor laws for app_subst *)

lemma app_subst_Nil: 
  "$ S [] = []"

apply (unfold app_subst_list)
apply (simp (no_asm))
done

lemma app_subst_Cons: 
  "$ S (x#l) = ($ S x)#($ S l)"
apply (unfold app_subst_list)
apply (simp (no_asm))
done

declare app_subst_Nil [simp] app_subst_Cons [simp]


(* constructor laws for new_tv *)

lemma new_tv_TVar: 
  "new_tv n (TVar m) = (m<n)"

apply (unfold new_tv_def)
apply (fastsimp)
done

lemma new_tv_FVar: 
  "new_tv n (FVar m) = (m<n)"
apply (unfold new_tv_def)
apply (fastsimp)
done

lemma new_tv_BVar: 
  "new_tv n (BVar m) = True"
apply (unfold new_tv_def)
apply (simp (no_asm))
done

lemma new_tv_Fun: 
  "new_tv n (t1 -> t2) = (new_tv n t1 & new_tv n t2)"
apply (unfold new_tv_def)
apply (fastsimp)
done

lemma new_tv_Fun2: 
  "new_tv n (t1 =-> t2) = (new_tv n t1 & new_tv n t2)"
apply (unfold new_tv_def)
apply (fastsimp)
done

lemma new_tv_Nil: 
  "new_tv n []"
apply (unfold new_tv_def)
apply (simp (no_asm))
done

lemma new_tv_Cons: 
  "new_tv n (x#l) = (new_tv n x & new_tv n l)"
apply (unfold new_tv_def)
apply (fastsimp)
done

lemma new_tv_TVar_subst: "new_tv n TVar"
apply (unfold new_tv_def)
apply (intro strip)
apply (simp add: free_tv_subst dom_def cod_def)
done

declare new_tv_TVar [simp] new_tv_FVar [simp] new_tv_BVar [simp] new_tv_Fun [simp] new_tv_Fun2 [simp] new_tv_Nil [simp] new_tv_Cons [simp] new_tv_TVar_subst [simp]

lemma new_tv_id_subst: 
  "new_tv n id_subst"
apply (unfold id_subst_def new_tv_def free_tv_subst dom_def cod_def)
apply (simp (no_asm))
done
declare new_tv_id_subst [simp]

lemma new_if_subst_type_scheme: "new_tv n (sch::type_scheme) -->  
      $(%k. if k<n then S k else S' k) sch = $S sch"
apply (induct_tac "sch")
apply (simp_all (no_asm_simp))
done
declare new_if_subst_type_scheme [simp]

lemma new_if_subst_type_scheme_list: "new_tv n (A::type_scheme list) -->  
      $(%k. if k<n then S k else S' k) A = $S A"
apply (induct_tac "A")
apply (simp_all (no_asm_simp))
done
declare new_if_subst_type_scheme_list [simp]


(* constructor laws for dom and cod *)

lemma dom_id_subst: 
  "dom id_subst = {}"

apply (unfold dom_def id_subst_def empty_def)
apply (simp (no_asm))
done
declare dom_id_subst [simp]

lemma cod_id_subst: 
  "cod id_subst = {}"
apply (unfold cod_def)
apply (simp (no_asm))
done
declare cod_id_subst [simp]


(* lemmata for free_tv *)

lemma free_tv_id_subst: 
  "free_tv id_subst = {}"

apply (unfold free_tv_subst)
apply (simp (no_asm))
done
declare free_tv_id_subst [simp]

lemma free_tv_nth_A_impl_free_tv_A [rule_format (no_asm)]: "!n. n < length A --> x : free_tv (A!n) --> x : free_tv A"
apply (induct_tac "A")
apply simp
apply (rule allI)
apply (induct_tac "n" rule: nat_induct)
apply simp
apply simp
done

declare free_tv_nth_A_impl_free_tv_A [simp]

lemma free_tv_nth_nat_A [rule_format (no_asm)]: "!nat. nat < length A --> x : free_tv (A!nat) --> x : free_tv A"
apply (induct_tac "A")
apply simp
apply (rule allI)
apply (induct_tac "nat" rule: nat_induct)
apply (intro strip)
apply simp
apply (simp (no_asm))
done


(* if two substitutions yield the same result if applied to a type
   structure the substitutions coincide on the free type variables
   occurring in the type structure *)

lemma typ_substitutions_only_on_free_variables [rule_format (no_asm)]: "(!x:free_tv t. (S x) = (S' x)) --> $ S (t::typ) = $ S' t"
apply (induct_tac "t")
apply (simp (no_asm))
apply simp
done

lemma eq_free_eq_subst_te: "(!n. n:(free_tv t) --> S1 n = S2 n) ==> $ S1 (t::typ) = $ S2 t"
apply (rule typ_substitutions_only_on_free_variables)
apply (simp (no_asm) add: Ball_def)
done

lemma scheme_substitutions_only_on_free_variables [rule_format (no_asm)]: "(!x:free_tv sch. (S x) = (S' x)) --> $ S (sch::type_scheme) = $ S' sch"
apply (induct_tac "sch")
apply (simp (no_asm))
apply (simp (no_asm))
apply simp
done

lemma eq_free_eq_subst_type_scheme: 
  "(!n. n:(free_tv sch) --> S1 n = S2 n) ==> $ S1 (sch::type_scheme) = $ S2 sch"
apply (rule scheme_substitutions_only_on_free_variables)
apply (simp (no_asm) add: Ball_def)
done

lemma eq_free_eq_subst_scheme_list [rule_format (no_asm)]: 
  "(!n. n:(free_tv A) --> S1 n = S2 n) --> $S1 (A::type_scheme list) = $S2 A"
apply (induct_tac "A")
(* case [] *)
apply (fastsimp)
(* case x#xl *)
apply (fastsimp intro: eq_free_eq_subst_type_scheme)
done

lemma weaken_asm_Un: "((!x:A. (P x)) --> Q) ==> ((!x:A Un B. (P x)) --> Q)"
apply fast
done

lemma scheme_list_substitutions_only_on_free_variables [rule_format (no_asm)]: "(!x:free_tv A. (S x) = (S' x)) --> $ S (A::type_scheme list) = $ S' A"
apply (induct_tac "A")
apply (simp (no_asm))
apply simp
apply (rule weaken_asm_Un)
apply (intro strip)
apply (erule scheme_substitutions_only_on_free_variables)
done

lemma eq_subst_te_eq_free [rule_format (no_asm)]: 
  "$ S1 (t::typ) = $ S2 t --> n:(free_tv t) --> S1 n = S2 n"
apply (induct_tac "t")
(* case TVar n *)
apply (fastsimp)
(* case Fun t1 t2 *)
apply (fastsimp)
done

lemma eq_subst_type_scheme_eq_free [rule_format (no_asm)]: 
  "$ S1 (sch::type_scheme) = $ S2 sch --> n:(free_tv sch) --> S1 n = S2 n"
apply (induct_tac "sch")
(* case TVar n *)
apply (simp (no_asm_simp))
(* case BVar n *)
apply (intro strip)
apply (erule mk_scheme_injective)
apply (simp (no_asm_simp))
(* case Fun t1 t2 *)
apply simp
done

lemma eq_subst_scheme_list_eq_free [rule_format (no_asm)]: 
  "$S1 (A::type_scheme list) = $S2 A --> n:(free_tv A) --> S1 n = S2 n"
apply (induct_tac "A")
(* case [] *)
apply (fastsimp)
(* case x#xl *)
apply (fastsimp intro: eq_subst_type_scheme_eq_free)
done

lemma codD: 
      "v : cod S ==> v : free_tv S"
apply (unfold free_tv_subst)
apply (fast)
done
 
lemma not_free_impl_id: 
      "x ~: free_tv S ==> S x = TVar x"
 
apply (unfold free_tv_subst dom_def)
apply (fast)
done

lemma free_tv_le_new_tv: 
      "[| new_tv n t; m:free_tv t |] ==> m<n"
apply (unfold new_tv_def)
apply (fast)
done

lemma cod_app_subst: 
  "[| v : free_tv(S n); v~=n |] ==> v : cod S"
apply (unfold dom_def cod_def UNION_def Bex_def)
apply (simp (no_asm))
apply (safe intro!: exI conjI notI)
prefer 2 apply (assumption)
apply simp
done
declare cod_app_subst [simp]

lemma free_tv_subst_var: "free_tv (S (v::nat)) <= insert v (cod S)"
apply (case_tac "v:dom S")
apply (fastsimp simp add: cod_def)
apply (fastsimp simp add: dom_def)
done

lemma free_tv_app_subst_te: "free_tv ($ S (t::typ)) <= cod S Un free_tv t"
apply (induct_tac "t")
(* case TVar n *)
apply (simp (no_asm) add: free_tv_subst_var)
(* case Fun t1 t2 *)
apply (fastsimp)
done

lemma free_tv_app_subst_type_scheme: "free_tv ($ S (sch::type_scheme)) <= cod S Un free_tv sch"
apply (induct_tac "sch")
(* case FVar n *)
apply (simp (no_asm) add: free_tv_subst_var)
(* case BVar n *)
apply (simp (no_asm))
(* case Fun t1 t2 *)
apply (fastsimp)
done

lemma free_tv_app_subst_scheme_list: "free_tv ($ S (A::type_scheme list)) <= cod S Un free_tv A"
apply (induct_tac "A")
(* case [] *)
apply (simp (no_asm))
(* case a#al *)
apply (cut_tac free_tv_app_subst_type_scheme)
apply (fastsimp)
done

lemma free_tv_comp_subst: 
     "free_tv (%u::nat. $ s1 (s2 u) :: typ) <=    
      free_tv s1 Un free_tv s2"
apply (unfold free_tv_subst dom_def) 
apply (clarsimp simp add: cod_def dom_def)
apply (drule free_tv_app_subst_te [THEN subsetD])
apply clarsimp
apply (auto simp add: cod_def dom_def)
apply (drule free_tv_subst_var [THEN subsetD])
apply (auto simp add: cod_def dom_def)
done

lemma free_tv_o_subst: 
     "free_tv ($ S1 o S2) <= free_tv S1 Un free_tv (S2 :: nat => typ)"
apply (unfold o_def)
apply (rule free_tv_comp_subst)
done

lemma free_tv_of_substitutions_extend_to_types [rule_format (no_asm)]: "n : free_tv t --> free_tv (S n) <= free_tv ($ S t::typ)"
apply (induct_tac "t")
apply (simp (no_asm))
apply (simp (no_asm))
apply fast
done

lemma free_tv_of_substitutions_extend_to_schemes [rule_format (no_asm)]: "n : free_tv sch --> free_tv (S n) <= free_tv ($ S sch::type_scheme)"
apply (induct_tac "sch")
apply (simp (no_asm))
apply (simp (no_asm))
apply (simp (no_asm))
apply fast
done

lemma free_tv_of_substitutions_extend_to_scheme_lists [rule_format (no_asm)]: "n : free_tv A --> free_tv (S n) <= free_tv ($ S A::type_scheme list)"
apply (induct_tac "A")
apply (simp (no_asm))
apply (simp (no_asm))
apply (fast dest: free_tv_of_substitutions_extend_to_schemes)
done

declare free_tv_of_substitutions_extend_to_scheme_lists [simp]

lemma free_tv_ML_scheme: "!!sch::type_scheme. (n : free_tv sch) = (n: set (free_tv_ML sch))"
apply (induct_tac "sch")
apply (simp_all (no_asm_simp))
done

lemma free_tv_ML_scheme_list: "!!A::type_scheme list. (n : free_tv A) = (n: set (free_tv_ML A))"
apply (induct_tac "A")
apply (simp (no_asm))
apply (simp (no_asm_simp) add: free_tv_ML_scheme)
done


(* lemmata for bound_tv *)

lemma bound_tv_mk_scheme: "bound_tv (mk_scheme t) = {}"
apply (induct_tac "t")
apply (simp_all (no_asm_simp))
done

declare bound_tv_mk_scheme [simp]

lemma bound_tv_subst_scheme: "!!sch::type_scheme. bound_tv ($ S sch) = bound_tv sch"
apply (induct_tac "sch")
apply (simp_all (no_asm_simp))
done

declare bound_tv_subst_scheme [simp]

lemma bound_tv_subst_scheme_list: "!!A::type_scheme list. bound_tv ($ S A) = bound_tv A"
apply (rule list.induct)
apply (simp (no_asm))
apply (simp (no_asm_simp))
done

declare bound_tv_subst_scheme_list [simp]


(* lemmata for new_tv *)

lemma new_tv_subst: 
  "new_tv n S = ((!m. n <= m --> (S m = TVar m)) &  
                 (! l. l < n --> new_tv n (S l) ))"

apply (unfold new_tv_def)
apply (safe)
  (* ==> *)
  apply (fastsimp dest: leD simp add: free_tv_subst dom_def)
 apply (subgoal_tac "m:cod S | S l = TVar l")
  apply safe
   apply (fastsimp dest: UnI2 simp add: free_tv_subst)
  apply (drule_tac P = "%x. m:free_tv x" in subst , assumption)
  apply simp
 apply (fastsimp simp add: free_tv_subst cod_def dom_def)
(* <== *)
apply (unfold free_tv_subst cod_def dom_def)
apply safe
 apply (cut_tac m = "m" and n = "n" in less_linear)
 apply (fast intro!: less_or_eq_imp_le)
apply (cut_tac m = "ma" and n = "n" in less_linear)
apply (fast intro!: less_or_eq_imp_le) 
done

lemma new_tv_list: "new_tv n x = (!y:set x. new_tv n y)"
apply (induct_tac "x")
apply (simp_all (no_asm_simp))
done

(* substitution affects only variables occurring freely *)
lemma subst_te_new_tv: 
  "new_tv n (t::typ) --> $(%x. if x=n then t' else S x) t = $S t"
apply (induct_tac "t")
apply (simp_all (no_asm_simp))
done
declare subst_te_new_tv [simp]

lemma subst_te_new_type_scheme [rule_format (no_asm)]: 
  "new_tv n (sch::type_scheme) --> $(%x. if x=n then sch' else S x) sch = $S sch"
apply (induct_tac "sch")
apply (simp_all (no_asm_simp))
done
declare subst_te_new_type_scheme [simp]

lemma subst_tel_new_scheme_list [rule_format (no_asm)]: 
  "new_tv n (A::type_scheme list) --> $(%x. if x=n then t else S x) A = $S A"
apply (induct_tac "A")
apply simp_all
done
declare subst_tel_new_scheme_list [simp]

(* all greater variables are also new *)
lemma new_tv_le: 
  "n<=m ==> new_tv n t ==> new_tv m t"
apply (unfold new_tv_def)
apply safe
apply (drule spec)
apply (erule (1) notE impE)
apply (simp (no_asm))
done
declare lessI [THEN less_imp_le [THEN new_tv_le], simp]

lemma new_tv_typ_le: "n<=m ==> new_tv n (t::typ) ==> new_tv m t"
apply (simp (no_asm_simp) add: new_tv_le)
done

lemma new_scheme_list_le: "n<=m ==> new_tv n (A::type_scheme list) ==> new_tv m A"
apply (simp (no_asm_simp) add: new_tv_le)
done

lemma new_tv_subst_le: "n<=m ==> new_tv n (S::subst) ==> new_tv m S"
apply (simp (no_asm_simp) add: new_tv_le)
done

(* new_tv property remains if a substitution is applied *)
lemma new_tv_subst_var: 
  "[| n<m; new_tv m (S::subst) |] ==> new_tv m (S n)"
apply (simp add: new_tv_subst)
done

lemma new_tv_subst_te [rule_format (no_asm)]: 
  "new_tv n S --> new_tv n (t::typ) --> new_tv n ($ S t)"
apply (induct_tac "t")
apply (fastsimp simp add: new_tv_subst)+
done
declare new_tv_subst_te [simp]

lemma new_tv_subst_type_scheme [rule_format (no_asm)]: "new_tv n S --> new_tv n (sch::type_scheme) --> new_tv n ($ S sch)"
apply (induct_tac "sch")
apply (simp_all)
apply (unfold new_tv_def)
apply (simp (no_asm) add: free_tv_subst dom_def cod_def)
apply (intro strip)
apply (case_tac "S nat = TVar nat")
apply simp
apply (drule_tac x = "m" in spec)
apply fast
done
declare new_tv_subst_type_scheme [simp]

lemma new_tv_subst_scheme_list [rule_format (no_asm)]: 
  "new_tv n S --> new_tv n (A::type_scheme list) --> new_tv n ($ S A)"
apply (induct_tac "A")
apply (fastsimp)+
done
declare new_tv_subst_scheme_list [simp]

lemma new_tv_Suc_list: "new_tv n A --> new_tv (Suc n) ((TVar n)#A)"
apply (simp (no_asm) add: new_tv_list)
done

lemma new_tv_only_depends_on_free_tv_type_scheme [rule_format (no_asm)]: "!!sch::type_scheme. (free_tv sch) = (free_tv sch') --> (new_tv n sch --> new_tv n sch')"
apply (unfold new_tv_def)
apply (simp (no_asm_simp))
done

lemma new_tv_only_depends_on_free_tv_scheme_list [rule_format (no_asm)]: "!!A::type_scheme list. (free_tv A) = (free_tv A') --> (new_tv n A --> new_tv n A')"
apply (unfold new_tv_def)
apply (simp (no_asm_simp))
done

lemma new_tv_nth_nat_A [rule_format (no_asm)]: 
  "!nat. nat < length A --> new_tv n A --> (new_tv n (A!nat))"
apply (unfold new_tv_def)
apply (induct_tac "A")
apply simp
apply (rule allI)
apply (induct_tac "nat" rule: nat_induct)
apply (intro strip)
apply simp
apply (simp (no_asm))
done


(* composition of substitutions preserves new_tv proposition *)
lemma new_tv_subst_comp_1: "[| new_tv n (S::subst); new_tv n R |] ==> new_tv n (($ R) o S)"
apply (simp add: new_tv_subst)
done

lemma new_tv_subst_comp_2: "[| new_tv n (S::subst); new_tv n R |] ==> new_tv n (%v.$ R (S v))"
apply (simp add: new_tv_subst)
done

declare new_tv_subst_comp_1 [simp] new_tv_subst_comp_2 [simp]

(* new type variables do not occur freely in a type structure *)
lemma new_tv_not_free_tv: 
      "new_tv n A ==> n~:(free_tv A)"
apply (unfold new_tv_def)
apply (fast elim: less_irrefl)
done
declare new_tv_not_free_tv [simp]

lemma fresh_variable_types: "!!t::typ. ? n. (new_tv n t)"
apply (unfold new_tv_def)
apply (induct_tac "t")
apply (rule_tac x = "Suc nat" in exI)
apply (simp (no_asm_simp))
apply (erule exE)+
apply (rename_tac "n'")
apply (rule_tac x = "max n n'" in exI)
apply (simp (no_asm) add: less_max_iff_disj)
apply blast
done

declare fresh_variable_types [simp]

lemma fresh_variable_type_schemes: "!!sch::type_scheme. ? n. (new_tv n sch)"
apply (unfold new_tv_def)
apply (induct_tac "sch")
apply (rule_tac x = "Suc nat" in exI)
apply (simp (no_asm))
apply (rule_tac x = "Suc nat" in exI)
apply (simp (no_asm))
apply (erule exE)+
apply (rename_tac "n'")
apply (rule_tac x = "max n n'" in exI)
apply (simp (no_asm) add: less_max_iff_disj)
apply blast
done

declare fresh_variable_type_schemes [simp]

lemma fresh_variable_type_scheme_lists: "!!A::type_scheme list. ? n. (new_tv n A)"
apply (induct_tac "A")
apply (simp (no_asm))
apply (simp (no_asm))
apply (erule exE)
apply (cut_tac sch = "a" in fresh_variable_type_schemes)
apply (erule exE)
apply (rename_tac "n'")
apply (rule_tac x = " (max n n') " in exI)
apply (subgoal_tac "n <= (max n n') ")
apply (subgoal_tac "n' <= (max n n') ")
apply (fast dest: new_tv_le)
apply (simp_all (no_asm) add: le_max_iff_disj)
done

declare fresh_variable_type_scheme_lists [simp]

lemma make_one_new_out_of_two: "[| ? n1. (new_tv n1 x); ? n2. (new_tv n2 y)|] ==> ? n. (new_tv n x) & (new_tv n y)"
apply (erule exE)+
apply (rename_tac "n1" "n2")
apply (rule_tac x = " (max n1 n2) " in exI)
apply (subgoal_tac "n1 <= max n1 n2")
apply (subgoal_tac "n2 <= max n1 n2")
apply (fast dest: new_tv_le)
apply (simp_all (no_asm) add: le_max_iff_disj)
done

lemma ex_fresh_variable: "!!(A::type_scheme list) (A'::type_scheme list) (t::typ) (t'::typ).  
          ? n. (new_tv n A) & (new_tv n A') & (new_tv n t) & (new_tv n t')"
apply (cut_tac t = "t" in fresh_variable_types)
apply (cut_tac t = "t'" in fresh_variable_types)
apply (drule make_one_new_out_of_two)
apply assumption
apply (erule_tac V = "? n. new_tv n t'" in thin_rl)
apply (cut_tac A = "A" in fresh_variable_type_scheme_lists)
apply (cut_tac A = "A'" in fresh_variable_type_scheme_lists)
apply (rotate_tac 1)
apply (drule make_one_new_out_of_two)
apply assumption
apply (erule_tac V = "? n. new_tv n A'" in thin_rl)
apply (erule exE)+
apply (rename_tac n2 n1)
apply (rule_tac x = " (max n1 n2) " in exI)
apply (unfold new_tv_def)
apply (simp (no_asm) add: less_max_iff_disj)
apply blast
done

(* mgu does not introduce new type variables *)
lemma mgu_new: 
      "[|mgu t1 t2 = Some u; new_tv n t1; new_tv n t2|] ==> new_tv n u"
apply (unfold new_tv_def)
apply (fast dest: mgu_free)
done


(* lemmata for substitutions *)

lemma length_app_subst_list: 
   "!!A:: ('a::type_struct) list. length ($ S A) = length A"

apply (unfold app_subst_list)
apply (simp (no_asm))
done
declare length_app_subst_list [simp]

lemma subst_TVar_scheme: "!!sch::type_scheme. $ TVar sch = sch"
apply (induct_tac "sch")
apply (simp_all (no_asm_simp))
done

declare subst_TVar_scheme [simp]

lemma subst_TVar_scheme_list: "!!A::type_scheme list. $ TVar A = A"
apply (rule list.induct)
apply (simp_all add: app_subst_list)
done

declare subst_TVar_scheme_list [simp]

(* application of id_subst does not change type expression *)
lemma app_subst_id_te: 
  "$ id_subst = (%t::typ. t)"
apply (unfold id_subst_def)
apply (rule ext)
apply (induct_tac "t")
apply (simp_all (no_asm_simp))
done
declare app_subst_id_te [simp]

lemma app_subst_id_type_scheme: 
  "$ id_subst = (%sch::type_scheme. sch)"
apply (unfold id_subst_def)
apply (rule ext)
apply (induct_tac "sch")
apply (simp_all (no_asm_simp))
done
declare app_subst_id_type_scheme [simp]

(* application of id_subst does not change list of type expressions *)
lemma app_subst_id_tel: 
  "$ id_subst = (%A::type_scheme list. A)"
apply (unfold app_subst_list)
apply (rule ext)
apply (induct_tac "A")
apply (simp_all (no_asm_simp))
done
declare app_subst_id_tel [simp]

lemma id_subst_sch: "!!sch::type_scheme. $ id_subst sch = sch"
apply (induct_tac "sch")
apply (simp_all add: id_subst_def)
done

declare id_subst_sch [simp]

lemma id_subst_A: "!!A::type_scheme list. $ id_subst A = A"
apply (induct_tac "A")
apply simp
apply simp
done

declare id_subst_A [simp]

(* composition of substitutions *)
lemma o_id_subst: "$S o id_subst = S"
apply (unfold id_subst_def o_def)
apply (rule ext)
apply (simp (no_asm))
done
declare o_id_subst [simp]

lemma subst_comp_te: "$ R ($ S t::typ) = $ (%x. $ R (S x) ) t"
apply (induct_tac "t")
apply (simp_all (no_asm_simp))
done

lemma subst_comp_type_scheme: "$ R ($ S sch::type_scheme) = $ (%x. $ R (S x) ) sch"
apply (induct_tac "sch")
apply simp_all
done

lemma subst_comp_scheme_list: 
  "$ R ($ S A::type_scheme list) = $ (%x. $ R (S x)) A"
apply (unfold app_subst_list)
apply (induct_tac "A")
(* case [] *)
apply (simp (no_asm))
(* case x#xl *)
apply (simp add: subst_comp_type_scheme)
done

lemma subst_id_on_type_scheme_list': "!!A::type_scheme list. !x : free_tv A. S x = (TVar x) ==> $ S A = $ id_subst A"
apply (rule scheme_list_substitutions_only_on_free_variables)
apply (simp add: id_subst_def)
done

lemma subst_id_on_type_scheme_list: "!!A::type_scheme list. !x : free_tv A. S x = (TVar x) ==> $ S A = A"
apply (subst subst_id_on_type_scheme_list')
apply assumption
apply (simp (no_asm))
done

lemma nth_subst [rule_format (no_asm)]: "!n. n < length A --> ($ S A)!n = $S (A!n)"
apply (induct_tac "A")
apply simp
apply (rule allI)
apply (rename_tac "n1")
apply (induct_tac "n1" rule: nat_induct)
apply simp
apply simp
done


end

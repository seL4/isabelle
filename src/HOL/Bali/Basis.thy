(*  Title:      HOL/Bali/Basis.thy
    ID:         $Id$
    Author:     David von Oheimb
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

*)
header {* Definitions extending HOL as logical basis of Bali *}

theory Basis = Main:

ML_setup {*
Unify.search_bound := 40;
Unify.trace_bound  := 40;
*}
(*print_depth 100;*)
(*Syntax.ambiguity_level := 1;*)

section "misc"

declare same_fstI [intro!] (*### TO HOL/Wellfounded_Relations *)

ML {*
fun cond_simproc name pat pred thm = Simplifier.simproc (Thm.sign_of_thm thm) name [pat]
  (fn _ => fn _ => fn t => if pred t then None else Some (mk_meta_eq thm));
*}

declare split_if_asm  [split] option.split [split] option.split_asm [split]
ML {*
simpset_ref() := simpset() addloop ("split_all_tac", split_all_tac)
*}
declare if_weak_cong [cong del] option.weak_case_cong [cong del]
declare length_Suc_conv [iff];

(*###to be phased out *)
ML {*
bind_thm ("make_imp", rearrange_prems [1,0] mp)
*}

lemma Collect_split_eq: "{p. P (split f p)} = {(a,b). P (f a b)}"
apply auto
done

lemma subset_insertD: 
  "A <= insert x B ==> A <= B & x ~: A | (EX B'. A = insert x B' & B' <= B)"
apply (case_tac "x:A")
apply (rule disjI2)
apply (rule_tac x = "A-{x}" in exI)
apply fast+
done

syntax
  "3" :: nat   ("3") 
  "4" :: nat   ("4")
translations
 "3" == "Suc 2"
 "4" == "Suc 3"

(*unused*)
lemma range_bool_domain: "range f = {f True, f False}"
apply auto
apply (case_tac "xa")
apply auto
done

(* context (theory "Transitive_Closure") *)
lemma irrefl_tranclI': "r^-1 Int r^+ = {} ==> !x. (x, x) ~: r^+"
apply (rule allI)
apply (erule irrefl_tranclI)
done

lemma trancl_rtrancl_trancl:
"\<lbrakk>(x,y)\<in>r^+; (y,z)\<in>r^*\<rbrakk> \<Longrightarrow> (x,z)\<in>r^+"
by (auto dest: tranclD rtrancl_trans rtrancl_into_trancl2)

lemma rtrancl_into_trancl3:
"\<lbrakk>(a,b)\<in>r^*; a\<noteq>b\<rbrakk> \<Longrightarrow> (a,b)\<in>r^+" 
apply (drule rtranclD)
apply auto
done

lemma rtrancl_into_rtrancl2: 
  "\<lbrakk> (a, b) \<in>  r; (b, c) \<in> r^* \<rbrakk> \<Longrightarrow> (a, c) \<in>  r^*"
by (auto intro: r_into_rtrancl rtrancl_trans)

lemma triangle_lemma:
 "\<lbrakk> \<And> a b c. \<lbrakk>(a,b)\<in>r; (a,c)\<in>r\<rbrakk> \<Longrightarrow> b=c; (a,x)\<in>r\<^sup>*; (a,y)\<in>r\<^sup>*\<rbrakk> 
 \<Longrightarrow> (x,y)\<in>r\<^sup>* \<or> (y,x)\<in>r\<^sup>*"
proof -
  note converse_rtrancl_induct = converse_rtrancl_induct [consumes 1]
  note converse_rtranclE = converse_rtranclE [consumes 1] 
  assume unique: "\<And> a b c. \<lbrakk>(a,b)\<in>r; (a,c)\<in>r\<rbrakk> \<Longrightarrow> b=c"
  assume "(a,x)\<in>r\<^sup>*" 
  then show "(a,y)\<in>r\<^sup>* \<Longrightarrow> (x,y)\<in>r\<^sup>* \<or> (y,x)\<in>r\<^sup>*"
  proof (induct rule: converse_rtrancl_induct)
    assume "(x,y)\<in>r\<^sup>*"
    then show ?thesis 
      by blast
  next
    fix a v
    assume a_v_r: "(a, v) \<in> r" and
          v_x_rt: "(v, x) \<in> r\<^sup>*" and
          a_y_rt: "(a, y) \<in> r\<^sup>*"  and
             hyp: "(v, y) \<in> r\<^sup>* \<Longrightarrow> (x, y) \<in> r\<^sup>* \<or> (y, x) \<in> r\<^sup>*"
    from a_y_rt 
    show "(x, y) \<in> r\<^sup>* \<or> (y, x) \<in> r\<^sup>*"
    proof (cases rule: converse_rtranclE)
      assume "a=y"
      with a_v_r v_x_rt have "(y,x) \<in> r\<^sup>*"
	by (auto intro: r_into_rtrancl rtrancl_trans)
      then show ?thesis 
	by blast
    next
      fix w 
      assume a_w_r: "(a, w) \<in> r" and
            w_y_rt: "(w, y) \<in> r\<^sup>*"
      from a_v_r a_w_r unique 
      have "v=w" 
	by auto
      with w_y_rt hyp 
      show ?thesis
	by blast
    qed
  qed
qed


lemma rtrancl_cases [consumes 1, case_names Refl Trancl]:
 "\<lbrakk>(a,b)\<in>r\<^sup>*;  a = b \<Longrightarrow> P; (a,b)\<in>r\<^sup>+ \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
apply (erule rtranclE)
apply (auto dest: rtrancl_into_trancl1)
done

(* ### To Transitive_Closure *)
theorems converse_rtrancl_induct 
 = converse_rtrancl_induct [consumes 1,case_names Id Step]

theorems converse_trancl_induct 
         = converse_trancl_induct [consumes 1,case_names Single Step]

(* context (theory "Set") *)
lemma Ball_weaken:"\<lbrakk>Ball s P;\<And> x. P x\<longrightarrow>Q x\<rbrakk>\<Longrightarrow>Ball s Q"
by auto

(* context (theory "Finite") *)
lemma finite_SetCompr2: "[| finite (Collect P); !y. P y --> finite (range (f y)) |] ==>  
  finite {f y x |x y. P y}"
apply (subgoal_tac "{f y x |x y. P y} = UNION (Collect P) (%y. range (f y))")
prefer 2 apply  fast
apply (erule ssubst)
apply (erule finite_UN_I)
apply fast
done


(* ### TO theory "List" *)
lemma list_all2_trans: "\<forall> a b c. P1 a b \<longrightarrow> P2 b c \<longrightarrow> P3 a c \<Longrightarrow>
 \<forall>xs2 xs3. list_all2 P1 xs1 xs2 \<longrightarrow> list_all2 P2 xs2 xs3 \<longrightarrow> list_all2 P3 xs1 xs3"
apply (induct_tac "xs1")
apply simp
apply (rule allI)
apply (induct_tac "xs2")
apply simp
apply (rule allI)
apply (induct_tac "xs3")
apply auto
done


section "pairs"

lemma surjective_pairing5: "p = (fst p, fst (snd p), fst (snd (snd p)), fst (snd (snd (snd p))), 
  snd (snd (snd (snd p))))"
apply auto
done

lemma fst_splitE [elim!]: 
"[| fst s' = x';  !!x s. [| s' = (x,s);  x = x' |] ==> Q |] ==> Q"
apply (cut_tac p = "s'" in surjective_pairing)
apply auto
done

lemma fst_in_set_lemma [rule_format (no_asm)]: "(x, y) : set l --> x : fst ` set l"
apply (induct_tac "l")
apply  auto
done


section "quantifiers"

(*###to be phased out *)
ML {* 
fun noAll_simpset () = simpset() setmksimps 
	mksimps (filter (fn (x,_) => x<>"All") mksimps_pairs)
*}

lemma All_Ex_refl_eq2 [simp]: 
 "(!x. (? b. x = f b & Q b) \<longrightarrow> P x) = (!b. Q b --> P (f b))"
apply auto
done

lemma ex_ex_miniscope1 [simp]:
  "(EX w v. P w v & Q v) = (EX v. (EX w. P w v) & Q v)"
apply auto
done

lemma ex_miniscope2 [simp]:
  "(EX v. P v & Q & R v) = (Q & (EX v. P v & R v))" 
apply auto
done

lemma ex_reorder31: "(\<exists>z x y. P x y z) = (\<exists>x y z. P x y z)"
apply auto
done

lemma All_Ex_refl_eq1 [simp]: "(!x. (? b. x = f b) --> P x) = (!b. P (f b))"
apply auto
done


section "sums"

hide const In0 In1

syntax
  fun_sum :: "('a => 'c) => ('b => 'c) => (('a+'b) => 'c)" (infixr "'(+')"80)
translations
 "fun_sum" == "sum_case"

consts    the_Inl  :: "'a + 'b \<Rightarrow> 'a"
          the_Inr  :: "'a + 'b \<Rightarrow> 'b"
primrec  "the_Inl (Inl a) = a"
primrec  "the_Inr (Inr b) = b"

datatype ('a, 'b, 'c) sum3 = In1 'a | In2 'b | In3 'c

consts    the_In1  :: "('a, 'b, 'c) sum3 \<Rightarrow> 'a"
          the_In2  :: "('a, 'b, 'c) sum3 \<Rightarrow> 'b"
          the_In3  :: "('a, 'b, 'c) sum3 \<Rightarrow> 'c"
primrec  "the_In1 (In1 a) = a"
primrec  "the_In2 (In2 b) = b"
primrec  "the_In3 (In3 c) = c"

syntax
	 In1l	:: "'al \<Rightarrow> ('al + 'ar, 'b, 'c) sum3"
	 In1r	:: "'ar \<Rightarrow> ('al + 'ar, 'b, 'c) sum3"
translations
	"In1l e" == "In1 (Inl e)"
	"In1r c" == "In1 (Inr c)"

syntax the_In1l :: "('al + 'ar, 'b, 'c) sum3 \<Rightarrow> 'al"
       the_In1r :: "('al + 'ar, 'b, 'c) sum3 \<Rightarrow> 'ar"
translations
   "the_In1l" == "the_Inl \<circ> the_In1"
   "the_In1r" == "the_Inr \<circ> the_In1"

ML {*
fun sum3_instantiate thm = map (fn s => simplify(simpset()delsimps[not_None_eq])
 (read_instantiate [("t","In"^s^" ?x")] thm)) ["1l","2","3","1r"]
*}
(* e.g. lemmas is_stmt_rews = is_stmt_def [of "In1l x", simplified] *)

translations
  "option"<= (type) "Datatype.option"
  "list"  <= (type) "List.list"
  "sum3"  <= (type) "Basis.sum3"


section "quantifiers for option type"

syntax
  Oall :: "[pttrn, 'a option, bool] => bool"   ("(3! _:_:/ _)" [0,0,10] 10)
  Oex  :: "[pttrn, 'a option, bool] => bool"   ("(3? _:_:/ _)" [0,0,10] 10)

syntax (symbols)
  Oall :: "[pttrn, 'a option, bool] => bool"   ("(3\<forall>_\<in>_:/ _)"  [0,0,10] 10)
  Oex  :: "[pttrn, 'a option, bool] => bool"   ("(3\<exists>_\<in>_:/ _)"  [0,0,10] 10)

translations
  "! x:A: P"    == "! x:o2s A. P"
  "? x:A: P"    == "? x:o2s A. P"


section "unique association lists"

constdefs
  unique   :: "('a \<times> 'b) list \<Rightarrow> bool"
 "unique \<equiv> distinct \<circ> map fst"

lemma uniqueD [rule_format (no_asm)]: 
"unique l--> (!x y. (x,y):set l --> (!x' y'. (x',y'):set l --> x=x'-->  y=y'))"
apply (unfold unique_def o_def)
apply (induct_tac "l")
apply  (auto dest: fst_in_set_lemma)
done

lemma unique_Nil [simp]: "unique []"
apply (unfold unique_def)
apply (simp (no_asm))
done

lemma unique_Cons [simp]: "unique ((x,y)#l) = (unique l & (!y. (x,y) ~: set l))"
apply (unfold unique_def)
apply  (auto dest: fst_in_set_lemma)
done

lemmas unique_ConsI = conjI [THEN unique_Cons [THEN iffD2], standard]

lemma unique_single [simp]: "!!p. unique [p]"
apply auto
done

lemma unique_ConsD: "unique (x#xs) ==> unique xs"
apply (simp add: unique_def)
done

lemma unique_append [rule_format (no_asm)]: "unique l' ==> unique l -->  
  (!(x,y):set l. !(x',y'):set l'. x' ~= x) --> unique (l @ l')"
apply (induct_tac "l")
apply  (auto dest: fst_in_set_lemma)
done

lemma unique_map_inj [rule_format (no_asm)]: "unique l --> inj f --> unique (map (%(k,x). (f k, g k x)) l)"
apply (induct_tac "l")
apply  (auto dest: fst_in_set_lemma simp add: inj_eq)
done

lemma map_of_SomeI [rule_format (no_asm)]: "unique l --> (k, x) : set l --> map_of l k = Some x"
apply (induct_tac "l")
apply auto
done


section "list patterns"

consts
  lsplit         :: "[['a, 'a list] => 'b, 'a list] => 'b"
defs
  lsplit_def:    "lsplit == %f l. f (hd l) (tl l)"
(*  list patterns -- extends pre-defined type "pttrn" used in abstractions *)
syntax
  "_lpttrn"    :: "[pttrn,pttrn] => pttrn"     ("_#/_" [901,900] 900)
translations
  "%y#x#xs. b"  == "lsplit (%y x#xs. b)"
  "%x#xs  . b"  == "lsplit (%x xs  . b)"

lemma lsplit [simp]: "lsplit c (x#xs) = c x xs"
apply (unfold lsplit_def)
apply (simp (no_asm))
done

lemma lsplit2 [simp]: "lsplit P (x#xs) y z = P x xs y z"
apply (unfold lsplit_def)
apply simp
done 


section "dummy pattern for quantifiers, let, etc."

syntax
  "@dummy_pat"   :: pttrn    ("'_")

parse_translation {*
let fun dummy_pat_tr [] = Free ("_",dummyT)
  | dummy_pat_tr ts = raise TERM ("dummy_pat_tr", ts);
in [("@dummy_pat", dummy_pat_tr)] 
end
*}

end

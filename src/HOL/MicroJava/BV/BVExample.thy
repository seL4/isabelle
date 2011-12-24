(*  Title:      HOL/MicroJava/BV/BVExample.thy
    Author:     Gerwin Klein
*)

header {* \isaheader{Example Welltypings}\label{sec:BVExample} *}

theory BVExample
imports
  "../JVM/JVMListExample"
  BVSpecTypeSafe
  JVM
  "~~/src/HOL/Library/Executable_Set"
begin

text {*
  This theory shows type correctness of the example program in section 
  \ref{sec:JVMListExample} (p. \pageref{sec:JVMListExample}) by
  explicitly providing a welltyping. It also shows that the start
  state of the program conforms to the welltyping; hence type safe
  execution is guaranteed.
*}

section "Setup"

text {* Abbreviations for definitions we will have to use often in the
proofs below: *}
lemmas name_defs   = list_name_def test_name_def val_name_def next_name_def 
lemmas system_defs = SystemClasses_def ObjectC_def NullPointerC_def 
                     OutOfMemoryC_def ClassCastC_def
lemmas class_defs  = list_class_def test_class_def

text {* These auxiliary proofs are for efficiency: class lookup,
subclass relation, method and field lookup are computed only once:
*}
lemma class_Object [simp]:
  "class E Object = Some (undefined, [],[])"
  by (simp add: class_def system_defs E_def)

lemma class_NullPointer [simp]:
  "class E (Xcpt NullPointer) = Some (Object, [], [])"
  by (simp add: class_def system_defs E_def)

lemma class_OutOfMemory [simp]:
  "class E (Xcpt OutOfMemory) = Some (Object, [], [])"
  by (simp add: class_def system_defs E_def)

lemma class_ClassCast [simp]:
  "class E (Xcpt ClassCast) = Some (Object, [], [])"
  by (simp add: class_def system_defs E_def)

lemma class_list [simp]:
  "class E list_name = Some list_class"
  by (simp add: class_def system_defs E_def name_defs distinct_classes [symmetric])
 
lemma class_test [simp]:
  "class E test_name = Some test_class"
  by (simp add: class_def system_defs E_def name_defs distinct_classes [symmetric])

lemma E_classes [simp]:
  "{C. is_class E C} = {list_name, test_name, Xcpt NullPointer, 
                        Xcpt ClassCast, Xcpt OutOfMemory, Object}"
  by (auto simp add: is_class_def class_def system_defs E_def name_defs class_defs)

text {* The subclass releation spelled out: *}
lemma subcls1:
  "subcls1 E = {(list_name,Object), (test_name,Object), (Xcpt NullPointer, Object),
                (Xcpt ClassCast, Object), (Xcpt OutOfMemory, Object)}"
apply (simp add: subcls1_def2)
apply (simp add: name_defs class_defs system_defs E_def class_def)
apply (simp add: Sigma_def)
apply auto
done

text {* The subclass relation is acyclic; hence its converse is well founded: *}
lemma notin_rtrancl:
  "(a, b) \<in> r\<^sup>* \<Longrightarrow> a \<noteq> b \<Longrightarrow> (\<And>y. (a, y) \<notin> r) \<Longrightarrow> False"
  by (auto elim: converse_rtranclE)

lemma acyclic_subcls1_E: "acyclic (subcls1 E)"
  apply (rule acyclicI)
  apply (simp add: subcls1)
  apply (auto dest!: tranclD)
  apply (auto elim!: notin_rtrancl simp add: name_defs distinct_classes)
  done

lemma wf_subcls1_E: "wf ((subcls1 E)\<inverse>)"
  apply (rule finite_acyclic_wf_converse)
  apply (simp add: subcls1 del: insert_iff)
  apply (rule acyclic_subcls1_E)
  done  

text {* Method and field lookup: *}
lemma method_Object [simp]:
  "method (E, Object) = Map.empty"
  by (simp add: method_rec_lemma [OF class_Object wf_subcls1_E])

lemma method_append [simp]:
  "method (E, list_name) (append_name, [Class list_name]) =
  Some (list_name, PrimT Void, 3, 0, append_ins, [(1, 2, 8, Xcpt NullPointer)])"
  apply (insert class_list)
  apply (unfold list_class_def)
  apply (drule method_rec_lemma [OF _ wf_subcls1_E])
  apply simp
  done

lemma method_makelist [simp]:
  "method (E, test_name) (makelist_name, []) = 
  Some (test_name, PrimT Void, 3, 2, make_list_ins, [])"
  apply (insert class_test)
  apply (unfold test_class_def)
  apply (drule method_rec_lemma [OF _ wf_subcls1_E])
  apply simp
  done

lemma field_val [simp]:
  "field (E, list_name) val_name = Some (list_name, PrimT Integer)"
  apply (unfold TypeRel.field_def)
  apply (insert class_list)
  apply (unfold list_class_def)
  apply (drule fields_rec_lemma [OF _ wf_subcls1_E])
  apply simp
  done

lemma field_next [simp]:
  "field (E, list_name) next_name = Some (list_name, Class list_name)"
  apply (unfold TypeRel.field_def)
  apply (insert class_list)
  apply (unfold list_class_def)
  apply (drule fields_rec_lemma [OF _ wf_subcls1_E])
  apply (simp add: name_defs distinct_fields [symmetric])
  done

lemma [simp]: "fields (E, Object) = []"
   by (simp add: fields_rec_lemma [OF class_Object wf_subcls1_E])
 
lemma [simp]: "fields (E, Xcpt NullPointer) = []"
  by (simp add: fields_rec_lemma [OF class_NullPointer wf_subcls1_E])

lemma [simp]: "fields (E, Xcpt ClassCast) = []"
  by (simp add: fields_rec_lemma [OF class_ClassCast wf_subcls1_E])

lemma [simp]: "fields (E, Xcpt OutOfMemory) = []"
  by (simp add: fields_rec_lemma [OF class_OutOfMemory wf_subcls1_E])

lemma [simp]: "fields (E, test_name) = []"
  apply (insert class_test)
  apply (unfold test_class_def)
  apply (drule fields_rec_lemma [OF _ wf_subcls1_E])
  apply simp
  done

lemmas [simp] = is_class_def

text {*
  The next definition and three proof rules implement an algorithm to
  enumarate natural numbers. The command @{text "apply (elim pc_end pc_next pc_0"} 
  transforms a goal of the form
  @{prop [display] "pc < n \<Longrightarrow> P pc"} 
  into a series of goals
  @{prop [display] "P 0"} 
  @{prop [display] "P (Suc 0)"} 

  @{text "\<dots>"}

  @{prop [display] "P n"} 
*}
definition intervall :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" ("_ \<in> [_, _')") where
  "x \<in> [a, b) \<equiv> a \<le> x \<and> x < b"

lemma pc_0: "x < n \<Longrightarrow> (x \<in> [0, n) \<Longrightarrow> P x) \<Longrightarrow> P x"
  by (simp add: intervall_def)

lemma pc_next: "x \<in> [n0, n) \<Longrightarrow> P n0 \<Longrightarrow> (x \<in> [Suc n0, n) \<Longrightarrow> P x) \<Longrightarrow> P x"
  apply (cases "x=n0")
  apply (auto simp add: intervall_def)
  done

lemma pc_end: "x \<in> [n,n) \<Longrightarrow> P x" 
  by (unfold intervall_def) arith


section "Program structure"

text {*
  The program is structurally wellformed:
*}

lemma wf_struct:
  "wf_prog (\<lambda>G C mb. True) E" (is "wf_prog ?mb E")
proof -
  have "unique E" 
    by (simp add: system_defs E_def class_defs name_defs distinct_classes)
  moreover
  have "set SystemClasses \<subseteq> set E" by (simp add: system_defs E_def)
  hence "wf_syscls E" by (rule wf_syscls)
  moreover
  have "wf_cdecl ?mb E ObjectC" by (simp add: wf_cdecl_def ObjectC_def)
  moreover
  have "wf_cdecl ?mb E NullPointerC" 
    by (auto elim: notin_rtrancl 
            simp add: wf_cdecl_def name_defs NullPointerC_def subcls1)
  moreover
  have "wf_cdecl ?mb E ClassCastC" 
    by (auto elim: notin_rtrancl 
            simp add: wf_cdecl_def name_defs ClassCastC_def subcls1)
  moreover
  have "wf_cdecl ?mb E OutOfMemoryC" 
    by (auto elim: notin_rtrancl 
            simp add: wf_cdecl_def name_defs OutOfMemoryC_def subcls1)
  moreover
  have "wf_cdecl ?mb E (list_name, list_class)"
    apply (auto elim!: notin_rtrancl 
            simp add: wf_cdecl_def wf_fdecl_def list_class_def 
                      wf_mdecl_def wf_mhead_def subcls1)
    apply (auto simp add: name_defs distinct_classes distinct_fields)
    done    
  moreover
  have "wf_cdecl ?mb E (test_name, test_class)" 
    apply (auto elim!: notin_rtrancl 
            simp add: wf_cdecl_def wf_fdecl_def test_class_def 
                      wf_mdecl_def wf_mhead_def subcls1)
    apply (auto simp add: name_defs distinct_classes distinct_fields)
    done       
  ultimately
  show ?thesis 
    by (simp add: wf_prog_def ws_prog_def wf_cdecl_mrT_cdecl_mdecl E_def SystemClasses_def)
qed

section "Welltypings"
text {*
  We show welltypings of the methods @{term append_name} in class @{term list_name}, 
  and @{term makelist_name} in class @{term test_name}:
*}
lemmas eff_simps [simp] = eff_def norm_eff_def xcpt_eff_def
declare appInvoke [simp del]

definition phi_append :: method_type ("\<phi>\<^sub>a") where
  "\<phi>\<^sub>a \<equiv> map (\<lambda>(x,y). Some (x, map OK y)) [ 
   (                                    [], [Class list_name, Class list_name]),
   (                     [Class list_name], [Class list_name, Class list_name]),
   (                     [Class list_name], [Class list_name, Class list_name]),
   (    [Class list_name, Class list_name], [Class list_name, Class list_name]),
   ([NT, Class list_name, Class list_name], [Class list_name, Class list_name]),
   (                     [Class list_name], [Class list_name, Class list_name]),
   (    [Class list_name, Class list_name], [Class list_name, Class list_name]),
   (                          [PrimT Void], [Class list_name, Class list_name]),
   (                        [Class Object], [Class list_name, Class list_name]),
   (                                    [], [Class list_name, Class list_name]),
   (                     [Class list_name], [Class list_name, Class list_name]),
   (    [Class list_name, Class list_name], [Class list_name, Class list_name]),
   (                                    [], [Class list_name, Class list_name]),
   (                          [PrimT Void], [Class list_name, Class list_name])]"


lemma bounded_append [simp]:
  "check_bounded append_ins [(Suc 0, 2, 8, Xcpt NullPointer)]"
  apply (simp add: check_bounded_def)
  apply (simp add: eval_nat_numeral append_ins_def)
  apply (rule allI, rule impI)
  apply (elim pc_end pc_next pc_0)
  apply auto
  done

lemma types_append [simp]: "check_types E 3 (Suc (Suc 0)) (map OK \<phi>\<^sub>a)"
  apply (auto simp add: check_types_def phi_append_def JVM_states_unfold)
  apply (unfold list_def)
  apply auto
  done
  
lemma wt_append [simp]:
  "wt_method E list_name [Class list_name] (PrimT Void) 3 0 append_ins
             [(Suc 0, 2, 8, Xcpt NullPointer)] \<phi>\<^sub>a"
  apply (simp add: wt_method_def wt_start_def wt_instr_def)
  apply (simp add: phi_append_def append_ins_def)
  apply clarify
  apply (elim pc_end pc_next pc_0)
  apply simp
  apply (fastforce simp add: match_exception_entry_def sup_state_conv subcls1)
  apply simp
  apply simp
  apply (fastforce simp add: sup_state_conv subcls1)
  apply simp
  apply (simp add: app_def xcpt_app_def)
  apply simp
  apply simp
  apply simp
  apply (simp add: match_exception_entry_def)
  apply (simp add: match_exception_entry_def)
  apply simp
  apply simp
  done

text {* Some abbreviations for readability *} 
abbreviation Clist :: ty 
  where "Clist == Class list_name"
abbreviation Ctest :: ty
  where "Ctest == Class test_name"

definition phi_makelist :: method_type ("\<phi>\<^sub>m") where
  "\<phi>\<^sub>m \<equiv> map (\<lambda>(x,y). Some (x, y)) [ 
    (                                   [], [OK Ctest, Err     , Err     ]),
    (                              [Clist], [OK Ctest, Err     , Err     ]),
    (                       [Clist, Clist], [OK Ctest, Err     , Err     ]),
    (                              [Clist], [OK Clist, Err     , Err     ]),
    (               [PrimT Integer, Clist], [OK Clist, Err     , Err     ]),
    (                                   [], [OK Clist, Err     , Err     ]),
    (                              [Clist], [OK Clist, Err     , Err     ]),
    (                       [Clist, Clist], [OK Clist, Err     , Err     ]),
    (                              [Clist], [OK Clist, OK Clist, Err     ]),
    (               [PrimT Integer, Clist], [OK Clist, OK Clist, Err     ]),
    (                                   [], [OK Clist, OK Clist, Err     ]),
    (                              [Clist], [OK Clist, OK Clist, Err     ]),
    (                       [Clist, Clist], [OK Clist, OK Clist, Err     ]),
    (                              [Clist], [OK Clist, OK Clist, OK Clist]),
    (               [PrimT Integer, Clist], [OK Clist, OK Clist, OK Clist]),
    (                                   [], [OK Clist, OK Clist, OK Clist]),
    (                              [Clist], [OK Clist, OK Clist, OK Clist]),
    (                       [Clist, Clist], [OK Clist, OK Clist, OK Clist]),
    (                         [PrimT Void], [OK Clist, OK Clist, OK Clist]),
    (                                   [], [OK Clist, OK Clist, OK Clist]),
    (                              [Clist], [OK Clist, OK Clist, OK Clist]),
    (                       [Clist, Clist], [OK Clist, OK Clist, OK Clist]),
    (                         [PrimT Void], [OK Clist, OK Clist, OK Clist])]"

lemma bounded_makelist [simp]: "check_bounded make_list_ins []"
  apply (simp add: check_bounded_def)
  apply (simp add: eval_nat_numeral make_list_ins_def)
  apply (rule allI, rule impI)
  apply (elim pc_end pc_next pc_0)
  apply auto
  done

lemma types_makelist [simp]: "check_types E 3 (Suc (Suc (Suc 0))) (map OK \<phi>\<^sub>m)"
  apply (auto simp add: check_types_def phi_makelist_def JVM_states_unfold)
  apply (unfold list_def)
  apply auto
  done

lemma wt_makelist [simp]:
  "wt_method E test_name [] (PrimT Void) 3 2 make_list_ins [] \<phi>\<^sub>m"
  apply (simp add: wt_method_def)
  apply (simp add: make_list_ins_def phi_makelist_def)
  apply (simp add: wt_start_def eval_nat_numeral)
  apply (simp add: wt_instr_def)
  apply clarify
  apply (elim pc_end pc_next pc_0)
  apply (simp add: match_exception_entry_def)
  apply simp
  apply simp
  apply simp
  apply (simp add: match_exception_entry_def)
  apply (simp add: match_exception_entry_def) 
  apply simp
  apply simp
  apply simp
  apply (simp add: match_exception_entry_def)
  apply (simp add: match_exception_entry_def) 
  apply simp
  apply simp
  apply simp
  apply (simp add: match_exception_entry_def)
  apply (simp add: match_exception_entry_def) 
  apply simp
  apply (simp add: app_def xcpt_app_def)
  apply simp 
  apply simp
  apply simp
  apply (simp add: app_def xcpt_app_def) 
  apply simp
  done

text {* The whole program is welltyped: *}
definition Phi :: prog_type ("\<Phi>") where
  "\<Phi> C sg \<equiv> if C = test_name \<and> sg = (makelist_name, []) then \<phi>\<^sub>m else          
             if C = list_name \<and> sg = (append_name, [Class list_name]) then \<phi>\<^sub>a else []"

lemma wf_prog:
  "wt_jvm_prog E \<Phi>" 
  apply (unfold wt_jvm_prog_def)
  apply (rule wf_mb'E [OF wf_struct])
  apply (simp add: E_def)
  apply clarify
  apply (fold E_def)
  apply (simp add: system_defs class_defs Phi_def) 
  apply auto
  done 


section "Conformance"
text {* Execution of the program will be typesafe, because its
  start state conforms to the welltyping: *}

lemma "E,\<Phi> \<turnstile>JVM start_state E test_name makelist_name \<surd>"
  apply (rule BV_correct_initial)
    apply (rule wf_prog)
   apply simp
  apply simp
  done


section "Example for code generation: inferring method types"

definition test_kil :: "jvm_prog \<Rightarrow> cname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
             exception_table \<Rightarrow> instr list \<Rightarrow> JVMType.state list" where
  "test_kil G C pTs rT mxs mxl et instr =
   (let first  = Some ([],(OK (Class C))#((map OK pTs))@(replicate mxl Err));
        start  = OK first#(replicate (size instr - 1) (OK None))
    in  kiljvm G mxs (1+size pTs+mxl) rT et instr start)"

lemma [code]:
  "unstables r step ss = 
   foldr (\<lambda>p A. if \<not>stable r step ss p then insert p A else A) [0..<size ss] {}"
proof -
  have "unstables r step ss = (UN p:{..<size ss}. if \<not>stable r step ss p then {p} else {})"
    apply (unfold unstables_def)
    apply (rule equalityI)
    apply (rule subsetI)
    apply (erule CollectE)
    apply (erule conjE)
    apply (rule UN_I)
    apply simp
    apply simp
    apply (rule subsetI)
    apply (erule UN_E)
    apply (case_tac "\<not> stable r step ss p")
    apply simp+
    done
  also have "\<And>f. (UN p:{..<size ss}. f p) = Union (set (map f [0..<size ss]))" by auto
  also note Sup_set_foldr also note foldr_map
  also have "op \<union> \<circ> (\<lambda>p. if \<not> stable r step ss p then {p} else {}) = 
            (\<lambda>p A. if \<not>stable r step ss p then insert p A else A)"
    by(auto simp add: fun_eq_iff)
  finally show ?thesis .
qed

definition some_elem :: "'a set \<Rightarrow> 'a" where [code del]:
  "some_elem = (%S. SOME x. x : S)"
code_const some_elem
  (SML "(case/ _ of/ Set/ xs/ =>/ hd/ xs)")
setup {* Code.add_signature_cmd ("some_elem", "'a set \<Rightarrow> 'a") *}

text {* This code setup is just a demonstration and \emph{not} sound! *}

lemma False
proof -
  have "some_elem (set [False, True]) = False"
    by eval
  moreover have "some_elem (set [True, False]) = True"
    by eval
  ultimately show False
    by (simp add: some_elem_def)
qed

lemma [code]:
  "iter f step ss w = while (\<lambda>(ss, w). \<not> More_Set.is_empty w)
    (\<lambda>(ss, w).
        let p = some_elem w in propa f (step p (ss ! p)) ss (w - {p}))
    (ss, w)"
  unfolding iter_def More_Set.is_empty_def some_elem_def ..

lemma JVM_sup_unfold [code]:
 "JVMType.sup S m n = lift2 (Opt.sup
       (Product.sup (Listn.sup (JType.sup S))
         (\<lambda>x y. OK (map2 (lift2 (JType.sup S)) x y))))" 
  apply (unfold JVMType.sup_def JVMType.sl_def Opt.esl_def Err.sl_def
         stk_esl_def reg_sl_def Product.esl_def  
         Listn.sl_def upto_esl_def JType.esl_def Err.esl_def) 
  by simp

lemmas [code] = JType.sup_def [unfolded exec_lub_def] JVM_le_unfold
lemmas [code] = lesub_def plussub_def

setup {*
  Code.add_signature_cmd ("More_Set.is_empty", "'a set \<Rightarrow> bool")
  #> Code.add_signature_cmd ("propa", "('s \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> (nat \<times> 's) list \<Rightarrow> 's list \<Rightarrow> nat set \<Rightarrow> 's list * nat set") 
  #> Code.add_signature_cmd 
     ("iter", "('s \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> (nat \<times> 's) list) \<Rightarrow> 's list \<Rightarrow> nat set \<Rightarrow> 's list * nat set")
  #> Code.add_signature_cmd ("unstables", "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> (nat \<times> 's) list) \<Rightarrow> 's list \<Rightarrow> nat set") 
*}

lemmas [code] =
  JType.sup_def [unfolded exec_lub_def]
  wf_class_code
  widen.equation
  match_exception_entry_def

definition test1 where
  "test1 = test_kil E list_name [Class list_name] (PrimT Void) 3 0
    [(Suc 0, 2, 8, Xcpt NullPointer)] append_ins"
definition test2 where
  "test2 = test_kil E test_name [] (PrimT Void) 3 2 [] make_list_ins"

ML {* 
  @{code test1}; 
  @{code test2};
*}

end

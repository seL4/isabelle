(*  Title:      HOL/MicroJava/BV/BVExample.thy
    ID:         $Id$
    Author:     Gerwin Klein
*)

header {* \isaheader{Example Welltypings}\label{sec:BVExample} *}

theory BVExample = JVMListExample + Correct:

text {*
  This theory shows type correctness of the example program in section 
  \ref{sec:JVMListExample} (p. \pageref{sec:JVMListExample}) by
  explicitly providing a welltyping. It also shows that the start
  state of the program conforms to the welltyping; hence type safe
  execution is guaranteed.
*}

section "Setup"
text {*
  Since the types @{typ cnam}, @{text vnam}, and @{text mname} are 
  anonymous, we describe distinctness of names in the example by axioms:
*}
axioms 
  distinct_classes: "list_nam \<noteq> test_nam"
  distinct_fields:  "val_nam \<noteq> next_nam"

text {* Shorthands for definitions we will have to use often in the
proofs below: *}
lemmas name_defs   = list_name_def test_name_def val_name_def next_name_def
lemmas system_defs = SystemClasses_def ObjectC_def NullPointerC_def 
                     OutOfMemoryC_def ClassCastC_def
lemmas class_defs  = list_class_def test_class_def

text {* These auxiliary proofs are for efficiency: class lookup,
subclass relation, method and field lookup are computed only once:
*}
lemma class_Object [simp]:
  "class E Object = Some (arbitrary, [],[])"
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
  apply (auto split: split_if_asm)
  done

text {* The subclass relation is acyclic; hence its converse is well founded: *}
lemma notin_rtrancl:
  "(a,b) \<in> r\<^sup>* \<Longrightarrow> a \<noteq> b \<Longrightarrow> (\<And>y. (a,y) \<notin> r) \<Longrightarrow> False"
  by (auto elim: converse_rtranclE)  

lemma acyclic_subcls1_E: "acyclic (subcls1 E)"
  apply (rule acyclicI)
  apply (simp add: subcls1)
  apply (auto dest!: tranclD)
  apply (auto elim!: notin_rtrancl simp add: name_defs distinct_classes)
  done

lemma wf_subcls1_E: "wf ((subcls1 E)\<inverse>)"
  apply (rule finite_acyclic_wf_converse)
  apply (simp add: subcls1)
  apply (rule acyclic_subcls1_E)
  done  

text {* Method and field lookup: *}
lemma method_Object [simp]:
  "method (E, Object) = empty"
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
  apply (unfold field_def)
  apply (insert class_list)
  apply (unfold list_class_def)
  apply (drule fields_rec_lemma [OF _ wf_subcls1_E])
  apply simp
  done

lemma field_next [simp]:
  "field (E, list_name) next_name = Some (list_name, Class list_name)"
  apply (unfold field_def)
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
constdefs 
  intervall :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" ("_ \<in> [_, _')")
  "x \<in> [a, b) \<equiv> a \<le> x \<and> x < b"

lemma pc_0: "x < n \<Longrightarrow> (x \<in> [0, n) \<Longrightarrow> P x) \<Longrightarrow> P x"
  by (simp add: intervall_def)

lemma pc_next: "x \<in> [n0, n) \<Longrightarrow> P n0 \<Longrightarrow> (x \<in> [Suc n0, n) \<Longrightarrow> P x) \<Longrightarrow> P x"
  apply (cases "x=n0")
  apply (auto simp add: intervall_def) 
  apply arith
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
  show ?thesis by (simp add: wf_prog_def E_def SystemClasses_def)
qed

section "Welltypings"
text {*
  We show welltypings of the methods @{term append_name} in class @{term list_name}, 
  and @{term makelist_name} in class @{term test_name}:
*}
lemmas eff_simps [simp] = eff_def norm_eff_def xcpt_eff_def
declare appInvoke [simp del]

constdefs
  phi_append :: method_type ("\<phi>\<^sub>a")
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

lemma wt_append [simp]:
  "wt_method E list_name [Class list_name] (PrimT Void) 3 0 append_ins
             [(Suc 0, 2, 8, Xcpt NullPointer)] \<phi>\<^sub>a"
  apply (simp add: wt_method_def append_ins_def phi_append_def 
                   wt_start_def wt_instr_def)
  apply clarify
  apply (elim pc_end pc_next pc_0)
  apply simp
  apply (fastsimp simp add: match_exception_entry_def sup_state_conv subcls1)
  apply simp
  apply simp
  apply (fastsimp simp add: sup_state_conv subcls1)
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
syntax
  list :: ty 
  test :: ty
translations
  "list" == "Class list_name"
  "test" == "Class test_name"

constdefs
  phi_makelist :: method_type ("\<phi>\<^sub>m")
  "\<phi>\<^sub>m \<equiv> map (\<lambda>(x,y). Some (x, y)) [ 
    (                                   [], [OK test, Err    , Err    ]),
    (                               [list], [OK test, Err    , Err    ]),
    (                         [list, list], [OK test, Err    , Err    ]),
    (                               [list], [OK list, Err    , Err    ]),
    (                [PrimT Integer, list], [OK list, Err    , Err    ]),
    (                                   [], [OK list, Err    , Err    ]),
    (                               [list], [OK list, Err    , Err    ]),
    (                         [list, list], [OK list, Err    , Err    ]),
    (                               [list], [OK list, OK list, Err    ]),
    (                [PrimT Integer, list], [OK list, OK list, Err    ]),
    (                                   [], [OK list, OK list, Err    ]),
    (                               [list], [OK list, OK list, Err    ]),
    (                         [list, list], [OK list, OK list, Err    ]),
    (                               [list], [OK list, OK list, OK list]),
    (                [PrimT Integer, list], [OK list, OK list, OK list]),
    (                                   [], [OK list, OK list, OK list]),
    (                               [list], [OK list, OK list, OK list]),
    (                         [list, list], [OK list, OK list, OK list]),
    (                         [PrimT Void], [OK list, OK list, OK list]),
    (                   [list, PrimT Void], [OK list, OK list, OK list]),
    (             [list, list, PrimT Void], [OK list, OK list, OK list]),
    (             [PrimT Void, PrimT Void], [OK list, OK list, OK list]),
    ( [PrimT Void, PrimT Void, PrimT Void], [OK list, OK list, OK list])]"

lemma wt_makelist [simp]:
  "wt_method E test_name [] (PrimT Void) 3 2 make_list_ins [] \<phi>\<^sub>m"
  apply (simp add: wt_method_def make_list_ins_def phi_makelist_def)
  apply (simp add: wt_start_def nat_number)
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
  apply (simp add: app_def xcpt_app_def)
  apply simp
  apply simp
  done

text {* The whole program is welltyped: *}
constdefs 
  Phi :: prog_type ("\<Phi>")
  "\<Phi> C sig \<equiv> if C = test_name \<and> sig = (makelist_name, []) then \<phi>\<^sub>m else
              if C = list_name \<and> sig = (append_name, [Class list_name]) then \<phi>\<^sub>a else []"
  
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

lemma [simp]: "preallocated start_heap"
  apply (unfold start_heap_def preallocated_def)
  apply auto
  apply (case_tac x)
  apply auto
  done

lemma "E,\<Phi> \<turnstile>JVM start_state \<surd>"
  apply (simp add: correct_state_def start_state_def test_class_def)
  apply (simp add: hconf_def start_heap_def oconf_def lconf_def)
  apply (simp add: Phi_def phi_makelist_def)
  apply (simp add: correct_frame_def)
  apply (simp add: make_list_ins_def)
  apply (simp add: conf_def start_heap_def)
  done

end

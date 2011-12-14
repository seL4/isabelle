(*  Title:      HOL/MicroJava/JVM/JVMListExample.thy
    Author:     Stefan Berghofer
*)

header {* \isaheader{Example for generating executable code from JVM semantics}\label{sec:JVMListExample} *}

theory JVMListExample
imports "../J/SystemClasses" JVMExec
begin

text {*
  Since the types @{typ cnam}, @{text vnam}, and @{text mname} are 
  anonymous, we describe distinctness of names in the example by axioms:
*}
axiomatization list_nam test_nam :: cnam
  where distinct_classes: "list_nam \<noteq> test_nam"

axiomatization append_name makelist_name :: mname
  where distinct_methods: "append_name \<noteq> makelist_name"

axiomatization val_nam next_nam :: vnam
  where distinct_fields: "val_nam \<noteq> next_nam"

axiomatization
  where nat_to_loc'_inject: "nat_to_loc' l = nat_to_loc' l' \<longleftrightarrow> l = l'"

definition list_name :: cname
  where "list_name = Cname list_nam"
  
definition test_name :: cname
  where "test_name = Cname test_nam"

definition val_name :: vname
  where "val_name = VName val_nam"

definition next_name :: vname
  where "next_name = VName next_nam"

definition append_ins :: bytecode where
  "append_ins =
       [Load 0,
        Getfield next_name list_name,
        Dup,
        LitPush Null,
        Ifcmpeq 4,
        Load 1,       
        Invoke list_name append_name [Class list_name],
        Return,
        Pop,
        Load 0,
        Load 1,
        Putfield next_name list_name,
        LitPush Unit,
        Return]"

definition list_class :: "jvm_method class" where
  "list_class =
    (Object,
     [(val_name, PrimT Integer), (next_name, Class list_name)],
     [((append_name, [Class list_name]), PrimT Void,
        (3, 0, append_ins,[(1,2,8,Xcpt NullPointer)]))])"

definition make_list_ins :: bytecode where
  "make_list_ins =
       [New list_name,
        Dup,
        Store 0,
        LitPush (Intg 1),
        Putfield val_name list_name,
        New list_name,
        Dup,
        Store 1,
        LitPush (Intg 2),
        Putfield val_name list_name,
        New list_name,
        Dup,
        Store 2,
        LitPush (Intg 3),
        Putfield val_name list_name,
        Load 0,
        Load 1,
        Invoke list_name append_name [Class list_name],
        Pop,
        Load 0,
        Load 2,
        Invoke list_name append_name [Class list_name],
        Return]"

definition test_class :: "jvm_method class" where
  "test_class =
    (Object, [],
     [((makelist_name, []), PrimT Void, (3, 2, make_list_ins,[]))])"

definition E :: jvm_prog where
  "E = SystemClasses @ [(list_name, list_class), (test_name, test_class)]"

code_datatype list_nam test_nam
lemma equal_cnam_code [code]:
  "HOL.equal list_nam list_nam \<longleftrightarrow> True"
  "HOL.equal test_nam test_nam \<longleftrightarrow> True"
  "HOL.equal list_nam test_nam \<longleftrightarrow> False"
  "HOL.equal test_nam list_nam \<longleftrightarrow> False"
  by(simp_all add: distinct_classes distinct_classes[symmetric] equal_cnam_def)

code_datatype append_name makelist_name
lemma equal_mname_code [code]: 
  "HOL.equal append_name append_name \<longleftrightarrow> True"
  "HOL.equal makelist_name makelist_name \<longleftrightarrow> True"
  "HOL.equal append_name makelist_name \<longleftrightarrow> False"
  "HOL.equal makelist_name append_name \<longleftrightarrow> False"
  by(simp_all add: distinct_methods distinct_methods[symmetric] equal_mname_def)

code_datatype val_nam next_nam
lemma equal_vnam_code [code]: 
  "HOL.equal val_nam val_nam \<longleftrightarrow> True"
  "HOL.equal next_nam next_nam \<longleftrightarrow> True"
  "HOL.equal val_nam next_nam \<longleftrightarrow> False"
  "HOL.equal next_nam val_nam \<longleftrightarrow> False"
  by(simp_all add: distinct_fields distinct_fields[symmetric] equal_vnam_def)


lemma equal_loc'_code [code]:
  "HOL.equal (nat_to_loc' l) (nat_to_loc' l') \<longleftrightarrow> l = l'"
  by(simp add: equal_loc'_def nat_to_loc'_inject)

definition undefined_cname :: cname 
  where [code del]: "undefined_cname = undefined"
code_datatype Object Xcpt Cname undefined_cname
declare undefined_cname_def[symmetric, code_unfold]

definition undefined_val :: val
  where [code del]: "undefined_val = undefined"
declare undefined_val_def[symmetric, code_unfold]
code_datatype Unit Null Bool Intg Addr undefined_val

definition
  "test = exec (E, start_state E test_name makelist_name)"

ML {*
  @{code test}; 
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
  @{code exec} (@{code E}, @{code the} it);
*}

end

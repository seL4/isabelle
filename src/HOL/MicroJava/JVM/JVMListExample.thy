(*  Title:      HOL/MicroJava/JVM/JVMListExample.thy
    ID:         $Id$
    Author:     Stefan Berghofer
*)

header {* \isaheader{Example for generating executable code from JVM semantics}\label{sec:JVMListExample} *}

theory JVMListExample imports SystemClasses JVMExec begin

consts
  list_nam :: cnam
  test_nam :: cnam
  append_name :: mname
  makelist_name :: mname
  val_nam :: vnam
  next_nam :: vnam

constdefs
  list_name :: cname
  "list_name == Cname list_nam"
  
  test_name :: cname
  "test_name == Cname test_nam"

  val_name :: vname
  "val_name == VName val_nam"

  next_name :: vname
  "next_name == VName next_nam"

  append_ins :: bytecode
  "append_ins == 
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

  list_class :: "jvm_method class"
  "list_class ==
    (Object,
     [(val_name, PrimT Integer), (next_name, Class list_name)],
     [((append_name, [Class list_name]), PrimT Void,
        (3, 0, append_ins,[(1,2,8,Xcpt NullPointer)]))])"

  make_list_ins :: bytecode
  "make_list_ins ==
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

  test_class :: "jvm_method class"
  "test_class ==
    (Object, [],
     [((makelist_name, []), PrimT Void, (3, 2, make_list_ins,[]))])"

  E :: jvm_prog
  "E == SystemClasses @ [(list_name, list_class), (test_name, test_class)]"


types_code
  cnam ("string")
  vnam ("string")
  mname ("string")
  loc_ ("int")

consts_code
  "new_Addr" ("\<module>new'_addr {* %x. case x of None => True | Some y => False *}/ {* None *}/ {* Loc *}")
attach {*
fun new_addr p none loc hp =
  let fun nr i = if p (hp (loc i)) then (loc i, none) else nr (i+1);
  in nr 0 end;
*}

  "arbitrary" ("(raise Match)")
  "arbitrary :: val" ("{* Unit *}")
  "arbitrary :: cname" ("{* Object *}")

  "list_nam" ("\"list\"")
  "test_nam" ("\"test\"")
  "append_name" ("\"append\"")
  "makelist_name" ("\"makelist\"")
  "val_nam" ("\"val\"")
  "next_nam" ("\"next\"")

code_type cnam and vnam and mname and loc_
  (SML "string" and "string" and "string" and "IntInf.int")

instance cnam :: eq
  and cname :: eq
  and vname :: eq
  and mname :: eq
  and ty :: eq
  and val :: eq
  and instr :: eq ..

definition
  arbitrary_val :: val where
  [symmetric, code inline]: "arbitrary_val = arbitrary"
definition
  arbitrary_cname :: cname where
  [symmetric, code inline]: "arbitrary_cname = arbitrary"

definition "unit' = Unit"
definition "object' = Object"

code_axioms
  arbitrary_val \<equiv> unit'
  arbitrary_cname \<equiv> object'

code_const list_nam and test_nam and append_name and makelist_name and val_nam and next_nam
  (SML "\"list\"" and "\"test\"" and "\"append\""
    and "\"makelist\"" and "\"val\"" and "\"next\"")

axiomatization
  incr_loc :: "loc_ \<Rightarrow> loc_"
  and zero_loc :: "loc_"

code_const incr_loc and zero_loc
  (SML "(op +)/ (_, 1)" and "0")

axiomatization
  test_loc :: "(loc_ \<Rightarrow> bool) \<Rightarrow> (loc_ \<Rightarrow> 'a) \<Rightarrow> loc_ \<Rightarrow> 'a" where
  "test_loc p v l = (if p l then v l else test_loc p v (incr l))"

definition
  new_addr' :: "(loc \<Rightarrow> (cname \<times> (vname \<times> cname \<Rightarrow> val option)) option) \<Rightarrow> loc \<times> val option" where
  "new_addr' hp =
    test_loc (\<lambda>i. hp (Loc i) = None) (\<lambda>i. (Loc i, None)) zero_loc"

lemma [code func]:
  "wf_class = wf_class" ..

code_const
  wf_class (SML "(fn `_ => true)")

code_axioms
  new_Addr \<equiv> new_addr'

definition
  "test = exec (E, start_state E test_name makelist_name)"


subsection {* Single step execution *}

code_module JVM
contains
  test = "exec (E, start_state E test_name makelist_name)"

ML {* JVM.test *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}

end

(*  Title:      HOL/MicroJava/JVM/JVMListExample.thy
    Author:     Stefan Berghofer
*)

header {* \isaheader{Example for generating executable code from JVM semantics}\label{sec:JVMListExample} *}

theory JVMListExample
imports "../J/SystemClasses" JVMExec
begin

consts
  list_nam :: cnam
  test_nam :: cnam
  append_name :: mname
  makelist_name :: mname
  val_nam :: vnam
  next_nam :: vnam

definition list_name :: cname where
  "list_name == Cname list_nam"
  
definition test_name :: cname where
  "test_name == Cname test_nam"

definition val_name :: vname where
  "val_name == VName val_nam"

definition next_name :: vname where
  "next_name == VName next_nam"

definition append_ins :: bytecode where
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

definition list_class :: "jvm_method class" where
  "list_class ==
    (Object,
     [(val_name, PrimT Integer), (next_name, Class list_name)],
     [((append_name, [Class list_name]), PrimT Void,
        (3, 0, append_ins,[(1,2,8,Xcpt NullPointer)]))])"

definition make_list_ins :: bytecode where
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

definition test_class :: "jvm_method class" where
  "test_class ==
    (Object, [],
     [((makelist_name, []), PrimT Void, (3, 2, make_list_ins,[]))])"

definition E :: jvm_prog where
  "E == SystemClasses @ [(list_name, list_class), (test_name, test_class)]"


types_code
  cnam ("string")
  vnam ("string")
  mname ("string")
  loc' ("int")

consts_code
  "new_Addr" ("\<module>new'_addr {* %x. case x of None => True | Some y => False *}/ {* None *}/ {* Loc *}")
attach {*
fun new_addr p none loc hp =
  let fun nr i = if p (hp (loc i)) then (loc i, none) else nr (i+1);
  in nr 0 end;
*}

  "undefined" ("(raise Match)")
  "undefined :: val" ("{* Unit *}")
  "undefined :: cname" ("{* Object *}")

  "list_nam" ("\"list\"")
  "test_nam" ("\"test\"")
  "append_name" ("\"append\"")
  "makelist_name" ("\"makelist\"")
  "val_nam" ("\"val\"")
  "next_nam" ("\"next\"")

definition
  "test = exec (E, start_state E test_name makelist_name)"


subsection {* Single step execution *}

code_module JVM
contains
  exec = exec
  test = test

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

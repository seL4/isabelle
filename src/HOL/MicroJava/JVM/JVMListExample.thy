(*  Title:      HOL/MicroJava/JVM/JVMListExample.thy
    ID:         $Id$
    Author:     Stefan Berghofer
*)

header {* \isaheader{Example for generating executable code from JVM semantics}\label{sec:JVMListExample} *}

theory JVMListExample = SystemClasses + JVMExec:

consts
  list_nam :: cnam
  test_nam :: cnam
  append_name :: mname
  makelist_name :: mname
  val_nam :: vnam
  next_nam :: vnam
  test_name_loc :: loc_

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
        Load 0,
        Load 2,
        Invoke list_name append_name [Class list_name],
        LitPush Unit,
        Return]"

  test_class :: "jvm_method class"
  "test_class ==
    (Object, [],
     [((makelist_name, []), PrimT Void, (3, 2, make_list_ins,[]))])"

  E :: jvm_prog
  "E == SystemClasses @ [(list_name, list_class), (test_name, test_class)]"

  start_heap :: aheap
  "start_heap == empty (XcptRef NullPointer \<mapsto> (Xcpt NullPointer, empty))
                       (XcptRef ClassCast \<mapsto> (Xcpt ClassCast, empty))
                       (XcptRef OutOfMemory \<mapsto> (Xcpt OutOfMemory, empty))
                       (Loc test_name_loc \<mapsto> (test_name, empty))"

  start_state :: jvm_state
  "start_state ==
    (None, start_heap, [([], [Addr (Loc test_name_loc), arbitrary, arbitrary], test_name, (makelist_name, []), 0)])"

types_code
  cnam ("string")
  vnam ("string")
  mname ("string")
  loc_ ("int")

consts_code
  "new_Addr" ("new'_addr {* %x. case x of None => True | Some y => False *}/ {* None *}/ {* Loc *}")

  "wf" ("true?")

  "arbitrary" ("(raise ERROR)")
  "arbitrary" :: "val" ("{* Unit *}")
  "arbitrary" :: "cname" ("Object")

  "test_name_loc" ("0")

  "list_nam" ("\"list\"")
  "test_nam" ("\"test\"")
  "append_name" ("\"append\"")
  "makelist_name" ("\"makelist\"")
  "val_nam" ("\"val\"")
  "next_nam" ("\"next\"")

ML {*
fun new_addr p none loc hp =
  let fun nr i = if p (hp (loc i)) then (loc i, none) else nr (i+1);
  in nr 0 end;
*}

subsection {* Single step execution *}

generate_code 
  test = "exec (E, start_state)"

ML {* test *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}
ML {* exec (E, the it) *}

end

(*  Title:      HOL/MicroJava/JVM/JVMListExample.thy
    ID:         $Id$
    Author:     Stefan Berghofer
*)

header {* Example for generating executable code from JVM semantics *}

theory JVMListExample = JVMExec:

consts
  list_name :: cname
  test_name :: cname
  append_name :: mname
  makelist_name :: mname
  val_nam :: vnam
  next_nam :: vnam

constdefs
  val_name :: vname
  "val_name == VName val_nam"

  next_name :: vname
  "next_name == VName next_nam"

  list_class :: "(nat * nat * bytecode) class"
  "list_class ==
    (Object,
     [(val_name, PrimT Integer), (next_name, RefT (ClassT list_name))],
     [((append_name, [RefT (ClassT list_name)]), PrimT Integer,
      (0, 0,
       [Load 0,
        Getfield next_name list_name,
        Dup,
        LitPush Null,
        Ifcmpeq 4,
        Load 1,
        Invoke list_name append_name [RefT (ClassT list_name)],
        Return,
        Pop,
        Load 0,
        Load 1,
        Putfield next_name list_name,
        LitPush Unit,
        Return]))])"

  test_class :: "(nat * nat * bytecode) class"
  "test_class ==
    (Object, [],
     [((makelist_name, []), PrimT Integer,
      (0, 3,
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
        Invoke list_name append_name [RefT (ClassT list_name)],
        Load 0,
        Load 2,
        Invoke list_name append_name [RefT (ClassT list_name)],
        LitPush Unit,
        Return]))])"

  example_prg :: jvm_prog
  "example_prg == [ObjectC, (list_name, list_class), (test_name, test_class)]"

  start_state :: jvm_state
  "start_state ==
    (None, empty, [([], Unit # Unit # Unit # [], test_name, (makelist_name, []), 0)])"

types_code
  cname ("string")
  vnam ("string")
  mname ("string")
  loc ("int")

consts_code
  "new_Addr" ("new'_addr {* %x. case x of None => True | Some y => False *}/ {* None *}")
  "cast_ok" ("true????")

  "wf" ("true?")

  "arbitrary" ("(raise ERROR)")
  "arbitrary" :: "val" ("{* Unit *}")
  "arbitrary" :: "cname" ("\"\"")

  "Object" ("\"Object\"")
  "list_name" ("\"list\"")
  "test_name" ("\"test\"")
  "append_name" ("\"append\"")
  "makelist_name" ("\"makelist\"")
  "val_nam" ("\"val\"")
  "next_nam" ("\"next\"")

ML {*
fun new_addr p none hp =
  let fun nr i = if p (hp i) then (i, none) else nr (i+1);
  in nr 0 end;
*}

subsection {* Single step execution *}

generate_code
  test = "exec (example_prg, start_state)"

ML {* test *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}
ML {* exec (example_prg, the it) *}

end


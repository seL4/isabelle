(*  Title:      HOL/MicroJava/J/JListExample.thy
    ID:         $Id$
    Author:     Stefan Berghofer
*)

header {* \isaheader{Example for generating executable code from Java semantics} *}

theory JListExample = Eval + SystemClasses:

ML {* Syntax.ambiguity_level := 100000 *}

consts
  list_name :: cname
  append_name :: mname
  val_nam :: vnam
  next_nam :: vnam
  l_nam :: vnam
  l1_nam :: vnam
  l2_nam :: vnam
  l3_nam :: vnam
  l4_nam :: vnam

constdefs
  val_name :: vname
  "val_name == VName val_nam"

  next_name :: vname
  "next_name == VName next_nam"

  l_name :: vname
  "l_name == VName l_nam"

  l1_name :: vname
  "l1_name == VName l1_nam"

  l2_name :: vname
  "l2_name == VName l2_nam"

  l3_name :: vname
  "l3_name == VName l3_nam"

  l4_name :: vname
  "l4_name == VName l4_nam"

  list_class :: "java_mb class"
  "list_class ==
    (Object,
     [(val_name, PrimT Integer), (next_name, RefT (ClassT list_name))],
     [((append_name, [RefT (ClassT list_name)]), PrimT Void,
      ([l_name], [],
       If(BinOp Eq ({list_name}(LAcc This)..next_name) (Lit Null))
         Expr ({list_name}(LAcc This)..next_name:=LAcc l_name)
       Else
         Expr ({list_name}({list_name}(LAcc This)..next_name)..
           append_name({[RefT (ClassT list_name)]}[LAcc l_name])), 
       Lit Unit))])"

  example_prg :: "java_mb prog"
  "example_prg == [ObjectC, (list_name, list_class)]"

types_code
  cname ("string")
  vnam ("string")
  mname ("string")
  loc_ ("int")

consts_code
  "new_Addr" ("new'_addr {* %x. case x of None => True | Some y => False *}/ {* None *} {* Loc *}")

  "arbitrary" ("(raise ERROR)")
  "arbitrary" :: "val" ("{* Unit *}")
  "arbitrary" :: "cname" ("\"\"")

  "Object" ("\"Object\"")
  "list_name" ("\"list\"")
  "append_name" ("\"append\"")
  "val_nam" ("\"val\"")
  "next_nam" ("\"next\"")
  "l_nam" ("\"l\"")
  "l1_nam" ("\"l1\"")
  "l2_nam" ("\"l2\"")
  "l3_nam" ("\"l3\"")
  "l4_nam" ("\"l4\"")

ML {*
fun new_addr p none loc hp =
  let fun nr i = if p (hp (loc i)) then (loc i, none) else nr (i+1);
  in nr 0 end;
*}

generate_code
  test = "example_prg\<turnstile>Norm (empty, empty)
    -(Expr (l1_name::=NewC list_name);;
      Expr ({list_name}(LAcc l1_name)..val_name:=Lit (Intg 1));;
      Expr (l2_name::=NewC list_name);;
      Expr ({list_name}(LAcc l2_name)..val_name:=Lit (Intg 2));;
      Expr (l3_name::=NewC list_name);;
      Expr ({list_name}(LAcc l3_name)..val_name:=Lit (Intg 3));;
      Expr (l4_name::=NewC list_name);;
      Expr ({list_name}(LAcc l4_name)..val_name:=Lit (Intg 4));;
      Expr ({list_name}(LAcc l1_name)..
        append_name({[RefT (ClassT list_name)]}[LAcc l2_name]));;
      Expr ({list_name}(LAcc l1_name)..
        append_name({[RefT (ClassT list_name)]}[LAcc l3_name]));;
      Expr ({list_name}(LAcc l1_name)..
        append_name({[RefT (ClassT list_name)]}[LAcc l4_name])))-> _"

section {* Big step execution *}

ML {*

val Library.Some ((_, (heap, locs)), _) = Seq.pull test;
locs l1_name;
locs l2_name;
locs l3_name;
locs l4_name;
snd (the (heap (Loc 0))) (val_name, "list");
snd (the (heap (Loc 0))) (next_name, "list");
snd (the (heap (Loc 1))) (val_name, "list");
snd (the (heap (Loc 1))) (next_name, "list");
snd (the (heap (Loc 2))) (val_name, "list");
snd (the (heap (Loc 2))) (next_name, "list");
snd (the (heap (Loc 3))) (val_name, "list");
snd (the (heap (Loc 3))) (next_name, "list");

*}

end

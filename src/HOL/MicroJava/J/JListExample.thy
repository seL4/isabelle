(*  Title:      HOL/MicroJava/J/JListExample.thy
    Author:     Stefan Berghofer
*)

header {* \isaheader{Example for generating executable code from Java semantics} *}

theory JListExample
imports Eval
begin

declare [[syntax_ambiguity = ignore]]

consts
  list_nam :: cnam
  append_name :: mname

axiomatization val_nam next_nam l_nam l1_nam l2_nam l3_nam l4_nam :: vnam
where distinct_fields: "val_name \<noteq> next_name"
  and distinct_vars:
  "l_nam \<noteq> l1_nam" "l_nam \<noteq> l2_nam" "l_nam \<noteq> l3_nam" "l_nam \<noteq> l4_nam"
  "l1_nam \<noteq> l2_nam" "l1_nam \<noteq> l3_nam" "l1_nam \<noteq> l4_nam"
  "l2_nam \<noteq> l3_nam" "l2_nam \<noteq> l4_nam"
  "l3_nam \<noteq> l4_nam"

definition list_name :: cname where
  "list_name = Cname list_nam"

definition val_name :: vname where
  "val_name == VName val_nam"

definition next_name :: vname where
  "next_name == VName next_nam"

definition l_name :: vname where
  "l_name == VName l_nam"

definition l1_name :: vname where
  "l1_name == VName l1_nam"

definition l2_name :: vname where
  "l2_name == VName l2_nam"

definition l3_name :: vname where
  "l3_name == VName l3_nam"

definition l4_name :: vname where
  "l4_name == VName l4_nam"

definition list_class :: "java_mb class" where
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

definition example_prg :: "java_mb prog" where
  "example_prg == [ObjectC, (list_name, list_class)]"

code_datatype list_nam
lemma equal_cnam_code [code]:
  "HOL.equal list_nam list_nam \<longleftrightarrow> True"
  by(simp add: equal_cnam_def)

code_datatype append_name
lemma equal_mname_code [code]:
  "HOL.equal append_name append_name \<longleftrightarrow> True"
  by(simp add: equal_mname_def)

code_datatype val_nam next_nam l_nam l1_nam l2_nam l3_nam l4_nam 
lemma equal_vnam_code [code]: 
  "HOL.equal val_nam val_nam \<longleftrightarrow> True"
  "HOL.equal next_nam next_nam \<longleftrightarrow> True"
  "HOL.equal l_nam l_nam \<longleftrightarrow> True"
  "HOL.equal l1_nam l1_nam \<longleftrightarrow> True"
  "HOL.equal l2_nam l2_nam \<longleftrightarrow> True"
  "HOL.equal l3_nam l3_nam \<longleftrightarrow> True"
  "HOL.equal l4_nam l4_nam \<longleftrightarrow> True"

  "HOL.equal val_nam next_nam \<longleftrightarrow> False"
  "HOL.equal next_nam val_nam \<longleftrightarrow> False"

  "HOL.equal l_nam l1_nam \<longleftrightarrow> False"
  "HOL.equal l_nam l2_nam \<longleftrightarrow> False"
  "HOL.equal l_nam l3_nam \<longleftrightarrow> False"
  "HOL.equal l_nam l4_nam \<longleftrightarrow> False"

  "HOL.equal l1_nam l_nam \<longleftrightarrow> False"
  "HOL.equal l1_nam l2_nam \<longleftrightarrow> False"
  "HOL.equal l1_nam l3_nam \<longleftrightarrow> False"
  "HOL.equal l1_nam l4_nam \<longleftrightarrow> False"

  "HOL.equal l2_nam l_nam \<longleftrightarrow> False"
  "HOL.equal l2_nam l1_nam \<longleftrightarrow> False"
  "HOL.equal l2_nam l3_nam \<longleftrightarrow> False"
  "HOL.equal l2_nam l4_nam \<longleftrightarrow> False"

  "HOL.equal l3_nam l_nam \<longleftrightarrow> False"
  "HOL.equal l3_nam l1_nam \<longleftrightarrow> False"
  "HOL.equal l3_nam l2_nam \<longleftrightarrow> False"
  "HOL.equal l3_nam l4_nam \<longleftrightarrow> False"

  "HOL.equal l4_nam l_nam \<longleftrightarrow> False"
  "HOL.equal l4_nam l1_nam \<longleftrightarrow> False"
  "HOL.equal l4_nam l2_nam \<longleftrightarrow> False"
  "HOL.equal l4_nam l3_nam \<longleftrightarrow> False"
  by(simp_all add: distinct_fields distinct_fields[symmetric] distinct_vars distinct_vars[symmetric] equal_vnam_def)

axiomatization where
  nat_to_loc'_inject: "nat_to_loc' l = nat_to_loc' l' \<longleftrightarrow> l = l'"

lemma equal_loc'_code [code]:
  "HOL.equal (nat_to_loc' l) (nat_to_loc' l') \<longleftrightarrow> l = l'"
  by(simp add: equal_loc'_def nat_to_loc'_inject)

definition undefined_cname :: cname 
  where [code del]: "undefined_cname = undefined"
declare undefined_cname_def[symmetric, code_unfold]
code_datatype Object Xcpt Cname undefined_cname

definition undefined_val :: val
  where [code del]: "undefined_val = undefined"
declare undefined_val_def[symmetric, code_unfold]
code_datatype Unit Null Bool Intg Addr undefined_val

definition E where 
  "E = Expr (l1_name::=NewC list_name);;
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
         append_name({[RefT (ClassT list_name)]}[LAcc l4_name]))"

definition test where
  "test = Predicate.Pred (\<lambda>s. example_prg\<turnstile>Norm (empty, empty) -E-> s)"

lemma test_code [code]:
  "test = exec_i_i_i_o example_prg (Norm (empty, empty)) E"
by(auto intro: exec_i_i_i_oI intro!: pred_eqI elim: exec_i_i_i_oE simp add: test_def)

ML {* 
  val SOME ((_, (heap, locs)), _) = Predicate.yield @{code test};
  locs @{code l1_name};
  locs @{code l2_name};
  locs @{code l3_name};
  locs @{code l4_name};

  fun list_fields n = 
    @{code snd} (@{code the} (heap (@{code Loc} (@{code "nat_to_loc'"} n))));
  fun val_field n =
    list_fields n (@{code val_name}, @{code "list_name"});
  fun next_field n =
    list_fields n (@{code next_name}, @{code "list_name"});
  val Suc = @{code Suc};

  val_field @{code "0 :: nat"};
  next_field @{code "0 :: nat"};

  val_field @{code "1 :: nat"};
  next_field @{code "1 :: nat"};

  val_field (Suc (Suc @{code "0 :: nat"}));
  next_field (Suc (Suc @{code "0 :: nat"}));

  val_field (Suc (Suc (Suc @{code "0 :: nat"})));
  next_field (Suc (Suc (Suc @{code "0 :: nat"})));
*}

end

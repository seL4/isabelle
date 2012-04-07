(*  Title:      HOL/MicroJava/J/State.thy
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* \isaheader{Program State} *}

theory State
imports TypeRel Value
begin

type_synonym 
  fields' = "(vname \<times> cname \<rightharpoonup> val)"  -- "field name, defining class, value"

type_synonym
  obj = "cname \<times> fields'"    -- "class instance with class name and fields"

definition obj_ty :: "obj => ty" where
 "obj_ty obj  == Class (fst obj)"

definition init_vars :: "('a \<times> ty) list => ('a \<rightharpoonup> val)" where
 "init_vars == map_of o map (\<lambda>(n,T). (n,default_val T))"

type_synonym aheap = "loc \<rightharpoonup> obj"    -- {* "@{text heap}" used in a translation below *}
type_synonym locals = "vname \<rightharpoonup> val"  -- "simple state, i.e. variable contents"

type_synonym state = "aheap \<times> locals"      -- "heap, local parameter including This"
type_synonym xstate = "val option \<times> state" -- "state including exception information"

abbreviation (input)
  heap :: "state => aheap"
  where "heap == fst"

abbreviation (input)
  locals :: "state => locals"
  where "locals == snd"

abbreviation "Norm s == (None, s)"

abbreviation (input)
  abrupt :: "xstate \<Rightarrow> val option"
  where "abrupt == fst"

abbreviation (input)
  store :: "xstate \<Rightarrow> state"
  where "store == snd"

abbreviation
  lookup_obj :: "state \<Rightarrow> val \<Rightarrow> obj"
  where "lookup_obj s a' == the (heap s (the_Addr a'))"

definition raise_if :: "bool \<Rightarrow> xcpt \<Rightarrow> val option \<Rightarrow> val option" where
  "raise_if b x xo \<equiv> if b \<and>  (xo = None) then Some (Addr (XcptRef x)) else xo"

text {* Make @{text new_Addr} completely specified (at least for the code generator) *}
(*
definition new_Addr  :: "aheap => loc \<times> val option" where
  "new_Addr h \<equiv> SOME (a,x). (h a = None \<and>  x = None) |  x = Some (Addr (XcptRef OutOfMemory))"
*)
consts nat_to_loc' :: "nat => loc'"
code_datatype nat_to_loc'
definition new_Addr  :: "aheap => loc \<times> val option" where
  "new_Addr h \<equiv> 
   if \<exists>n. h (Loc (nat_to_loc' n)) = None 
   then (Loc (nat_to_loc' (LEAST n. h (Loc (nat_to_loc' n)) = None)), None)
   else (Loc (nat_to_loc' 0), Some (Addr (XcptRef OutOfMemory)))"

definition np    :: "val => val option => val option" where
 "np v == raise_if (v = Null) NullPointer"

definition c_hupd  :: "aheap => xstate => xstate" where
 "c_hupd h'== \<lambda>(xo,(h,l)). if xo = None then (None,(h',l)) else (xo,(h,l))"

definition cast_ok :: "'c prog => cname => aheap => val => bool" where
 "cast_ok G C h v == v = Null \<or> G\<turnstile>obj_ty (the (h (the_Addr v)))\<preceq> Class C"

lemma obj_ty_def2 [simp]: "obj_ty (C,fs) = Class C"
apply (unfold obj_ty_def)
apply (simp (no_asm))
done


lemma new_AddrD: "new_Addr hp = (ref, xcp) \<Longrightarrow>
  hp ref = None \<and> xcp = None \<or> xcp = Some (Addr (XcptRef OutOfMemory))"
apply (drule sym)
apply (unfold new_Addr_def)
apply (simp split: split_if_asm)
apply (erule LeastI)
done

lemma raise_if_True [simp]: "raise_if True x y \<noteq> None"
apply (unfold raise_if_def)
apply auto
done

lemma raise_if_False [simp]: "raise_if False x y = y"
apply (unfold raise_if_def)
apply auto
done

lemma raise_if_Some [simp]: "raise_if c x (Some y) \<noteq> None"
apply (unfold raise_if_def)
apply auto
done

lemma raise_if_Some2 [simp]: 
  "raise_if c z (if x = None then Some y else x) \<noteq> None"
apply (unfold raise_if_def)
apply(induct_tac "x")
apply auto
done

lemma raise_if_SomeD [rule_format (no_asm)]: 
  "raise_if c x y = Some z \<longrightarrow> c \<and>  Some z = Some (Addr (XcptRef x)) |  y = Some z"
apply (unfold raise_if_def)
apply auto
done

lemma raise_if_NoneD [rule_format (no_asm)]: 
  "raise_if c x y = None --> \<not> c \<and>  y = None"
apply (unfold raise_if_def)
apply auto
done

lemma np_NoneD [rule_format (no_asm)]: 
  "np a' x' = None --> x' = None \<and>  a' \<noteq> Null"
apply (unfold np_def raise_if_def)
apply auto
done

lemma np_None [rule_format (no_asm), simp]: "a' \<noteq> Null --> np a' x' = x'"
apply (unfold np_def raise_if_def)
apply auto
done

lemma np_Some [simp]: "np a' (Some xc) = Some xc"
apply (unfold np_def raise_if_def)
apply auto
done

lemma np_Null [simp]: "np Null None = Some (Addr (XcptRef NullPointer))"
apply (unfold np_def raise_if_def)
apply auto
done

lemma np_Addr [simp]: "np (Addr a) None = None"
apply (unfold np_def raise_if_def)
apply auto
done

lemma np_raise_if [simp]: "(np Null (raise_if c xc None)) =  
  Some (Addr (XcptRef (if c then  xc else NullPointer)))"
apply (unfold raise_if_def)
apply (simp (no_asm))
done

lemma c_hupd_fst [simp]: "fst (c_hupd h (x, s)) = x"
by (simp add: c_hupd_def split_beta)

text {* Naive implementation for @{term "new_Addr"} by exhaustive search *}

definition gen_new_Addr :: "aheap => nat \<Rightarrow> loc \<times> val option" where
  "gen_new_Addr h n \<equiv> 
   if \<exists>a. a \<ge> n \<and> h (Loc (nat_to_loc' a)) = None 
   then (Loc (nat_to_loc' (LEAST a. a \<ge> n \<and> h (Loc (nat_to_loc' a)) = None)), None)
   else (Loc (nat_to_loc' 0), Some (Addr (XcptRef OutOfMemory)))"

lemma new_Addr_code_code [code]:
  "new_Addr h = gen_new_Addr h 0"
by(simp only: new_Addr_def gen_new_Addr_def split: split_if) simp

lemma gen_new_Addr_code [code]:
  "gen_new_Addr h n = (if h (Loc (nat_to_loc' n)) = None then (Loc (nat_to_loc' n), None) else gen_new_Addr h (Suc n))"
apply(simp add: gen_new_Addr_def)
apply(rule impI)
apply(rule conjI)
 apply safe[1]
  apply(auto intro: arg_cong[where f=nat_to_loc'] Least_equality)[1]
 apply(rule arg_cong[where f=nat_to_loc'])
 apply(rule arg_cong[where f=Least])
 apply(rule ext)
 apply(safe, simp_all)[1]
 apply(rename_tac "n'")
 apply(case_tac "n = n'", simp_all)[1]
apply clarify
apply(subgoal_tac "a = n")
 apply(auto intro: Least_equality arg_cong[where f=nat_to_loc'])[1]
apply(rule ccontr)
apply(erule_tac x="a" in allE)
apply simp
done

instantiation loc' :: equal
begin

definition "HOL.equal (l :: loc') l' \<longleftrightarrow> l = l'"
instance by default (simp add: equal_loc'_def)

end

end

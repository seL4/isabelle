(*  Title:      HOL/MicroJava/J/State.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* \isaheader{Program State} *}

theory State = TypeRel + Value:

types 
  fields_ = "(vname \<times> cname \<rightharpoonup> val)"  -- "field name, defining class, value"

  obj = "cname \<times> fields_"    -- "class instance with class name and fields"

constdefs
  obj_ty  :: "obj => ty"
 "obj_ty obj  == Class (fst obj)"

  init_vars :: "('a \<times> ty) list => ('a \<rightharpoonup> val)"
 "init_vars == map_of o map (\<lambda>(n,T). (n,default_val T))"
  

types aheap  = "loc \<rightharpoonup> obj"    -- {* "@{text heap}" used in a translation below *}
      locals = "vname \<rightharpoonup> val"  -- "simple state, i.e. variable contents"

      state  = "aheap \<times> locals"      -- "heap, local parameter including This"
      xstate = "val option \<times> state" -- "state including exception information"

syntax
  heap    :: "state => aheap"
  locals  :: "state => locals"
  Norm    :: "state => xstate"
  abrupt  :: "xstate \<Rightarrow> val option"
  store   :: "xstate \<Rightarrow> state"
  lookup_obj   :: "state \<Rightarrow> val \<Rightarrow> obj"

translations
  "heap"   => "fst"
  "locals" => "snd"
  "Norm s" == "(None,s)"
  "abrupt"     => "fst"
  "store"      => "snd"
 "lookup_obj s a'"  == "the (heap s (the_Addr a'))"


constdefs
  raise_if :: "bool \<Rightarrow> xcpt \<Rightarrow> val option \<Rightarrow> val option"
  "raise_if b x xo \<equiv> if b \<and>  (xo = None) then Some (Addr (XcptRef x)) else xo"

  new_Addr  :: "aheap => loc \<times> val option"
  "new_Addr h \<equiv> SOME (a,x). (h a = None \<and>  x = None) |  x = Some (Addr (XcptRef OutOfMemory))"

  np    :: "val => val option => val option"
 "np v == raise_if (v = Null) NullPointer"

  c_hupd  :: "aheap => xstate => xstate"
 "c_hupd h'== \<lambda>(xo,(h,l)). if xo = None then (None,(h',l)) else (xo,(h,l))"

  cast_ok :: "'c prog => cname => aheap => val => bool"
 "cast_ok G C h v == v = Null \<or> G\<turnstile>obj_ty (the (h (the_Addr v)))\<preceq> Class C"

lemma obj_ty_def2 [simp]: "obj_ty (C,fs) = Class C"
apply (unfold obj_ty_def)
apply (simp (no_asm))
done


lemma new_AddrD: "new_Addr hp = (ref, xcp) \<Longrightarrow>
  hp ref = None \<and> xcp = None \<or> xcp = Some (Addr (XcptRef OutOfMemory))"
apply (drule sym)
apply (unfold new_Addr_def)
apply(simp add: Pair_fst_snd_eq Eps_split)
apply(rule someI)
apply(rule disjI2)
apply(rule_tac "r" = "snd (?a,Some (Addr (XcptRef OutOfMemory)))" in trans)
apply auto
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

end

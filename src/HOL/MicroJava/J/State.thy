(*  Title:      HOL/MicroJava/J/State.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

header "Program State"

theory State = TypeRel + Value:

types 
  fields_ = "(vname \<times> cname \<leadsto> val)"  -- "field name, defining class, value"

  obj = "cname \<times> fields_"    -- "class instance with class name and fields"

constdefs
  obj_ty  :: "obj => ty"
 "obj_ty obj  == Class (fst obj)"

  init_vars :: "('a \<times> ty) list => ('a \<leadsto> val)"
 "init_vars == map_of o map (\<lambda>(n,T). (n,default_val T))"
  

types aheap  = "loc \<leadsto> obj"    -- {* "@{text heap}" used in a translation below *}
      locals = "vname \<leadsto> val"  -- "simple state, i.e. variable contents"

      state  = "aheap \<times> locals"      -- "heap, local parameter including This"
      xstate = "xcpt option \<times> state" -- "state including exception information"

syntax
  heap    :: "state => aheap"
  locals  :: "state => locals"
  Norm    :: "state => xstate"

translations
  "heap"   => "fst"
  "locals" => "snd"
  "Norm s" == "(None,s)"

constdefs
  new_Addr  :: "aheap => loc \<times> xcpt option"
 "new_Addr h == SOME (a,x). (h a = None \<and>  x = None) |  x = Some OutOfMemory"

  raise_if  :: "bool => xcpt => xcpt option => xcpt option"
 "raise_if c x xo == if c \<and>  (xo = None) then Some x else xo"

  np    :: "val => xcpt option => xcpt option"
 "np v == raise_if (v = Null) NullPointer"

  c_hupd  :: "aheap => xstate => xstate"
 "c_hupd h'== \<lambda>(xo,(h,l)). if xo = None then (None,(h',l)) else (xo,(h,l))"

  cast_ok :: "'c prog => cname => aheap => val => bool"
 "cast_ok G C h v == v = Null \<or> G\<turnstile>obj_ty (the (h (the_Addr v)))\<preceq> Class C"

lemma obj_ty_def2 [simp]: "obj_ty (C,fs) = Class C"
apply (unfold obj_ty_def)
apply (simp (no_asm))
done

lemma new_AddrD: 
"(a,x) = new_Addr h ==> h a = None \<and> x = None | x = Some OutOfMemory"
apply (unfold new_Addr_def)
apply(simp add: Pair_fst_snd_eq Eps_split)
apply(rule someI)
apply(rule disjI2)
apply(rule_tac "r" = "snd (?a,Some OutOfMemory)" in trans)
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
  "raise_if c x y = Some z \<longrightarrow> c \<and>  Some z = Some x |  y = Some z"
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

lemma np_Null [simp]: "np Null None = Some NullPointer"
apply (unfold np_def raise_if_def)
apply auto
done

lemma np_Addr [simp]: "np (Addr a) None = None"
apply (unfold np_def raise_if_def)
apply auto
done

lemma np_raise_if [simp]: "(np Null (raise_if c xc None)) =  
  Some (if c then xc else NullPointer)"
apply (unfold raise_if_def)
apply (simp (no_asm))
done

end

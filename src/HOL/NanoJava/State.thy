(*  Title:      HOL/NanoJava/State.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   2001 Technische Universitaet Muenchen
*)

header "Program State"

theory State = TypeRel:

constdefs

  body :: "cname \<times> mname => stmt"
 "body \<equiv> \<lambda>(C,m). bdy (the (method C m))"

text {* Locations, i.e.\ abstract references to objects *}
typedecl loc 

datatype val
  = Null        --{* null reference *}
  | Addr loc    --{* address, i.e. location of object *}

types	fields
	= "(fname \<rightharpoonup> val)"

        obj = "cname \<times> fields"

translations

  "fields" \<leftharpoondown> (type)"fname => val option"
  "obj"    \<leftharpoondown> (type)"cname \<times> fields"

constdefs

  init_vars:: "('a \<rightharpoonup> 'b) => ('a \<rightharpoonup> val)"
 "init_vars m == option_map (\<lambda>T. Null) o m"
  
text {* private: *}
types	heap   = "loc   \<rightharpoonup> obj"
        locals = "vname \<rightharpoonup> val"	

text {* private: *}
record  state
	= heap   :: heap
          locals :: locals

translations

  "heap"   \<leftharpoondown> (type)"loc   => obj option"
  "locals" \<leftharpoondown> (type)"vname => val option"
  "state" \<leftharpoondown> (type)"(|heap :: heap, locals :: locals|)"

constdefs

  del_locs     :: "state => state"
 "del_locs s \<equiv> s (| locals := empty |)"

  init_locs     :: "cname => mname => state => state"
 "init_locs C m s \<equiv> s (| locals := locals s ++ 
                         init_vars (map_of (lcl (the (method C m)))) |)"

text {* The first parameter of @{term set_locs} is of type @{typ state} 
        rather than @{typ locals} in order to keep @{typ locals} private.*}
constdefs
  set_locs  :: "state => state => state"
 "set_locs s s' \<equiv> s' (| locals := locals s |)"

  get_local     :: "state => vname => val" ("_<_>" [99,0] 99)
 "get_local s x  \<equiv> the (locals s x)"

--{* local function: *}
  get_obj       :: "state => loc => obj"
 "get_obj s a \<equiv> the (heap s a)"

  obj_class     :: "state => loc => cname"
 "obj_class s a \<equiv> fst (get_obj s a)"

  get_field     :: "state => loc => fname => val"
 "get_field s a f \<equiv> the (snd (get_obj s a) f)"

--{* local function: *}
  hupd       :: "loc => obj => state => state"   ("hupd'(_|->_')" [10,10] 1000)
 "hupd a obj s \<equiv> s (| heap   := ((heap   s)(a\<mapsto>obj))|)"

  lupd       :: "vname => val => state => state" ("lupd'(_|->_')" [10,10] 1000)
 "lupd x v s   \<equiv> s (| locals := ((locals s)(x\<mapsto>v  ))|)"

syntax (xsymbols)
  hupd       :: "loc => obj => state => state"   ("hupd'(_\<mapsto>_')" [10,10] 1000)
  lupd       :: "vname => val => state => state" ("lupd'(_\<mapsto>_')" [10,10] 1000)

constdefs

  new_obj    :: "loc => cname => state => state"
 "new_obj a C   \<equiv> hupd(a\<mapsto>(C,init_vars (field C)))"

  upd_obj    :: "loc => fname => val => state => state"
 "upd_obj a f v s \<equiv> let (C,fs) = the (heap s a) in hupd(a\<mapsto>(C,fs(f\<mapsto>v))) s"

  new_Addr	:: "state => val"
 "new_Addr s == SOME v. (\<exists>a. v = Addr a \<and> (heap s) a = None) | v = Null"


subsection "Properties not used in the meta theory"

lemma locals_upd_id [simp]: "s\<lparr>locals := locals s\<rparr> = s" 
by simp

lemma lupd_get_local_same [simp]: "lupd(x\<mapsto>v) s<x> = v"
by (simp add: lupd_def get_local_def)

lemma lupd_get_local_other [simp]: "x \<noteq> y \<Longrightarrow> lupd(x\<mapsto>v) s<y> = s<y>"
apply (drule not_sym)
by (simp add: lupd_def get_local_def)

lemma get_field_lupd [simp]:
  "get_field (lupd(x\<mapsto>y) s) a f = get_field s a f"
by (simp add: lupd_def get_field_def get_obj_def)

lemma get_field_set_locs [simp]:
  "get_field (set_locs l s) a f = get_field s a f"
by (simp add: lupd_def get_field_def set_locs_def get_obj_def)

lemma get_field_del_locs [simp]:
  "get_field (del_locs s) a f = get_field s a f"
by (simp add: lupd_def get_field_def del_locs_def get_obj_def)

lemma new_obj_get_local [simp]: "new_obj a C s <x> = s<x>"
by (simp add: new_obj_def hupd_def get_local_def)

lemma heap_lupd [simp]: "heap (lupd(x\<mapsto>y) s) = heap s"
by (simp add: lupd_def)

lemma heap_hupd_same [simp]: "heap (hupd(a\<mapsto>obj) s) a = Some obj"
by (simp add: hupd_def)

lemma heap_hupd_other [simp]: "aa \<noteq> a  \<Longrightarrow> heap (hupd(aa\<mapsto>obj) s) a = heap s a"
apply (drule not_sym)
by (simp add: hupd_def)

lemma hupd_hupd [simp]: "hupd(a\<mapsto>obj) (hupd(a\<mapsto>obj') s) = hupd(a\<mapsto>obj) s"
by (simp add: hupd_def)

lemma heap_del_locs [simp]: "heap (del_locs s) = heap s"
by (simp add: del_locs_def)

lemma heap_set_locs [simp]: "heap (set_locs l s) = heap s"
by (simp add: set_locs_def)

lemma hupd_lupd [simp]: 
  "hupd(a\<mapsto>obj) (lupd(x\<mapsto>y) s) = lupd(x\<mapsto>y) (hupd(a\<mapsto>obj) s)"
by (simp add: hupd_def lupd_def)

lemma hupd_del_locs [simp]: 
  "hupd(a\<mapsto>obj) (del_locs s) = del_locs (hupd(a\<mapsto>obj) s)"
by (simp add: hupd_def del_locs_def)

lemma new_obj_lupd [simp]: 
  "new_obj a C (lupd(x\<mapsto>y) s) = lupd(x\<mapsto>y) (new_obj a C s)"
by (simp add: new_obj_def)

lemma new_obj_del_locs [simp]: 
  "new_obj a C (del_locs s) = del_locs (new_obj a C s)"
by (simp add: new_obj_def)

lemma upd_obj_lupd [simp]: 
  "upd_obj a f v (lupd(x\<mapsto>y) s) = lupd(x\<mapsto>y) (upd_obj a f v s)"
by (simp add: upd_obj_def Let_def split_beta)

lemma upd_obj_del_locs [simp]: 
  "upd_obj a f v (del_locs s) = del_locs (upd_obj a f v s)"
by (simp add: upd_obj_def Let_def split_beta)

lemma get_field_hupd_same [simp]:
 "get_field (hupd(a\<mapsto>(C, fs)) s) a = the \<circ> fs"
apply (rule ext)
by (simp add: get_field_def get_obj_def)

lemma get_field_hupd_other [simp]:
 "aa \<noteq> a  \<Longrightarrow> get_field (hupd(aa\<mapsto>obj) s) a = get_field s a"
apply (rule ext)
by (simp add: get_field_def get_obj_def)

lemma new_AddrD: 
"new_Addr s = v \<Longrightarrow> (\<exists>a. v = Addr a \<and> heap s a = None) | v = Null"
apply (unfold new_Addr_def)
apply (erule subst)
apply (rule someI)
apply (rule disjI2)
apply (rule HOL.refl)
done

end

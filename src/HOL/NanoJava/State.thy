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

text {* locations, i.e.\ abstract references to objects *}
typedecl loc 

datatype val
  = Null        --{* null reference *}
  | Addr loc    --{* address, i.e. location of object *}

types	fields
	= "(fname \<leadsto> val)"

        obj = "cname \<times> fields"

translations

  "fields" \<leftharpoondown> (type)"fname => val option"
  "obj"    \<leftharpoondown> (type)"cname \<times> fields"

constdefs

  init_vars:: "('a \<leadsto> 'b) => ('a \<leadsto> val)"
 "init_vars m == option_map (\<lambda>T. Null) o m"
  
text {* private *}
types	heap   = "loc   \<leadsto> obj"
        locals = "vname \<leadsto> val"	

text {* private *}
record  state
	= heap   :: heap
          locals :: locals

translations

  "heap"   \<leftharpoondown> (type)"loc   => obj option"
  "locals" \<leftharpoondown> (type)"vname => val option"
  "state" \<leftharpoondown> (type)"(|heap :: heap, locals :: locals|)"

constdefs

  reset_locs     :: "state => state"
 "reset_locs s \<equiv> s (| locals := empty |)"

  init_locs     :: "cname => mname => state => state"
 "init_locs C m s \<equiv> s (| locals:=init_vars (map_of (lcl (the (method C m)))) |)"

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

lemma new_AddrD: 
"new_Addr s = v \<Longrightarrow> (\<exists>a. v = Addr a \<and> heap s a = None) | v = Null"
apply (unfold new_Addr_def)
apply (erule subst)
apply (rule someI)
apply (rule disjI2)
apply (rule HOL.refl)
done

end

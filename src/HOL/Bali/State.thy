(*  Title:      HOL/Bali/State.thy
    ID:         $Id$
    Author:     David von Oheimb
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)
header {* State for evaluation of Java expressions and statements *}

theory State = DeclConcepts:

text {*
design issues:
\begin{itemize}
\item all kinds of objects (class instances, arrays, and class objects)
  are handeled via a general object abstraction
\item the heap and the map for class objects are combined into a single table
  @{text "(recall (loc, obj) table \<times> (qtname, obj) table  ~=  (loc + qtname, obj) table)"}
\end{itemize}
*}

section "objects"

datatype  obj_tag =     --{* tag for generic object   *}
	  CInst qtname  --{* class instance           *}
	| Arr  ty int   --{* array with component type and length *}
    --{* | CStat qtname   the tag is irrelevant for a class object,
			   i.e. the static fields of a class,
                           since its type is given already by the reference to 
                           it (see below) *}

types	vn   = "fspec + int"                    --{* variable name      *}
record	obj  = 
          tag :: "obj_tag"                      --{* generalized object *}
          values :: "(vn, val) table"      

translations 
  "fspec" <= (type) "vname \<times> qtname" 
  "vn"    <= (type) "fspec + int"
  "obj"   <= (type) "\<lparr>tag::obj_tag, values::vn \<Rightarrow> val option\<rparr>"
  "obj"   <= (type) "\<lparr>tag::obj_tag, values::vn \<Rightarrow> val option,\<dots>::'a\<rparr>"

constdefs
  
  the_Arr :: "obj option \<Rightarrow> ty \<times> int \<times> (vn, val) table"
 "the_Arr obj \<equiv> \<epsilon>(T,k,t). obj = Some \<lparr>tag=Arr T k,values=t\<rparr>"

lemma the_Arr_Arr [simp]: "the_Arr (Some \<lparr>tag=Arr T k,values=cs\<rparr>) = (T,k,cs)"
apply (auto simp: the_Arr_def)
done

lemma the_Arr_Arr1 [simp,intro,dest]:
 "\<lbrakk>tag obj = Arr T k\<rbrakk> \<Longrightarrow> the_Arr (Some obj) = (T,k,values obj)"
apply (auto simp add: the_Arr_def)
done

constdefs

  upd_obj       :: "vn \<Rightarrow> val \<Rightarrow> obj \<Rightarrow> obj" 
 "upd_obj n v \<equiv> \<lambda> obj . obj \<lparr>values:=(values obj)(n\<mapsto>v)\<rparr>"

lemma upd_obj_def2 [simp]: 
  "upd_obj n v obj = obj \<lparr>values:=(values obj)(n\<mapsto>v)\<rparr>" 
apply (auto simp: upd_obj_def)
done

constdefs
  obj_ty        :: "obj \<Rightarrow> ty"
 "obj_ty obj    \<equiv> case tag obj of 
                    CInst C \<Rightarrow> Class C 
                  | Arr T k \<Rightarrow> T.[]"

lemma obj_ty_eq [intro!]: "obj_ty \<lparr>tag=oi,values=x\<rparr> = obj_ty \<lparr>tag=oi,values=y\<rparr>" 
by (simp add: obj_ty_def)


lemma obj_ty_eq1 [intro!,dest]: 
  "tag obj = tag obj' \<Longrightarrow> obj_ty obj = obj_ty obj'" 
by (simp add: obj_ty_def)

lemma obj_ty_cong [simp]: 
  "obj_ty (obj \<lparr>values:=vs\<rparr>) = obj_ty obj" 
by auto

lemma obj_ty_CInst [simp]: 
 "obj_ty \<lparr>tag=CInst C,values=vs\<rparr> = Class C" 
by (simp add: obj_ty_def)

lemma obj_ty_CInst1 [simp,intro!,dest]: 
 "\<lbrakk>tag obj = CInst C\<rbrakk> \<Longrightarrow> obj_ty obj = Class C" 
by (simp add: obj_ty_def)

lemma obj_ty_Arr [simp]: 
 "obj_ty \<lparr>tag=Arr T i,values=vs\<rparr> = T.[]"
by (simp add: obj_ty_def)

lemma obj_ty_Arr1 [simp,intro!,dest]: 
 "\<lbrakk>tag obj = Arr T i\<rbrakk> \<Longrightarrow> obj_ty obj = T.[]"
by (simp add: obj_ty_def)

lemma obj_ty_widenD: 
 "G\<turnstile>obj_ty obj\<preceq>RefT t \<Longrightarrow> (\<exists>C. tag obj = CInst C) \<or> (\<exists>T k. tag obj = Arr T k)"
apply (unfold obj_ty_def)
apply (auto split add: obj_tag.split_asm)
done

constdefs

  obj_class :: "obj \<Rightarrow> qtname"
 "obj_class obj \<equiv> case tag obj of 
                    CInst C \<Rightarrow> C 
                  | Arr T k \<Rightarrow> Object"


lemma obj_class_CInst [simp]: "obj_class \<lparr>tag=CInst C,values=vs\<rparr> = C" 
by (auto simp: obj_class_def)

lemma obj_class_CInst1 [simp,intro!,dest]: 
  "tag obj = CInst C \<Longrightarrow> obj_class obj = C" 
by (auto simp: obj_class_def)

lemma obj_class_Arr [simp]: "obj_class \<lparr>tag=Arr T k,values=vs\<rparr> = Object" 
by (auto simp: obj_class_def)

lemma obj_class_Arr1 [simp,intro!,dest]: 
 "tag obj = Arr T k \<Longrightarrow> obj_class obj = Object" 
by (auto simp: obj_class_def)

lemma obj_ty_obj_class: "G\<turnstile>obj_ty obj\<preceq> Class statC = G\<turnstile>obj_class obj \<preceq>\<^sub>C statC"
apply (case_tac "tag obj")
apply (auto simp add: obj_ty_def obj_class_def)
apply (case_tac "statC = Object")
apply (auto dest: widen_Array_Class)
done

section "object references"

types oref = "loc + qtname"         --{* generalized object reference *}
syntax
  Heap  :: "loc   \<Rightarrow> oref"
  Stat  :: "qtname \<Rightarrow> oref"

translations
  "Heap" => "Inl"
  "Stat" => "Inr"
  "oref" <= (type) "loc + qtname"

constdefs
  fields_table::
    "prog \<Rightarrow> qtname \<Rightarrow> (fspec \<Rightarrow> field \<Rightarrow> bool)  \<Rightarrow> (fspec, ty) table"
 "fields_table G C P 
    \<equiv> option_map type \<circ> table_of (filter (split P) (DeclConcepts.fields G C))"

lemma fields_table_SomeI: 
"\<lbrakk>table_of (DeclConcepts.fields G C) n = Some f; P n f\<rbrakk> 
 \<Longrightarrow> fields_table G C P n = Some (type f)"
apply (unfold fields_table_def)
apply clarsimp
apply (rule exI)
apply (rule conjI)
apply (erule map_of_filter_in)
apply assumption
apply simp
done

(* unused *)
lemma fields_table_SomeD': "fields_table G C P fn = Some T \<Longrightarrow>  
  \<exists>f. (fn,f)\<in>set(DeclConcepts.fields G C) \<and> type f = T"
apply (unfold fields_table_def)
apply clarsimp
apply (drule map_of_SomeD)
apply auto
done

lemma fields_table_SomeD: 
"\<lbrakk>fields_table G C P fn = Some T; unique (DeclConcepts.fields G C)\<rbrakk> \<Longrightarrow>  
  \<exists>f. table_of (DeclConcepts.fields G C) fn = Some f \<and> type f = T"
apply (unfold fields_table_def)
apply clarsimp
apply (rule exI)
apply (rule conjI)
apply (erule table_of_filter_unique_SomeD)
apply assumption
apply simp
done

constdefs
  in_bounds :: "int \<Rightarrow> int \<Rightarrow> bool"            ("(_/ in'_bounds _)" [50, 51] 50)
 "i in_bounds k \<equiv> 0 \<le> i \<and> i < k"

  arr_comps :: "'a \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 'a option"
 "arr_comps T k \<equiv> \<lambda>i. if i in_bounds k then Some T else None"
  
  var_tys       :: "prog \<Rightarrow> obj_tag \<Rightarrow> oref \<Rightarrow> (vn, ty) table"
"var_tys G oi r 
  \<equiv> case r of 
      Heap a \<Rightarrow> (case oi of 
                   CInst C \<Rightarrow> fields_table G C (\<lambda>n f. \<not>static f) (+) empty
                 | Arr T k \<Rightarrow> empty (+) arr_comps T k)
    | Stat C \<Rightarrow> fields_table G C (\<lambda>fn f. declclassf fn = C \<and> static f) 
                (+) empty"

lemma var_tys_Some_eq: 
 "var_tys G oi r n = Some T 
  = (case r of 
       Inl a \<Rightarrow> (case oi of  
                   CInst C \<Rightarrow> (\<exists>nt. n = Inl nt \<and> fields_table G C (\<lambda>n f. 
                               \<not>static f) nt = Some T)  
                 | Arr t k \<Rightarrow> (\<exists> i. n = Inr i  \<and> i in_bounds k \<and> t = T))  
     | Inr C \<Rightarrow> (\<exists>nt. n = Inl nt \<and> 
                 fields_table G C (\<lambda>fn f. declclassf fn = C \<and> static f) nt 
                  = Some T))"
apply (unfold var_tys_def arr_comps_def)
apply (force split add: sum.split_asm sum.split obj_tag.split)
done


section "stores"

types	globs               --{* global variables: heap and static variables *}
	= "(oref , obj) table"
	heap
	= "(loc  , obj) table"
(*	locals                   
	= "(lname, val) table" *) (* defined in Value.thy local variables *)

translations
 "globs"  <= (type) "(oref , obj) table"
 "heap"   <= (type) "(loc  , obj) table"
(*  "locals" <= (type) "(lname, val) table" *)

datatype st = (* pure state, i.e. contents of all variables *)
	 st globs locals

subsection "access"

constdefs

  globs  :: "st \<Rightarrow> globs"
 "globs  \<equiv> st_case (\<lambda>g l. g)"
  
  locals :: "st \<Rightarrow> locals"
 "locals \<equiv> st_case (\<lambda>g l. l)"

  heap   :: "st \<Rightarrow> heap"
 "heap s \<equiv> globs s \<circ> Heap"


lemma globs_def2 [simp]: " globs (st g l) = g"
by (simp add: globs_def)

lemma locals_def2 [simp]: "locals (st g l) = l"
by (simp add: locals_def)

lemma heap_def2 [simp]:  "heap s a=globs s (Heap a)"
by (simp add: heap_def)


syntax
  val_this     :: "st \<Rightarrow> val"
  lookup_obj   :: "st \<Rightarrow> val \<Rightarrow> obj"

translations
 "val_this s"       == "the (locals s This)" 
 "lookup_obj s a'"  == "the (heap s (the_Addr a'))"

subsection "memory allocation"

constdefs
  new_Addr     :: "heap \<Rightarrow> loc option"
 "new_Addr h   \<equiv> if (\<forall>a. h a \<noteq> None) then None else Some (\<epsilon> a. h a = None)"

lemma new_AddrD: "new_Addr h = Some a \<Longrightarrow> h a = None"
apply (unfold new_Addr_def)
apply auto
apply (case_tac "h (SOME a\<Colon>loc. h a = None)")
apply simp
apply (fast intro: someI2)
done

lemma new_AddrD2: "new_Addr h = Some a \<Longrightarrow> \<forall>b. h b \<noteq> None \<longrightarrow> b \<noteq> a"
apply (drule new_AddrD)
apply auto
done

lemma new_Addr_SomeI: "h a = None \<Longrightarrow> \<exists>b. new_Addr h = Some b \<and> h b = None"
apply (unfold new_Addr_def)
apply (frule not_Some_eq [THEN iffD2])
apply auto
apply  (drule not_Some_eq [THEN iffD2])
apply  auto
apply (fast intro!: someI2)
done


subsection "initialization"

syntax

  init_vals     :: "('a, ty) table \<Rightarrow> ('a, val) table"

translations
 "init_vals vs"    == "option_map default_val \<circ> vs"

lemma init_arr_comps_base [simp]: "init_vals (arr_comps T 0) = empty"
apply (unfold arr_comps_def in_bounds_def)
apply (rule ext)
apply auto
done

lemma init_arr_comps_step [simp]: 
"0 < j \<Longrightarrow> init_vals (arr_comps T  j    ) =  
           init_vals (arr_comps T (j - 1))(j - 1\<mapsto>default_val T)"
apply (unfold arr_comps_def in_bounds_def)
apply (rule ext)
apply auto
done

subsection "update"

constdefs
  gupd       :: "oref  \<Rightarrow> obj \<Rightarrow> st \<Rightarrow> st"        ("gupd'(_\<mapsto>_')"[10,10]1000)
 "gupd r obj  \<equiv> st_case (\<lambda>g l. st (g(r\<mapsto>obj)) l)"

  lupd       :: "lname \<Rightarrow> val \<Rightarrow> st \<Rightarrow> st"        ("lupd'(_\<mapsto>_')"[10,10]1000)
 "lupd vn v   \<equiv> st_case (\<lambda>g l. st g (l(vn\<mapsto>v)))"

  upd_gobj   :: "oref \<Rightarrow> vn \<Rightarrow> val \<Rightarrow> st \<Rightarrow> st" 
 "upd_gobj r n v \<equiv> st_case (\<lambda>g l. st (chg_map (upd_obj n v) r g) l)"

  set_locals  :: "locals \<Rightarrow> st \<Rightarrow> st"
 "set_locals l \<equiv> st_case (\<lambda>g l'. st g l)"
  
  init_obj    :: "prog \<Rightarrow> obj_tag \<Rightarrow> oref \<Rightarrow> st \<Rightarrow> st"
 "init_obj G oi r \<equiv> gupd(r\<mapsto>\<lparr>tag=oi, values=init_vals (var_tys G oi r)\<rparr>)"

syntax
  init_class_obj :: "prog \<Rightarrow> qtname \<Rightarrow> st \<Rightarrow> st"

translations
 "init_class_obj G C" == "init_obj G arbitrary (Inr C)"

lemma gupd_def2 [simp]: "gupd(r\<mapsto>obj) (st g l) = st (g(r\<mapsto>obj)) l"
apply (unfold gupd_def)
apply (simp (no_asm))
done

lemma lupd_def2 [simp]: "lupd(vn\<mapsto>v) (st g l) = st g (l(vn\<mapsto>v))"
apply (unfold lupd_def)
apply (simp (no_asm))
done

lemma globs_gupd [simp]: "globs  (gupd(r\<mapsto>obj) s) = globs s(r\<mapsto>obj)"
apply (induct "s")
by (simp add: gupd_def)

lemma globs_lupd [simp]: "globs  (lupd(vn\<mapsto>v ) s) = globs  s"
apply (induct "s")
by (simp add: lupd_def)

lemma locals_gupd [simp]: "locals (gupd(r\<mapsto>obj) s) = locals s"
apply (induct "s")
by (simp add: gupd_def)

lemma locals_lupd [simp]: "locals (lupd(vn\<mapsto>v ) s) = locals s(vn\<mapsto>v )"
apply (induct "s")
by (simp add: lupd_def)

lemma globs_upd_gobj_new [rule_format (no_asm), simp]: 
  "globs s r = None \<longrightarrow> globs (upd_gobj r n v s) = globs s"
apply (unfold upd_gobj_def)
apply (induct "s")
apply auto
done

lemma globs_upd_gobj_upd [rule_format (no_asm), simp]: 
"globs s r=Some obj\<longrightarrow> globs (upd_gobj r n v s) = globs s(r\<mapsto>upd_obj n v obj)"
apply (unfold upd_gobj_def)
apply (induct "s")
apply auto
done

lemma locals_upd_gobj [simp]: "locals (upd_gobj r n v s) = locals s"
apply (induct "s")
by (simp add: upd_gobj_def) 


lemma globs_init_obj [simp]: "globs (init_obj G oi r s) t =  
  (if t=r then Some \<lparr>tag=oi,values=init_vals (var_tys G oi r)\<rparr> else globs s t)"
apply (unfold init_obj_def)
apply (simp (no_asm))
done

lemma locals_init_obj [simp]: "locals (init_obj G oi r s) = locals s"
by (simp add: init_obj_def)
  
lemma surjective_st [simp]: "st (globs s) (locals s) = s"
apply (induct "s")
by auto

lemma surjective_st_init_obj: 
 "st (globs (init_obj G oi r s)) (locals s) = init_obj G oi r s"
apply (subst locals_init_obj [THEN sym])
apply (rule surjective_st)
done

lemma heap_heap_upd [simp]: 
  "heap (st (g(Inl a\<mapsto>obj)) l) = heap (st g l)(a\<mapsto>obj)"
apply (rule ext)
apply (simp (no_asm))
done
lemma heap_stat_upd [simp]: "heap (st (g(Inr C\<mapsto>obj)) l) = heap (st g l)"
apply (rule ext)
apply (simp (no_asm))
done
lemma heap_local_upd [simp]: "heap (st g (l(vn\<mapsto>v))) = heap (st g l)"
apply (rule ext)
apply (simp (no_asm))
done

lemma heap_gupd_Heap [simp]: "heap (gupd(Heap a\<mapsto>obj) s) = heap s(a\<mapsto>obj)"
apply (rule ext)
apply (simp (no_asm))
done
lemma heap_gupd_Stat [simp]: "heap (gupd(Stat C\<mapsto>obj) s) = heap s"
apply (rule ext)
apply (simp (no_asm))
done
lemma heap_lupd [simp]: "heap (lupd(vn\<mapsto>v) s) = heap s"
apply (rule ext)
apply (simp (no_asm))
done

lemma heap_upd_gobj_Stat [simp]: "heap (upd_gobj (Stat C) n v s) = heap s"
apply (rule ext)
apply (simp (no_asm))
apply (case_tac "globs s (Stat C)")
apply  auto
done

lemma set_locals_def2 [simp]: "set_locals l (st g l') = st g l"
apply (unfold set_locals_def)
apply (simp (no_asm))
done

lemma set_locals_id [simp]: "set_locals (locals s) s = s"
apply (unfold set_locals_def)
apply (induct_tac "s")
apply (simp (no_asm))
done

lemma set_set_locals [simp]: "set_locals l (set_locals l' s) = set_locals l s"
apply (unfold set_locals_def)
apply (induct_tac "s")
apply (simp (no_asm))
done

lemma locals_set_locals [simp]: "locals (set_locals l s) = l"
apply (unfold set_locals_def)
apply (induct_tac "s")
apply (simp (no_asm))
done

lemma globs_set_locals [simp]: "globs (set_locals l s) = globs s"
apply (unfold set_locals_def)
apply (induct_tac "s")
apply (simp (no_asm))
done

lemma heap_set_locals [simp]: "heap (set_locals l s) = heap s"
apply (unfold heap_def)
apply (induct_tac "s")
apply (simp (no_asm))
done


section "abrupt completion"



consts

  the_Xcpt :: "abrupt \<Rightarrow> xcpt"
  the_Jump :: "abrupt => jump"
  the_Loc  :: "xcpt \<Rightarrow> loc"
  the_Std  :: "xcpt \<Rightarrow> xname"

primrec "the_Xcpt (Xcpt x) = x"
primrec "the_Jump (Jump j) = j"
primrec "the_Loc (Loc a) = a"
primrec "the_Std (Std x) = x"


	

constdefs
  abrupt_if    :: "bool \<Rightarrow> abopt \<Rightarrow> abopt \<Rightarrow> abopt"
 "abrupt_if c x' x \<equiv> if c \<and> (x = None) then x' else x"

lemma abrupt_if_True_None [simp]: "abrupt_if True x None = x"
by (simp add: abrupt_if_def)

lemma abrupt_if_True_not_None [simp]: "x \<noteq> None \<Longrightarrow> abrupt_if True x y \<noteq> None"
by (simp add: abrupt_if_def)

lemma abrupt_if_False [simp]: "abrupt_if False x y = y"
by (simp add: abrupt_if_def)

lemma abrupt_if_Some [simp]: "abrupt_if c x (Some y) = Some y"
by (simp add: abrupt_if_def)

lemma abrupt_if_not_None [simp]: "y \<noteq> None \<Longrightarrow> abrupt_if c x y = y"
apply (simp add: abrupt_if_def)
by auto


lemma split_abrupt_if: 
"P (abrupt_if c x' x) = 
      ((c \<and> x = None \<longrightarrow> P x') \<and> (\<not> (c \<and> x = None) \<longrightarrow> P x))"
apply (unfold abrupt_if_def)
apply (split split_if)
apply auto
done

syntax

  raise_if :: "bool \<Rightarrow> xname \<Rightarrow> abopt \<Rightarrow> abopt"
  np       :: "val  \<spacespace>        \<Rightarrow> abopt \<Rightarrow> abopt"
  check_neg:: "val  \<spacespace>        \<Rightarrow> abopt \<Rightarrow> abopt"
  error_if :: "bool \<Rightarrow> error \<Rightarrow> abopt \<Rightarrow> abopt"
  
translations

 "raise_if c xn" == "abrupt_if c (Some (Xcpt (Std xn)))"
 "np v"          == "raise_if (v = Null)      NullPointer"
 "check_neg i'"  == "raise_if (the_Intg i'<0) NegArrSize"
 "error_if c e"  == "abrupt_if c (Some (Error e))"

lemma raise_if_None [simp]: "(raise_if c x y = None) = (\<not>c \<and> y = None)"
apply (simp add: abrupt_if_def)
by auto
declare raise_if_None [THEN iffD1, dest!]

lemma if_raise_if_None [simp]: 
  "((if b then y else raise_if c x y) = None) = ((c \<longrightarrow> b) \<and> y = None)"
apply (simp add: abrupt_if_def)
apply auto
done

lemma raise_if_SomeD [dest!]:
  "raise_if c x y = Some z \<Longrightarrow> c \<and> z=(Xcpt (Std x)) \<and> y=None \<or> (y=Some z)"
apply (case_tac y)
apply (case_tac c)
apply (simp add: abrupt_if_def)
apply (simp add: abrupt_if_def)
apply auto
done

lemma error_if_None [simp]: "(error_if c e y = None) = (\<not>c \<and> y = None)"
apply (simp add: abrupt_if_def)
by auto
declare error_if_None [THEN iffD1, dest!]

lemma if_error_if_None [simp]: 
  "((if b then y else error_if c e y) = None) = ((c \<longrightarrow> b) \<and> y = None)"
apply (simp add: abrupt_if_def)
apply auto
done

lemma error_if_SomeD [dest!]:
  "error_if c e y = Some z \<Longrightarrow> c \<and> z=(Error e) \<and> y=None \<or> (y=Some z)"
apply (case_tac y)
apply (case_tac c)
apply (simp add: abrupt_if_def)
apply (simp add: abrupt_if_def)
apply auto
done

constdefs
   absorb :: "jump \<Rightarrow> abopt \<Rightarrow> abopt"
  "absorb j a \<equiv> if a=Some (Jump j) then None else a"

lemma absorb_SomeD [dest!]: "absorb j a = Some x \<Longrightarrow> a = Some x"
by (auto simp add: absorb_def)

lemma absorb_same [simp]: "absorb j (Some (Jump j)) = None"
by (auto simp add: absorb_def)

lemma absorb_other [simp]: "a \<noteq> Some (Jump j) \<Longrightarrow> absorb j a = a"
by (auto simp add: absorb_def)

lemma absorb_Some_NoneD: "absorb j (Some abr) = None \<Longrightarrow> abr = Jump j"
  by (simp add: absorb_def)

lemma absorb_Some_JumpD: "absorb j s = Some (Jump j') \<Longrightarrow> j'\<noteq>j"
  by (simp add: absorb_def)


section "full program state"

types
  state = "abopt \<times> st"          --{* state including abruption information *}

syntax 
  Norm   :: "st \<Rightarrow> state"
  abrupt :: "state \<Rightarrow> abopt"
  store  :: "state \<Rightarrow> st"

translations
   
  "Norm s"     == "(None,s)" 
  "abrupt"     => "fst"
  "store"      => "snd"
  "abopt"       <= (type) "State.abrupt option"
  "abopt"       <= (type) "abrupt option"
  "state"      <= (type) "abopt \<times> State.st"
  "state"      <= (type) "abopt \<times> st"



lemma single_stateE: "\<forall>Z. Z = (s::state) \<Longrightarrow> False"
apply (erule_tac x = "(Some k,y)" in all_dupE)
apply (erule_tac x = "(None,y)" in allE)
apply clarify
done

lemma state_not_single: "All (op = (x::state)) \<Longrightarrow> R"
apply (drule_tac x = "(if abrupt x = None then Some ?x else None,?y)" in spec)
apply clarsimp
done

constdefs

  normal     :: "state \<Rightarrow> bool"
 "normal \<equiv> \<lambda>s. abrupt s = None"

lemma normal_def2 [simp]: "normal s = (abrupt s = None)"
apply (unfold normal_def)
apply (simp (no_asm))
done

constdefs
  heap_free :: "nat \<Rightarrow> state \<Rightarrow> bool"
 "heap_free n \<equiv> \<lambda>s. atleast_free (heap (store s)) n"

lemma heap_free_def2 [simp]: "heap_free n s = atleast_free (heap (store s)) n"
apply (unfold heap_free_def)
apply simp
done

subsection "update"

constdefs
 
  abupd     :: "(abopt \<Rightarrow> abopt) \<Rightarrow> state \<Rightarrow> state"
 "abupd f \<equiv> prod_fun f id"

  supd     :: "(st \<Rightarrow> st) \<Rightarrow> state \<Rightarrow> state" 
 "supd \<equiv> prod_fun id"
  
lemma abupd_def2 [simp]: "abupd f (x,s) = (f x,s)"
by (simp add: abupd_def)

lemma abupd_abrupt_if_False [simp]: "\<And> s. abupd (abrupt_if False xo) s = s"
by simp

lemma supd_def2 [simp]: "supd f (x,s) = (x,f s)"
by (simp add: supd_def)

lemma supd_lupd [simp]: 
 "\<And> s. supd (lupd vn v ) s = (abrupt s,lupd vn v (store s))"
apply (simp (no_asm_simp) only: split_tupled_all)
apply (simp (no_asm))
done


lemma supd_gupd [simp]: 
 "\<And> s. supd (gupd r obj) s = (abrupt s,gupd r obj (store s))"
apply (simp (no_asm_simp) only: split_tupled_all)
apply (simp (no_asm))
done

lemma supd_init_obj [simp]: 
 "supd (init_obj G oi r) s = (abrupt s,init_obj G oi r (store s))"
apply (unfold init_obj_def)
apply (simp (no_asm))
done

lemma abupd_store_invariant [simp]: "store (abupd f s) = store s"
  by (cases s) simp

lemma supd_abrupt_invariant [simp]: "abrupt (supd f s) = abrupt s"
  by (cases s) simp

syntax

  set_lvars     :: "locals \<Rightarrow> state \<Rightarrow> state"
  restore_lvars :: "state  \<Rightarrow> state \<Rightarrow> state"
  
translations

 "set_lvars l" == "supd (set_locals l)"
 "restore_lvars s' s" == "set_lvars (locals (store s')) s"

lemma set_set_lvars [simp]: "\<And> s. set_lvars l (set_lvars l' s) = set_lvars l s"
apply (simp (no_asm_simp) only: split_tupled_all)
apply (simp (no_asm))
done

lemma set_lvars_id [simp]: "\<And> s. set_lvars (locals (store s)) s = s"
apply (simp (no_asm_simp) only: split_tupled_all)
apply (simp (no_asm))
done

section "initialisation test"

constdefs

  inited   :: "qtname \<Rightarrow> globs \<Rightarrow> bool"
 "inited C g \<equiv> g (Stat C) \<noteq> None"

  initd    :: "qtname \<Rightarrow> state \<Rightarrow> bool"
 "initd C \<equiv> inited C \<circ> globs \<circ> store"

lemma not_inited_empty [simp]: "\<not>inited C empty"
apply (unfold inited_def)
apply (simp (no_asm))
done

lemma inited_gupdate [simp]: "inited C (g(r\<mapsto>obj)) = (inited C g \<or> r = Stat C)"
apply (unfold inited_def)
apply (auto split add: st.split)
done

lemma inited_init_class_obj [intro!]: "inited C (globs (init_class_obj G C s))"
apply (unfold inited_def)
apply (simp (no_asm))
done

lemma not_initedD: "\<not> inited C g \<Longrightarrow> g (Stat C) = None"
apply (unfold inited_def)
apply (erule notnotD)
done

lemma initedD: "inited C g \<Longrightarrow> \<exists> obj. g (Stat C) = Some obj"
apply (unfold inited_def)
apply auto
done

lemma initd_def2 [simp]: "initd C s = inited C (globs (store s))"
apply (unfold initd_def)
apply (simp (no_asm))
done

section {* @{text error_free} *}
constdefs error_free:: "state \<Rightarrow> bool"
"error_free s \<equiv> \<not> (\<exists> err. abrupt s = Some (Error err))"

lemma error_free_Norm [simp,intro]: "error_free (Norm s)"
by (simp add: error_free_def)

lemma error_free_normal [simp,intro]: "normal s \<Longrightarrow> error_free s"
by (simp add: error_free_def)

lemma error_free_Xcpt [simp]: "error_free (Some (Xcpt x),s)"
by (simp add: error_free_def)

lemma error_free_Jump [simp,intro]: "error_free (Some (Jump j),s)"
by (simp add: error_free_def)

lemma error_free_Error [simp]: "error_free (Some (Error e),s) = False"
by (simp add: error_free_def)  

lemma error_free_Some [simp,intro]: 
 "\<not> (\<exists> err. x=Error err) \<Longrightarrow> error_free ((Some x),s)"
by (auto simp add: error_free_def)

lemma error_free_abupd_absorb [simp,intro]: 
 "error_free s \<Longrightarrow> error_free (abupd (absorb j) s)"
by (cases s) 
   (auto simp add: error_free_def absorb_def
         split: split_if_asm)

lemma error_free_absorb [simp,intro]: 
 "error_free (a,s) \<Longrightarrow> error_free (absorb j a, s)"
by (auto simp add: error_free_def absorb_def
            split: split_if_asm)

lemma error_free_abrupt_if [simp,intro]:
"\<lbrakk>error_free s; \<not> (\<exists> err. x=Error err)\<rbrakk>
 \<Longrightarrow> error_free (abupd (abrupt_if p (Some x)) s)"
by (cases s)
   (auto simp add: abrupt_if_def
            split: split_if)

lemma error_free_abrupt_if1 [simp,intro]:
"\<lbrakk>error_free (a,s); \<not> (\<exists> err. x=Error err)\<rbrakk>
 \<Longrightarrow> error_free (abrupt_if p (Some x) a, s)"
by  (auto simp add: abrupt_if_def
            split: split_if)

lemma error_free_abrupt_if_Xcpt [simp,intro]:
 "error_free s 
  \<Longrightarrow> error_free (abupd (abrupt_if p (Some (Xcpt x))) s)"
by simp 

lemma error_free_abrupt_if_Xcpt1 [simp,intro]:
 "error_free (a,s) 
  \<Longrightarrow> error_free (abrupt_if p (Some (Xcpt x)) a, s)" 
by simp 

lemma error_free_abrupt_if_Jump [simp,intro]:
 "error_free s 
  \<Longrightarrow> error_free (abupd (abrupt_if p (Some (Jump j))) s)" 
by simp

lemma error_free_abrupt_if_Jump1 [simp,intro]:
 "error_free (a,s) 
  \<Longrightarrow> error_free (abrupt_if p (Some (Jump j)) a, s)" 
by simp

lemma error_free_raise_if [simp,intro]:
 "error_free s \<Longrightarrow> error_free (abupd (raise_if p x) s)"
by simp 

lemma error_free_raise_if1 [simp,intro]:
 "error_free (a,s) \<Longrightarrow> error_free ((raise_if p x a), s)"
by simp 

lemma error_free_supd [simp,intro]:
 "error_free s \<Longrightarrow> error_free (supd f s)"
by (cases s) (simp add: error_free_def)

lemma error_free_supd1 [simp,intro]:
 "error_free (a,s) \<Longrightarrow> error_free (a,f s)"
by (simp add: error_free_def)

lemma error_free_set_lvars [simp,intro]:
"error_free s \<Longrightarrow> error_free ((set_lvars l) s)"
by (cases s) simp

lemma error_free_set_locals [simp,intro]: 
"error_free (x, s)
       \<Longrightarrow> error_free (x, set_locals l s')"
by (simp add: error_free_def)


end


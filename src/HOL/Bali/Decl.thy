(*  Title:      HOL/Bali/Decl.thy
    ID:         $Id$
    Author:     David von Oheimb and Norbert Schirmer
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)
header {* Field, method, interface, and class declarations, whole Java programs
*}

(** order is significant, because of clash for "var" **)
theory Decl = Term + Table:

text {*
improvements:
\begin{itemize}
\item clarification and correction of some aspects of the package/access concept
  (Also submitted as bug report to the Java Bug Database:
   Bug Id: 4485402 and Bug Id: 4493343 
   http://developer.java.sun.com/developer/bugParade/index.jshtml
  )
\end{itemize}
simplifications:
\begin{itemize}
\item the only field and method modifiers are static and the access modifiers
\item no constructors, which may be simulated by new + suitable methods
\item there is just one global initializer per class, which can simulate all 
      others

\item no throws clause
\item a void method is replaced by one that returns Unit (of dummy type Void)

\item no interface fields

\item every class has an explicit superclass (unused for Object)
\item the (standard) methods of Object and of standard exceptions are not 
      specified

\item no main method
\end{itemize}
*}

subsection {* Modifier*}

subsubsection {* Access modifier *}

datatype acc_modi (* access modifier *)
         = Private | Package | Protected | Public 

text {* 
We can define a linear order for the access modifiers. With Private yielding the
most restrictive access and public the most liberal access policy:
  Private < Package < Protected < Public
*}
 
instance acc_modi:: ord ..

defs (overloaded)
less_acc_def: 
 "a < (b::acc_modi) 
      \<equiv> (case a of
             Private    \<Rightarrow> (b=Package \<or> b=Protected \<or> b=Public)
           | Package    \<Rightarrow> (b=Protected \<or> b=Public)
           | Protected  \<Rightarrow> (b=Public)
           | Public     \<Rightarrow> False)"
le_acc_def:
 "a \<le> (b::acc_modi) \<equiv> (a = b) \<or> (a < b)"

instance acc_modi:: order
proof
  fix x y z::acc_modi
  {
  show "x \<le> x"               \<spacespace>\<spacespace>    -- reflexivity
    by (auto simp add: le_acc_def)
  next
  assume "x \<le> y" "y \<le> z"           -- transitivity 
  thus "x \<le> z"
    by (auto simp add: le_acc_def less_acc_def split add: acc_modi.split)
  next
  assume "x \<le> y" "y \<le> x"           -- antisymmetry
  thus "x = y"
  proof -
    have "\<forall> x y. x < (y::acc_modi) \<and> y < x \<longrightarrow> False"
      by (auto simp add: less_acc_def split add: acc_modi.split)
    with prems show ?thesis
      by  (auto simp add: le_acc_def)
  qed
  next
  show "(x < y) = (x \<le> y \<and> x \<noteq> y)"
    by (auto simp add: le_acc_def less_acc_def split add: acc_modi.split) 
  }
qed
  
instance acc_modi:: linorder
proof
  fix x y:: acc_modi
  show  "x \<le> y \<or> y \<le> x"   
  by (auto simp add: less_acc_def le_acc_def split add: acc_modi.split)
qed

lemma acc_modi_top [simp]: "Public \<le> a \<Longrightarrow> a = Public"
by (auto simp add: le_acc_def less_acc_def split: acc_modi.splits)

lemma acc_modi_top1 [simp, intro!]: "a \<le> Public"
by (auto simp add: le_acc_def less_acc_def split: acc_modi.splits)

lemma acc_modi_le_Public: 
"a \<le> Public \<Longrightarrow> a=Private \<or> a = Package \<or> a=Protected \<or> a=Public"
by (auto simp add: le_acc_def less_acc_def split: acc_modi.splits)

lemma acc_modi_bottom: "a \<le> Private \<Longrightarrow> a = Private"
by (auto simp add: le_acc_def less_acc_def split: acc_modi.splits)

lemma acc_modi_Private_le: 
"Private \<le> a \<Longrightarrow> a=Private \<or> a = Package \<or> a=Protected \<or> a=Public"
by (auto simp add: le_acc_def less_acc_def split: acc_modi.splits)

lemma acc_modi_Package_le: 
  "Package \<le> a \<Longrightarrow> a = Package \<or> a=Protected \<or> a=Public"
by (auto simp add: le_acc_def less_acc_def split: acc_modi.split)

lemma acc_modi_le_Package: 
  "a \<le> Package \<Longrightarrow> a=Private \<or> a = Package"
by (auto simp add: le_acc_def less_acc_def split: acc_modi.splits)

lemma acc_modi_Protected_le: 
  "Protected \<le> a \<Longrightarrow> a=Protected \<or> a=Public"
by (auto simp add: le_acc_def less_acc_def split: acc_modi.splits)

lemma acc_modi_le_Protected: 
  "a \<le> Protected  \<Longrightarrow> a=Private \<or> a = Package \<or> a = Protected"
by (auto simp add: le_acc_def less_acc_def split: acc_modi.splits)


lemmas acc_modi_le_Dests = acc_modi_top           acc_modi_le_Public
                           acc_modi_Private_le    acc_modi_bottom
                           acc_modi_Package_le    acc_modi_le_Package
                           acc_modi_Protected_le  acc_modi_le_Protected

lemma acc_modi_Package_le_cases 
 [consumes 1,case_names Package Protected Public]:
 "Package \<le> m \<Longrightarrow> ( m = Package \<Longrightarrow> P m) \<Longrightarrow> (m=Protected \<Longrightarrow> P m) \<Longrightarrow> 
   (m=Public \<Longrightarrow> P m) \<Longrightarrow> P m"
by (auto dest: acc_modi_Package_le)


subsubsection {* Static Modifier *}
types stat_modi = bool (* modifier: static *)

subsection {* Declaration (base "class" for member,interface and class
 declarations *}

record decl =
        access :: acc_modi

translations
  "decl" <= (type) "\<lparr>access::acc_modi\<rparr>"
  "decl" <= (type) "\<lparr>access::acc_modi,\<dots>::'a\<rparr>"

subsection {* Member (field or method)*}
record  member = decl +
         static :: stat_modi

translations
  "member" <= (type) "\<lparr>access::acc_modi,static::bool\<rparr>"
  "member" <= (type) "\<lparr>access::acc_modi,static::bool,\<dots>::'a\<rparr>"

subsection {* Field *}

record field = member +
        type :: ty
translations
  "field" <= (type) "\<lparr>access::acc_modi, static::bool, type::ty\<rparr>"
  "field" <= (type) "\<lparr>access::acc_modi, static::bool, type::ty,\<dots>::'a\<rparr>"

types     
        fdecl           (* field declaration, cf. 8.3 *)
	= "vname \<times> field"


translations
  "fdecl" <= (type) "vname \<times> field"

subsection  {* Method *}

record mhead = member +     (* method head (excluding signature) *)
        pars ::"vname list" (* parameter names *)
        resT ::ty           (* result type *)

record mbody =                      (* method body *)
        lcls::  "(vname \<times> ty) list" (* local variables *)
        stmt:: stmt                 (* the body statement *)

record methd = mhead + (* method in a class *)
        mbody::mbody

types mdecl = "sig \<times> methd"  (* method declaration in a class *)


translations
  "mhead" <= (type) "\<lparr>access::acc_modi, static::bool, 
                      pars::vname list, resT::ty\<rparr>"
  "mhead" <= (type) "\<lparr>access::acc_modi, static::bool, 
                      pars::vname list, resT::ty,\<dots>::'a\<rparr>"
  "mbody" <= (type) "\<lparr>lcls::(vname \<times> ty) list,stmt::stmt\<rparr>"
  "mbody" <= (type) "\<lparr>lcls::(vname \<times> ty) list,stmt::stmt,\<dots>::'a\<rparr>"      
  "methd" <= (type) "\<lparr>access::acc_modi, static::bool, 
                      pars::vname list, resT::ty,mbody::mbody\<rparr>"
  "methd" <= (type) "\<lparr>access::acc_modi, static::bool, 
                      pars::vname list, resT::ty,mbody::mbody,\<dots>::'a\<rparr>"
  "mdecl" <= (type) "sig \<times> methd"


constdefs 
  mhead::"methd \<Rightarrow> mhead"
  "mhead m \<equiv> \<lparr>access=access m, static=static m, pars=pars m, resT=resT m\<rparr>"

lemma access_mhead [simp]:"access (mhead m) = access m"
by (simp add: mhead_def)

lemma static_mhead [simp]:"static (mhead m) = static m"
by (simp add: mhead_def)

lemma pars_mhead [simp]:"pars (mhead m) = pars m"
by (simp add: mhead_def)

lemma resT_mhead [simp]:"resT (mhead m) = resT m"
by (simp add: mhead_def)

text {* To be able to talk uniformaly about field and method declarations we
introduce the notion of a member declaration (e.g. useful to define 
accessiblity ) *}

datatype memberdecl = fdecl fdecl | mdecl mdecl

datatype memberid = fid vname | mid sig

axclass has_memberid < "type"
consts
 memberid :: "'a::has_memberid \<Rightarrow> memberid"

instance memberdecl::has_memberid ..

defs (overloaded)
memberdecl_memberid_def:
  "memberid m \<equiv> (case m of
                    fdecl (vn,f)  \<Rightarrow> fid vn
                  | mdecl (sig,m) \<Rightarrow> mid sig)"

lemma memberid_fdecl_simp[simp]: "memberid (fdecl (vn,f)) = fid vn"
by (simp add: memberdecl_memberid_def)

lemma memberid_fdecl_simp1: "memberid (fdecl f) = fid (fst f)"
by (cases f) (simp add: memberdecl_memberid_def)

lemma memberid_mdecl_simp[simp]: "memberid (mdecl (sig,m)) = mid sig"
by (simp add: memberdecl_memberid_def)

lemma memberid_mdecl_simp1: "memberid (mdecl m) = mid (fst m)"
by (cases m) (simp add: memberdecl_memberid_def)

instance * :: (type, has_memberid) has_memberid ..

defs (overloaded)
pair_memberid_def:
  "memberid p \<equiv> memberid (snd p)"

lemma memberid_pair_simp[simp]: "memberid (c,m) = memberid m"
by (simp add: pair_memberid_def)

lemma memberid_pair_simp1: "memberid p  = memberid (snd p)"
by (simp add: pair_memberid_def)

constdefs is_field :: "qtname \<times> memberdecl \<Rightarrow> bool"
"is_field m \<equiv> \<exists> declC f. m=(declC,fdecl f)"
  
lemma is_fieldD: "is_field m \<Longrightarrow> \<exists> declC f. m=(declC,fdecl f)"
by (simp add: is_field_def)

lemma is_fieldI: "is_field (C,fdecl f)"
by (simp add: is_field_def)

constdefs is_method :: "qtname \<times> memberdecl \<Rightarrow> bool"
"is_method membr \<equiv> \<exists> declC m. membr=(declC,mdecl m)"
  
lemma is_methodD: "is_method membr \<Longrightarrow> \<exists> declC m. membr=(declC,mdecl m)"
by (simp add: is_method_def)

lemma is_methodI: "is_method (C,mdecl m)"
by (simp add: is_method_def)


subsection {* Interface *}


record  ibody = decl +  (* interface body *)
          imethods :: "(sig \<times> mhead) list" (* method heads *)

record  iface = ibody + (* interface *)
         isuperIfs:: "qtname list" (* superinterface list *)
types	
	idecl           (* interface declaration, cf. 9.1 *)
	= "qtname \<times> iface"

translations
  "ibody" <= (type) "\<lparr>access::acc_modi,imethods::(sig \<times> mhead) list\<rparr>"
  "ibody" <= (type) "\<lparr>access::acc_modi,imethods::(sig \<times> mhead) list,\<dots>::'a\<rparr>"
  "iface" <= (type) "\<lparr>access::acc_modi,imethods::(sig \<times> mhead) list,
                      isuperIfs::qtname list\<rparr>"
  "iface" <= (type) "\<lparr>access::acc_modi,imethods::(sig \<times> mhead) list,
                      isuperIfs::qtname list,\<dots>::'a\<rparr>"
  "idecl" <= (type) "qtname \<times> iface"

constdefs
  ibody :: "iface \<Rightarrow> ibody"
  "ibody i \<equiv> \<lparr>access=access i,imethods=imethods i\<rparr>"

lemma access_ibody [simp]: "(access (ibody i)) = access i"
by (simp add: ibody_def)

lemma imethods_ibody [simp]: "(imethods (ibody i)) = imethods i"
by (simp add: ibody_def)

subsection  {* Class *}
record cbody = decl +          (* class body *)
         cfields:: "fdecl list" 
         methods:: "mdecl list"
         init   :: "stmt"       (* initializer *)

record class = cbody +           (* class *)
        super   :: "qtname"      (* superclass *)
        superIfs:: "qtname list" (* implemented interfaces *)
types	
	cdecl           (* class declaration, cf. 8.1 *)
	= "qtname \<times> class"

translations
  "cbody" <= (type) "\<lparr>access::acc_modi,cfields::fdecl list,
                      methods::mdecl list,init::stmt\<rparr>"
  "cbody" <= (type) "\<lparr>access::acc_modi,cfields::fdecl list,
                      methods::mdecl list,init::stmt,\<dots>::'a\<rparr>"
  "class" <= (type) "\<lparr>access::acc_modi,cfields::fdecl list,
                      methods::mdecl list,init::stmt,
                      super::qtname,superIfs::qtname list\<rparr>"
  "class" <= (type) "\<lparr>access::acc_modi,cfields::fdecl list,
                      methods::mdecl list,init::stmt,
                      super::qtname,superIfs::qtname list,\<dots>::'a\<rparr>"
  "cdecl" <= (type) "qtname \<times> class"

constdefs
  cbody :: "class \<Rightarrow> cbody"
  "cbody c \<equiv> \<lparr>access=access c, cfields=cfields c,methods=methods c,init=init c\<rparr>"

lemma access_cbody [simp]:"access (cbody c) = access c"
by (simp add: cbody_def)

lemma cfields_cbody [simp]:"cfields (cbody c) = cfields c"
by (simp add: cbody_def)

lemma methods_cbody [simp]:"methods (cbody c) = methods c"
by (simp add: cbody_def)

lemma init_cbody [simp]:"init (cbody c) = init c"
by (simp add: cbody_def)


section "standard classes"

consts

  Object_mdecls  ::  "mdecl list" (* methods of Object *)
  SXcpt_mdecls   ::  "mdecl list" (* methods of SXcpts *)
  ObjectC ::         "cdecl"      (* declaration  of root      class   *)
  SXcptC  ::"xname \<Rightarrow> cdecl"      (* declarations of throwable classes *)

defs 


ObjectC_def:"ObjectC  \<equiv> (Object,\<lparr>access=Public,cfields=[],methods=Object_mdecls,
                                  init=Skip,super=arbitrary,superIfs=[]\<rparr>)"
SXcptC_def:"SXcptC xn\<equiv> (SXcpt xn,\<lparr>access=Public,cfields=[],methods=SXcpt_mdecls,
                                   init=Skip,
                                   super=if xn = Throwable then Object 
                                                           else SXcpt Throwable,
                                   superIfs=[]\<rparr>)"

lemma ObjectC_neq_SXcptC [simp]: "ObjectC \<noteq> SXcptC xn"
by (simp add: ObjectC_def SXcptC_def Object_def SXcpt_def)

lemma SXcptC_inject [simp]: "(SXcptC xn = SXcptC xm) = (xn = xm)"
apply (simp add: SXcptC_def)
apply auto
done

constdefs standard_classes :: "cdecl list"
         "standard_classes \<equiv> [ObjectC, SXcptC Throwable,
		SXcptC NullPointer, SXcptC OutOfMemory, SXcptC ClassCast,
		SXcptC NegArrSize , SXcptC IndOutBound, SXcptC ArrStore]"


section "programs"

record prog =
        ifaces ::"idecl list"
        "classes"::"cdecl list"

translations
     "prog"<= (type) "\<lparr>ifaces::idecl list,classes::cdecl list\<rparr>"
     "prog"<= (type) "\<lparr>ifaces::idecl list,classes::cdecl list,\<dots>::'a\<rparr>"

syntax
  iface     :: "prog  \<Rightarrow> (qtname, iface) table"
  class     :: "prog  \<Rightarrow> (qtname, class) table"
  is_iface  :: "prog  \<Rightarrow> qtname  \<Rightarrow> bool"
  is_class  :: "prog  \<Rightarrow> qtname  \<Rightarrow> bool"

translations
	   "iface G I" == "table_of (ifaces G) I"
	   "class G C" == "table_of (classes G) C"
	"is_iface G I" == "iface G I \<noteq> None"
	"is_class G C" == "class G C \<noteq> None"


section "is type"

consts
  is_type :: "prog \<Rightarrow>     ty \<Rightarrow> bool"
  isrtype :: "prog \<Rightarrow> ref_ty \<Rightarrow> bool"

primrec	"is_type G (PrimT pt)  = True"
	"is_type G (RefT  rt)  = isrtype G rt"
	"isrtype G (NullT    ) = True"
	"isrtype G (IfaceT tn) = is_iface G tn"
	"isrtype G (ClassT tn) = is_class G tn"
	"isrtype G (ArrayT T ) = is_type  G T"

lemma type_is_iface: "is_type G (Iface I) \<Longrightarrow> is_iface G I"
by auto

lemma type_is_class: "is_type G (Class C) \<Longrightarrow>  is_class G C"
by auto


section "subinterface and subclass relation, in anticipation of TypeRel.thy"

consts 
  subint1  :: "prog \<Rightarrow> (qtname \<times> qtname) set"
  subcls1  :: "prog \<Rightarrow> (qtname \<times> qtname) set"

defs
  subint1_def: "subint1 G \<equiv> {(I,J). \<exists>i\<in>iface G I: J\<in>set (isuperIfs i)}"
  subcls1_def: "subcls1 G \<equiv> {(C,D). C\<noteq>Object \<and> (\<exists>c\<in>class G C: super c = D)}"

syntax
 "@subcls1" :: "prog => [qtname, qtname] => bool" ("_|-_<:C1_" [71,71,71] 70)
 "@subclseq":: "prog => [qtname, qtname] => bool" ("_|-_<=:C _"[71,71,71] 70)
 "@subcls"  :: "prog => [qtname, qtname] => bool" ("_|-_<:C _"[71,71,71] 70)

syntax (xsymbols)
  "@subcls1" :: "prog \<Rightarrow> [qtname, qtname] \<Rightarrow> bool" ("_\<turnstile>_\<prec>\<^sub>C\<^sub>1_"  [71,71,71] 70)
  "@subclseq":: "prog \<Rightarrow> [qtname, qtname] \<Rightarrow> bool" ("_\<turnstile>_\<preceq>\<^sub>C _"  [71,71,71] 70)
  "@subcls"  :: "prog \<Rightarrow> [qtname, qtname] \<Rightarrow> bool" ("_\<turnstile>_\<prec>\<^sub>C _"  [71,71,71] 70)

translations
        "G\<turnstile>C \<prec>\<^sub>C\<^sub>1 D" == "(C,D) \<in> subcls1 G"
	"G\<turnstile>C \<preceq>\<^sub>C  D" == "(C,D) \<in>(subcls1 G)^*" (* cf. 8.1.3 *)
        "G\<turnstile>C \<prec>\<^sub>C  D" == "(C,D) \<in>(subcls1 G)^+"
 

lemma subint1I: "\<lbrakk>iface G I = Some i; J \<in> set (isuperIfs i)\<rbrakk> 
                 \<Longrightarrow> (I,J) \<in> subint1 G" 
apply (simp add: subint1_def)
done

lemma subcls1I:"\<lbrakk>class G C = Some c; C \<noteq> Object\<rbrakk> \<Longrightarrow> (C,(super c)) \<in> subcls1 G"
apply (simp add: subcls1_def)
done


lemma subint1D: "(I,J)\<in>subint1 G\<Longrightarrow> \<exists>i\<in>iface G I: J\<in>set (isuperIfs i)"
by (simp add: subint1_def)

lemma subcls1D: 
  "(C,D)\<in>subcls1 G \<Longrightarrow> C\<noteq>Object \<and> (\<exists>c. class G C = Some c \<and> (super c = D))"
apply (simp add: subcls1_def)
apply auto
done

lemma subint1_def2:  
   "subint1 G = (\<Sigma> I\<in>{I. is_iface G I}. set (isuperIfs (the (iface G I))))"
apply (unfold subint1_def)
apply auto
done

lemma subcls1_def2: 
 "subcls1 G = (\<Sigma>C\<in>{C. is_class G C}. {D. C\<noteq>Object \<and> super (the(class G C))=D})"
apply (unfold subcls1_def)
apply auto
done

lemma subcls_is_class:
"\<lbrakk>G\<turnstile>C \<prec>\<^sub>C D\<rbrakk> \<Longrightarrow> \<exists> c. class G C = Some c"
by (auto simp add: subcls1_def dest: tranclD)

lemma no_subcls1_Object:"G\<turnstile>Object\<prec>\<^sub>C\<^sub>1 D \<Longrightarrow> P"
by (auto simp add: subcls1_def)

lemma no_subcls_Object: "G\<turnstile>Object\<prec>\<^sub>C D \<Longrightarrow> P"
apply (erule trancl_induct)
apply (auto intro: no_subcls1_Object)
done

section "well-structured programs"

constdefs
  ws_idecl :: "prog \<Rightarrow> qtname \<Rightarrow> qtname list \<Rightarrow> bool"
 "ws_idecl G I si \<equiv> \<forall>J\<in>set si.  is_iface G J   \<and> (J,I)\<notin>(subint1 G)^+"
  
  ws_cdecl :: "prog \<Rightarrow> qtname \<Rightarrow> qtname \<Rightarrow> bool"
 "ws_cdecl G C sc \<equiv> C\<noteq>Object \<longrightarrow> is_class G sc \<and> (sc,C)\<notin>(subcls1 G)^+"
  
  ws_prog  :: "prog \<Rightarrow> bool"
 "ws_prog G \<equiv> (\<forall>(I,i)\<in>set (ifaces  G). ws_idecl G I (isuperIfs i)) \<and> 
	      (\<forall>(C,c)\<in>set (classes G). ws_cdecl G C (super c))"


lemma ws_progI: 
"\<lbrakk>\<forall>(I,i)\<in>set (ifaces G). \<forall>J\<in>set (isuperIfs i). is_iface G J \<and> 
                                                (J,I) \<notin> (subint1 G)^+; 
  \<forall>(C,c)\<in>set (classes G). C\<noteq>Object \<longrightarrow> is_class G (super c) \<and> 
                                        ((super c),C) \<notin> (subcls1 G)^+  
 \<rbrakk> \<Longrightarrow> ws_prog G"
apply (unfold ws_prog_def ws_idecl_def ws_cdecl_def)
apply (erule_tac conjI)
apply blast
done

lemma ws_prog_ideclD: 
"\<lbrakk>iface G I = Some i; J\<in>set (isuperIfs i); ws_prog G\<rbrakk> \<Longrightarrow>  
  is_iface G J \<and> (J,I)\<notin>(subint1 G)^+"
apply (unfold ws_prog_def ws_idecl_def)
apply clarify
apply (drule_tac map_of_SomeD)
apply auto
done

lemma ws_prog_cdeclD: 
"\<lbrakk>class G C = Some c; C\<noteq>Object; ws_prog G\<rbrakk> \<Longrightarrow>  
  is_class G (super c) \<and> (super c,C)\<notin>(subcls1 G)^+"
apply (unfold ws_prog_def ws_cdecl_def)
apply clarify
apply (drule_tac map_of_SomeD)
apply auto
done


section "well-foundedness"

lemma finite_is_iface: "finite {I. is_iface G I}"
apply (fold dom_def)
apply (rule_tac finite_dom_map_of)
done

lemma finite_is_class: "finite {C. is_class G C}"
apply (fold dom_def)
apply (rule_tac finite_dom_map_of)
done

lemma finite_subint1: "finite (subint1 G)"
apply (subst subint1_def2)
apply (rule finite_SigmaI)
apply (rule finite_is_iface)
apply (simp (no_asm))
done

lemma finite_subcls1: "finite (subcls1 G)"
apply (subst subcls1_def2)
apply (rule finite_SigmaI)
apply (rule finite_is_class)
apply (rule_tac B = "{super (the (class G C))}" in finite_subset)
apply  auto
done

lemma subint1_irrefl_lemma1: 
  "ws_prog G \<Longrightarrow> (subint1 G)^-1 \<inter> (subint1 G)^+ = {}"
apply (force dest: subint1D ws_prog_ideclD conjunct2)
done

lemma subcls1_irrefl_lemma1: 
  "ws_prog G \<Longrightarrow> (subcls1 G)^-1 \<inter> (subcls1 G)^+ = {}"
apply (force dest: subcls1D ws_prog_cdeclD conjunct2)
done

lemmas subint1_irrefl_lemma2 = subint1_irrefl_lemma1 [THEN irrefl_tranclI']
lemmas subcls1_irrefl_lemma2 = subcls1_irrefl_lemma1 [THEN irrefl_tranclI']

lemma subint1_irrefl: "\<lbrakk>(x, y) \<in> subint1 G; ws_prog G\<rbrakk> \<Longrightarrow> x \<noteq> y"
apply (rule irrefl_trancl_rD)
apply (rule subint1_irrefl_lemma2)
apply auto
done

lemma subcls1_irrefl: "\<lbrakk>(x, y) \<in> subcls1 G; ws_prog G\<rbrakk> \<Longrightarrow> x \<noteq> y"
apply (rule irrefl_trancl_rD)
apply (rule subcls1_irrefl_lemma2)
apply auto
done

lemmas subint1_acyclic = subint1_irrefl_lemma2 [THEN acyclicI, standard]
lemmas subcls1_acyclic = subcls1_irrefl_lemma2 [THEN acyclicI, standard]


lemma wf_subint1: "ws_prog G \<Longrightarrow> wf ((subint1 G)\<inverse>)"
by (auto intro: finite_acyclic_wf_converse finite_subint1 subint1_acyclic)

lemma wf_subcls1: "ws_prog G \<Longrightarrow> wf ((subcls1 G)\<inverse>)"
by (auto intro: finite_acyclic_wf_converse finite_subcls1 subcls1_acyclic)


lemma subint1_induct: 
  "\<lbrakk>ws_prog G; \<And>x. \<forall>y. (x, y) \<in> subint1 G \<longrightarrow> P y \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> P a"
apply (frule wf_subint1)
apply (erule wf_induct)
apply (simp (no_asm_use) only: converse_iff)
apply blast
done

lemma subcls1_induct [consumes 1]:
  "\<lbrakk>ws_prog G; \<And>x. \<forall>y. (x, y) \<in> subcls1 G \<longrightarrow> P y \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> P a"
apply (frule wf_subcls1)
apply (erule wf_induct)
apply (simp (no_asm_use) only: converse_iff)
apply blast
done

lemma ws_subint1_induct: 
 "\<lbrakk>is_iface G I; ws_prog G; \<And>I i. \<lbrakk>iface G I = Some i \<and> 
   (\<forall>J \<in> set (isuperIfs i). (I,J)\<in>subint1 G \<and> P J \<and> is_iface G J)\<rbrakk> \<Longrightarrow> P I
  \<rbrakk> \<Longrightarrow> P I"
apply (erule make_imp)
apply (rule subint1_induct)
apply  assumption
apply safe
apply (fast dest: subint1I ws_prog_ideclD)
done


lemma ws_subcls1_induct: "\<lbrakk>is_class G C; ws_prog G;  
  \<And>C c. \<lbrakk>class G C = Some c;  
 (C \<noteq> Object \<longrightarrow> (C,(super c))\<in>subcls1 G \<and> 
                  P (super c) \<and> is_class G (super c))\<rbrakk> \<Longrightarrow> P C
 \<rbrakk> \<Longrightarrow> P C"
apply (erule make_imp)
apply (rule subcls1_induct)
apply  assumption
apply safe
apply (fast dest: subcls1I ws_prog_cdeclD)
done

lemma ws_class_induct [consumes 2, case_names Object Subcls]:
"\<lbrakk>class G C = Some c; ws_prog G; 
  \<And> co. class G Object = Some co \<Longrightarrow> P Object; 
  \<And>  C c. \<lbrakk>class G C = Some c; C \<noteq> Object; P (super c)\<rbrakk> \<Longrightarrow> P C
 \<rbrakk> \<Longrightarrow> P C"
proof -
  assume clsC: "class G C = Some c"
  and    init: "\<And> co. class G Object = Some co \<Longrightarrow> P Object"
  and    step: "\<And>   C c. \<lbrakk>class G C = Some c; C \<noteq> Object; P (super c)\<rbrakk> \<Longrightarrow> P C"
  assume ws: "ws_prog G"
  then have "is_class G C \<Longrightarrow> P C"  
  proof (induct rule: subcls1_induct)
    fix C
    assume   hyp:"\<forall> S. G\<turnstile>C \<prec>\<^sub>C\<^sub>1 S \<longrightarrow> is_class G S \<longrightarrow> P S"
       and iscls:"is_class G C"
    show "P C"
    proof (cases "C=Object")
      case True with iscls init show "P C" by auto
    next
      case False with ws step hyp iscls 
      show "P C" by (auto dest: subcls1I ws_prog_cdeclD)
    qed
  qed
  with clsC show ?thesis by simp
qed

lemma ws_class_induct' [consumes 2, case_names Object Subcls]:
"\<lbrakk>is_class G C; ws_prog G; 
  \<And> co. class G Object = Some co \<Longrightarrow> P Object; 
  \<And> C c. \<lbrakk>class G C = Some c; C \<noteq> Object; P (super c)\<rbrakk> \<Longrightarrow> P C
 \<rbrakk> \<Longrightarrow> P C"
by (blast intro: ws_class_induct)

lemma ws_class_induct'' [consumes 2, case_names Object Subcls]:
"\<lbrakk>class G C = Some c; ws_prog G; 
  \<And> co. class G Object = Some co \<Longrightarrow> P Object co; 
  \<And>  C c sc. \<lbrakk>class G C = Some c; class G (super c) = Some sc;
            C \<noteq> Object; P (super c) sc\<rbrakk> \<Longrightarrow> P C c
 \<rbrakk> \<Longrightarrow> P C c"
proof -
  assume clsC: "class G C = Some c"
  and    init: "\<And> co. class G Object = Some co \<Longrightarrow> P Object co"
  and    step: "\<And> C c sc . \<lbrakk>class G C = Some c; class G (super c) = Some sc;
                             C \<noteq> Object; P (super c) sc\<rbrakk> \<Longrightarrow> P C c"
  assume ws: "ws_prog G"
  then have "\<And> c. class G C = Some c\<Longrightarrow> P C c"  
  proof (induct rule: subcls1_induct)
    fix C c
    assume   hyp:"\<forall> S. G\<turnstile>C \<prec>\<^sub>C\<^sub>1 S \<longrightarrow> (\<forall> s. class G S = Some s \<longrightarrow> P S s)"
       and iscls:"class G C = Some c"
    show "P C c"
    proof (cases "C=Object")
      case True with iscls init show "P C c" by auto
    next
      case False
      with ws iscls obtain sc where
	sc: "class G (super c) = Some sc"
	by (auto dest: ws_prog_cdeclD)
      from iscls False have "G\<turnstile>C \<prec>\<^sub>C\<^sub>1 (super c)" by (rule subcls1I)
      with False ws step hyp iscls sc
      show "P C c" 
	by (auto)  
    qed
  qed
  with clsC show "P C c" by auto
qed

lemma ws_interface_induct [consumes 2, case_names Step]:
  assumes is_if_I: "is_iface G I" and 
               ws: "ws_prog G" and
          hyp_sub: "\<And>I i. \<lbrakk>iface G I = Some i; 
                            \<forall> J \<in> set (isuperIfs i).
                                 (I,J)\<in>subint1 G \<and> P J \<and> is_iface G J\<rbrakk> \<Longrightarrow> P I"
  shows "P I"
proof -
  from is_if_I ws 
  show "P I"
  proof (rule ws_subint1_induct)
    fix I i
    assume hyp: "iface G I = Some i \<and>
                (\<forall>J\<in>set (isuperIfs i). (I,J) \<in>subint1 G \<and> P J \<and> is_iface G J)"
    then have if_I: "iface G I = Some i"
      by blast
    show "P I"
    proof (cases "isuperIfs i")
      case Nil
      with if_I hyp_sub 
      show "P I" 
	by auto
    next
      case (Cons hd tl)
      with hyp if_I hyp_sub 
      show "P I" 
	by auto
    qed
  qed
qed

section "general recursion operators for the interface and class hiearchies"

consts
  iface_rec  :: "prog \<times> qtname \<Rightarrow>   \<spacespace>  (qtname \<Rightarrow> iface \<Rightarrow> 'a set \<Rightarrow> 'a) \<Rightarrow> 'a"
  class_rec  :: "prog \<times> qtname \<Rightarrow> 'a \<Rightarrow> (qtname \<Rightarrow> class \<Rightarrow> 'a     \<Rightarrow> 'a) \<Rightarrow> 'a"

recdef iface_rec "same_fst ws_prog (\<lambda>G. (subint1 G)^-1)" 
"iface_rec (G,I) = 
  (\<lambda>f. case iface G I of 
         None \<Rightarrow> arbitrary 
       | Some i \<Rightarrow> if ws_prog G 
                      then f I i 
                               ((\<lambda>J. iface_rec (G,J) f)`set (isuperIfs i))
                      else arbitrary)"
(hints recdef_wf: wf_subint1 intro: subint1I)
declare iface_rec.simps [simp del]

lemma iface_rec: 
"\<lbrakk>iface G I = Some i; ws_prog G\<rbrakk> \<Longrightarrow> 
 iface_rec (G,I) f = f I i ((\<lambda>J. iface_rec (G,J) f)`set (isuperIfs i))"
apply (subst iface_rec.simps)
apply simp
done

recdef class_rec "same_fst ws_prog (\<lambda>G. (subcls1 G)^-1)"
"class_rec(G,C) = 
  (\<lambda>t f. case class G C of 
           None \<Rightarrow> arbitrary 
         | Some c \<Rightarrow> if ws_prog G 
                        then f C c 
                                 (if C = Object then t 
                                                else class_rec (G,super c) t f)
                        else arbitrary)"
(hints recdef_wf: wf_subcls1 intro: subcls1I)
declare class_rec.simps [simp del]

lemma class_rec: "\<lbrakk>class G C = Some c; ws_prog G\<rbrakk> \<Longrightarrow>  
 class_rec (G,C) t f = 
   f C c (if C = Object then t else class_rec (G,super c) t f)"
apply (rule class_rec.simps [THEN trans [THEN fun_cong [THEN fun_cong]]])
apply simp
done
(*
lemma bar:
 "[| P;  !!x.  P ==> Q x  |] ==> Q x"
by simp

lemma metaMP: "[| A ==> B; A |] ==> B"
by blast

lemma True
proof- 
  presume t: "C  ==> E"
  thm metaMP [OF t]

  presume r1: "\<And> B. P \<Longrightarrow> B"
  presume r2: "\<And> C. C \<Longrightarrow> P"
  thm r1 [OF r2]

  thm metaMP [OF t]

lemma ws_subcls1_induct4: "\<lbrakk>is_class G C; ws_prog G;  
  \<And>C c. \<lbrakk>C \<noteq> Object\<longrightarrow> P (super c)\<rbrakk> \<Longrightarrow> P C
 \<rbrakk> \<Longrightarrow> P C"
proof -
  assume cls_C: "is_class G C"
  and       ws: "ws_prog G"
  and      hyp: "\<And>C c. \<lbrakk>C \<noteq> Object\<longrightarrow> P (super c)\<rbrakk> \<Longrightarrow> P C"
  thm ws_subcls1_induct [OF cls_C ws hyp]

show
(\<And>C c. class G C = Some c \<and>
       (C \<noteq> Object \<longrightarrow> G\<turnstile>C\<prec>\<^sub>C\<^sub>1super c \<and> ?P (super c) \<and> is_class G (super c)) \<Longrightarrow>
       ?P C) \<Longrightarrow>
?P C
  show ?thesis
    thm "thm ws_subcls1_induct [OF cls_C ws hyp]"
    apply (rule ws_subcls1_induct)
  proof (rule ws_subcls1_induct)
    fix C c
    assume "class G C = Some c \<and>
            (C \<noteq> Object \<longrightarrow>
              G\<turnstile>C\<prec>\<^sub>C\<^sub>1super c \<and> P (super c) \<and> is_class G (super c))"
    show "C \<noteq> Object \<longrightarrow> P (super  (?c C c))" 
apply (erule ws_subcls1_induct)
apply assumption
apply (erule conjE)
apply (case_tac "C=Object")
apply blast
apply (erule impE)
apply assumption
apply (erule conjE)+
apply (rotate_tac 2)
sorry

*)


constdefs
imethds:: "prog \<Rightarrow> qtname \<Rightarrow> (sig,qtname \<times> mhead) tables"
  (* methods of an interface, with overriding and inheritance, cf. 9.2 *)
"imethds G I 
  \<equiv> iface_rec (G,I)  
              (\<lambda>I i ts. (Un_tables ts) \<oplus>\<oplus> 
                        (o2s \<circ> table_of (map (\<lambda>(s,m). (s,I,m)) (imethods i))))"
	


end

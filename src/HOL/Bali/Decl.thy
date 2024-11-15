(*  Title:      HOL/Bali/Decl.thy
    Author:     David von Oheimb and Norbert Schirmer
*)
subsection \<open>Field, method, interface, and class declarations, whole Java programs
\<close>

theory Decl
imports Term Table
  (** order is significant, because of clash for "var" **)
begin

text \<open>
improvements:
\begin{itemize}
\item clarification and correction of some aspects of the package/access concept
  (Also submitted as bug report to the Java Bug Database:
   Bug Id: 4485402 and Bug Id: 4493343 
   \<^url>\<open>http://developer.java.sun.com/developer/bugParade/index.jshtml\<close>
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
\<close>

subsection \<open>Modifier\<close>

subsubsection \<open>Access modifier\<close>

datatype acc_modi (* access modifier *)
         = Private | Package | Protected | Public 

text \<open>
We can define a linear order for the access modifiers. With Private yielding the
most restrictive access and public the most liberal access policy:
  Private < Package < Protected < Public
\<close>
 
instantiation acc_modi :: linorder
begin

definition
  less_acc_def: "a < b
      \<longleftrightarrow> (case a of
             Private    \<Rightarrow> (b=Package \<or> b=Protected \<or> b=Public)
           | Package    \<Rightarrow> (b=Protected \<or> b=Public)
           | Protected  \<Rightarrow> (b=Public)
           | Public     \<Rightarrow> False)"

definition
  le_acc_def: "(a :: acc_modi) \<le> b \<longleftrightarrow> a < b \<or> a = b"

instance
proof
  fix x y z::acc_modi
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (auto simp add: le_acc_def less_acc_def split: acc_modi.split) 
  show "x \<le> x"                       \<comment> \<open>reflexivity\<close>
    by (auto simp add: le_acc_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"  \<comment> \<open>transitivity\<close>
    by (auto simp add: le_acc_def less_acc_def split: acc_modi.split)
  show "x = y" if "x \<le> y" "y \<le> x"   \<comment> \<open>antisymmetry\<close>
  proof -
    have "\<forall>x y. x < (y::acc_modi) \<and> y < x \<longrightarrow> False"
      by (auto simp add: less_acc_def split: acc_modi.split)
    with that show ?thesis by (unfold le_acc_def) iprover
  qed
  show "x \<le> y \<or> y \<le> x"
    by (auto simp add: less_acc_def le_acc_def split: acc_modi.split)
qed
  
end

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

lemma acc_modi_Package_le_cases:
  assumes "Package \<le> m"
  obtains (Package) "m = Package"
    | (Protected) "m = Protected"
    | (Public) "m = Public"
using assms by (auto dest: acc_modi_Package_le)


subsubsection \<open>Static Modifier\<close>
type_synonym stat_modi = bool (* modifier: static *)

subsection \<open>Declaration (base "class" for member,interface and class
 declarations\<close>

record decl =
        access :: acc_modi

translations
  (type) "decl" <= (type) "\<lparr>access::acc_modi\<rparr>"
  (type) "decl" <= (type) "\<lparr>access::acc_modi,\<dots>::'a\<rparr>"

subsection \<open>Member (field or method)\<close>
record  member = decl +
         static :: stat_modi

translations
  (type) "member" <= (type) "\<lparr>access::acc_modi,static::bool\<rparr>"
  (type) "member" <= (type) "\<lparr>access::acc_modi,static::bool,\<dots>::'a\<rparr>"

subsection \<open>Field\<close>

record field = member +
        type :: ty
translations
  (type) "field" <= (type) "\<lparr>access::acc_modi, static::bool, type::ty\<rparr>"
  (type) "field" <= (type) "\<lparr>access::acc_modi, static::bool, type::ty,\<dots>::'a\<rparr>"

type_synonym fdecl          (* field declaration, cf. 8.3 *)
        = "vname \<times> field"


translations
  (type) "fdecl" <= (type) "vname \<times> field"

subsection  \<open>Method\<close>

record mhead = member +     (* method head (excluding signature) *)
        pars ::"vname list" (* parameter names *)
        resT ::ty           (* result type *)

record mbody =                      (* method body *)
        lcls::  "(vname \<times> ty) list" (* local variables *)
        stmt:: stmt                 (* the body statement *)

record methd = mhead + (* method in a class *)
        mbody::mbody

type_synonym mdecl = "sig \<times> methd"  (* method declaration in a class *)


translations
  (type) "mhead" <= (type) "\<lparr>access::acc_modi, static::bool, 
                      pars::vname list, resT::ty\<rparr>"
  (type) "mhead" <= (type) "\<lparr>access::acc_modi, static::bool, 
                      pars::vname list, resT::ty,\<dots>::'a\<rparr>"
  (type) "mbody" <= (type) "\<lparr>lcls::(vname \<times> ty) list,stmt::stmt\<rparr>"
  (type) "mbody" <= (type) "\<lparr>lcls::(vname \<times> ty) list,stmt::stmt,\<dots>::'a\<rparr>"      
  (type) "methd" <= (type) "\<lparr>access::acc_modi, static::bool, 
                      pars::vname list, resT::ty,mbody::mbody\<rparr>"
  (type) "methd" <= (type) "\<lparr>access::acc_modi, static::bool, 
                      pars::vname list, resT::ty,mbody::mbody,\<dots>::'a\<rparr>"
  (type) "mdecl" <= (type) "sig \<times> methd"


definition
  mhead :: "methd \<Rightarrow> mhead"
  where "mhead m = \<lparr>access=access m, static=static m, pars=pars m, resT=resT m\<rparr>"

lemma access_mhead [simp]:"access (mhead m) = access m"
by (simp add: mhead_def)

lemma static_mhead [simp]:"static (mhead m) = static m"
by (simp add: mhead_def)

lemma pars_mhead [simp]:"pars (mhead m) = pars m"
by (simp add: mhead_def)

lemma resT_mhead [simp]:"resT (mhead m) = resT m"
by (simp add: mhead_def)

text \<open>To be able to talk uniformaly about field and method declarations we
introduce the notion of a member declaration (e.g. useful to define 
accessiblity )\<close>

datatype memberdecl = fdecl fdecl | mdecl mdecl

datatype memberid = fid vname | mid sig

class has_memberid =
  fixes memberid :: "'a \<Rightarrow> memberid"

instantiation memberdecl :: has_memberid
begin

definition
memberdecl_memberid_def:
  "memberid m = (case m of
                    fdecl (vn,f)  \<Rightarrow> fid vn
                  | mdecl (sig,m) \<Rightarrow> mid sig)"

instance ..

end

lemma memberid_fdecl_simp[simp]: "memberid (fdecl (vn,f)) = fid vn"
by (simp add: memberdecl_memberid_def)

lemma memberid_fdecl_simp1: "memberid (fdecl f) = fid (fst f)"
by (cases f) (simp add: memberdecl_memberid_def)

lemma memberid_mdecl_simp[simp]: "memberid (mdecl (sig,m)) = mid sig"
by (simp add: memberdecl_memberid_def)

lemma memberid_mdecl_simp1: "memberid (mdecl m) = mid (fst m)"
by (cases m) (simp add: memberdecl_memberid_def)

instantiation prod :: (type, has_memberid) has_memberid
begin

definition
pair_memberid_def:
  "memberid p = memberid (snd p)"

instance ..

end

lemma memberid_pair_simp[simp]: "memberid (c,m) = memberid m"
by (simp add: pair_memberid_def)

lemma memberid_pair_simp1: "memberid p  = memberid (snd p)"
by (simp add: pair_memberid_def)

definition
  is_field :: "qtname \<times> memberdecl \<Rightarrow> bool"
  where "is_field m = (\<exists> declC f. m=(declC,fdecl f))"
  
lemma is_fieldD: "is_field m \<Longrightarrow> \<exists> declC f. m=(declC,fdecl f)"
by (simp add: is_field_def)

lemma is_fieldI: "is_field (C,fdecl f)"
by (simp add: is_field_def)

definition
  is_method :: "qtname \<times> memberdecl \<Rightarrow> bool"
  where "is_method membr = (\<exists>declC m. membr=(declC,mdecl m))"
  
lemma is_methodD: "is_method membr \<Longrightarrow> \<exists> declC m. membr=(declC,mdecl m)"
by (simp add: is_method_def)

lemma is_methodI: "is_method (C,mdecl m)"
by (simp add: is_method_def)


subsection \<open>Interface\<close>


record  ibody = decl +  \<comment> \<open>interface body\<close>
          imethods :: "(sig \<times> mhead) list" \<comment> \<open>method heads\<close>

record  iface = ibody + \<comment> \<open>interface\<close>
         isuperIfs:: "qtname list" \<comment> \<open>superinterface list\<close>
type_synonym
        idecl           \<comment> \<open>interface declaration, cf. 9.1\<close>
        = "qtname \<times> iface"

translations
  (type) "ibody" <= (type) "\<lparr>access::acc_modi,imethods::(sig \<times> mhead) list\<rparr>"
  (type) "ibody" <= (type) "\<lparr>access::acc_modi,imethods::(sig \<times> mhead) list,\<dots>::'a\<rparr>"
  (type) "iface" <= (type) "\<lparr>access::acc_modi,imethods::(sig \<times> mhead) list,
                      isuperIfs::qtname list\<rparr>"
  (type) "iface" <= (type) "\<lparr>access::acc_modi,imethods::(sig \<times> mhead) list,
                      isuperIfs::qtname list,\<dots>::'a\<rparr>"
  (type) "idecl" <= (type) "qtname \<times> iface"

definition
  ibody :: "iface \<Rightarrow> ibody"
  where "ibody i = \<lparr>access=access i,imethods=imethods i\<rparr>"

lemma access_ibody [simp]: "(access (ibody i)) = access i"
by (simp add: ibody_def)

lemma imethods_ibody [simp]: "(imethods (ibody i)) = imethods i"
by (simp add: ibody_def)

subsection  \<open>Class\<close>
record cbody = decl +          \<comment> \<open>class body\<close>
         cfields:: "fdecl list" 
         methods:: "mdecl list"
         init   :: "stmt"       \<comment> \<open>initializer\<close>

record "class" = cbody +           \<comment> \<open>class\<close>
        super   :: "qtname"      \<comment> \<open>superclass\<close>
        superIfs:: "qtname list" \<comment> \<open>implemented interfaces\<close>
type_synonym
        cdecl           \<comment> \<open>class declaration, cf. 8.1\<close>
        = "qtname \<times> class"

translations
  (type) "cbody" <= (type) "\<lparr>access::acc_modi,cfields::fdecl list,
                      methods::mdecl list,init::stmt\<rparr>"
  (type) "cbody" <= (type) "\<lparr>access::acc_modi,cfields::fdecl list,
                      methods::mdecl list,init::stmt,\<dots>::'a\<rparr>"
  (type) "class" <= (type) "\<lparr>access::acc_modi,cfields::fdecl list,
                      methods::mdecl list,init::stmt,
                      super::qtname,superIfs::qtname list\<rparr>"
  (type) "class" <= (type) "\<lparr>access::acc_modi,cfields::fdecl list,
                      methods::mdecl list,init::stmt,
                      super::qtname,superIfs::qtname list,\<dots>::'a\<rparr>"
  (type) "cdecl" <= (type) "qtname \<times> class"

definition
  cbody :: "class \<Rightarrow> cbody"
  where "cbody c = \<lparr>access=access c, cfields=cfields c,methods=methods c,init=init c\<rparr>"

lemma access_cbody [simp]:"access (cbody c) = access c"
by (simp add: cbody_def)

lemma cfields_cbody [simp]:"cfields (cbody c) = cfields c"
by (simp add: cbody_def)

lemma methods_cbody [simp]:"methods (cbody c) = methods c"
by (simp add: cbody_def)

lemma init_cbody [simp]:"init (cbody c) = init c"
by (simp add: cbody_def)


subsubsection "standard classes"

consts
  Object_mdecls  ::  "mdecl list" \<comment> \<open>methods of Object\<close>
  SXcpt_mdecls   ::  "mdecl list" \<comment> \<open>methods of SXcpts\<close>

definition
  ObjectC ::         "cdecl"      \<comment> \<open>declaration  of root      class\<close> where
  "ObjectC = (Object,\<lparr>access=Public,cfields=[],methods=Object_mdecls,
                                  init=Skip,super=undefined,superIfs=[]\<rparr>)"

definition
  SXcptC  ::"xname \<Rightarrow> cdecl"      \<comment> \<open>declarations of throwable classes\<close> where
  "SXcptC xn = (SXcpt xn,\<lparr>access=Public,cfields=[],methods=SXcpt_mdecls,
                                   init=Skip,
                                   super=if xn = Throwable then Object 
                                                           else SXcpt Throwable,
                                   superIfs=[]\<rparr>)"

lemma ObjectC_neq_SXcptC [simp]: "ObjectC \<noteq> SXcptC xn"
by (simp add: ObjectC_def SXcptC_def Object_def SXcpt_def)

lemma SXcptC_inject [simp]: "(SXcptC xn = SXcptC xm) = (xn = xm)"
by (simp add: SXcptC_def)

definition
  standard_classes :: "cdecl list" where
  "standard_classes = [ObjectC, SXcptC Throwable,
                SXcptC NullPointer, SXcptC OutOfMemory, SXcptC ClassCast,
                SXcptC NegArrSize , SXcptC IndOutBound, SXcptC ArrStore]"


subsubsection "programs"

record prog =
        ifaces ::"idecl list"
        "classes"::"cdecl list"

translations
     (type) "prog" <= (type) "\<lparr>ifaces::idecl list,classes::cdecl list\<rparr>"
     (type) "prog" <= (type) "\<lparr>ifaces::idecl list,classes::cdecl list,\<dots>::'a\<rparr>"

abbreviation
  iface :: "prog  \<Rightarrow> (qtname, iface) table"
  where "iface G I == table_of (ifaces G) I"

abbreviation
  "class" :: "prog  \<Rightarrow> (qtname, class) table"
  where "class G C == table_of (classes G) C"

abbreviation
  is_iface :: "prog  \<Rightarrow> qtname  \<Rightarrow> bool"
  where "is_iface G I == iface G I \<noteq> None"

abbreviation
  is_class :: "prog  \<Rightarrow> qtname  \<Rightarrow> bool"
  where "is_class G C == class G C \<noteq> None"


subsubsection "is type"

primrec is_type :: "prog \<Rightarrow> ty \<Rightarrow> bool"
  and isrtype :: "prog \<Rightarrow> ref_ty \<Rightarrow> bool"
where
  "is_type G (PrimT pt)  = True"
| "is_type G (RefT  rt)  = isrtype G rt"
| "isrtype G (NullT) = True"
| "isrtype G (IfaceT tn) = is_iface G tn"
| "isrtype G (ClassT tn) = is_class G tn"
| "isrtype G (ArrayT T ) = is_type  G T"

lemma type_is_iface: "is_type G (Iface I) \<Longrightarrow> is_iface G I"
by auto

lemma type_is_class: "is_type G (Class C) \<Longrightarrow>  is_class G C"
by auto


subsubsection "subinterface and subclass relation, in anticipation of TypeRel.thy"

definition
  subint1  :: "prog \<Rightarrow> (qtname \<times> qtname) set" \<comment> \<open>direct subinterface\<close>
  where "subint1 G = {(I,J). \<exists>i\<in>iface G I: J\<in>set (isuperIfs i)}"

definition
  subcls1  :: "prog \<Rightarrow> (qtname \<times> qtname) set" \<comment> \<open>direct subclass\<close>
  where "subcls1 G = {(C,D). C\<noteq>Object \<and> (\<exists>c\<in>class G C: super c = D)}"

abbreviation
  subcls1_syntax :: "prog => [qtname, qtname] => bool" (\<open>_\<turnstile>_\<prec>\<^sub>C1_\<close>  [71,71,71] 70)
  where "G\<turnstile>C \<prec>\<^sub>C1 D == (C,D) \<in> subcls1 G"

abbreviation
  subclseq_syntax :: "prog => [qtname, qtname] => bool" (\<open>_\<turnstile>_\<preceq>\<^sub>C _\<close>  [71,71,71] 70) 
  where "G\<turnstile>C \<preceq>\<^sub>C D == (C,D) \<in>(subcls1 G)\<^sup>*" (* cf. 8.1.3 *)

abbreviation
  subcls_syntax :: "prog => [qtname, qtname] => bool" (\<open>_\<turnstile>_\<prec>\<^sub>C _\<close>  [71,71,71] 70)
  where "G\<turnstile>C \<prec>\<^sub>C D == (C,D) \<in>(subcls1 G)\<^sup>+"

notation (ASCII)
  subcls1_syntax  (\<open>_|-_<:C1_\<close> [71,71,71] 70) and
  subclseq_syntax  (\<open>_|-_<=:C _\<close>[71,71,71] 70) and
  subcls_syntax  (\<open>_|-_<:C _\<close>[71,71,71] 70)

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
  "subint1 G = (SIGMA I: {I. is_iface G I}. set (isuperIfs (the (iface G I))))"
apply (unfold subint1_def)
apply auto
done

lemma subcls1_def2: 
  "subcls1 G = 
     (SIGMA C: {C. is_class G C}. {D. C\<noteq>Object \<and> super (the(class G C))=D})"
apply (unfold subcls1_def)
apply auto
done

lemma subcls_is_class:
"\<lbrakk>G\<turnstile>C \<prec>\<^sub>C D\<rbrakk> \<Longrightarrow> \<exists> c. class G C = Some c"
by (auto simp add: subcls1_def dest: tranclD)

lemma no_subcls1_Object:"G\<turnstile>Object\<prec>\<^sub>C1 D \<Longrightarrow> P"
by (auto simp add: subcls1_def)

lemma no_subcls_Object: "G\<turnstile>Object\<prec>\<^sub>C D \<Longrightarrow> P"
apply (erule trancl_induct)
apply (auto intro: no_subcls1_Object)
done

subsubsection "well-structured programs"

definition
  ws_idecl :: "prog \<Rightarrow> qtname \<Rightarrow> qtname list \<Rightarrow> bool"
  where "ws_idecl G I si = (\<forall>J\<in>set si.  is_iface G J   \<and> (J,I)\<notin>(subint1 G)\<^sup>+)"
  
definition
  ws_cdecl :: "prog \<Rightarrow> qtname \<Rightarrow> qtname \<Rightarrow> bool"
  where "ws_cdecl G C sc = (C\<noteq>Object \<longrightarrow> is_class G sc \<and> (sc,C)\<notin>(subcls1 G)\<^sup>+)"
  
definition
  ws_prog  :: "prog \<Rightarrow> bool" where
  "ws_prog G = ((\<forall>(I,i)\<in>set (ifaces  G). ws_idecl G I (isuperIfs i)) \<and> 
                 (\<forall>(C,c)\<in>set (classes G). ws_cdecl G C (super c)))"


lemma ws_progI: 
"\<lbrakk>\<forall>(I,i)\<in>set (ifaces G). \<forall>J\<in>set (isuperIfs i). is_iface G J \<and> 
                                                (J,I) \<notin> (subint1 G)\<^sup>+; 
  \<forall>(C,c)\<in>set (classes G). C\<noteq>Object \<longrightarrow> is_class G (super c) \<and> 
                                        ((super c),C) \<notin> (subcls1 G)\<^sup>+  
 \<rbrakk> \<Longrightarrow> ws_prog G"
apply (unfold ws_prog_def ws_idecl_def ws_cdecl_def)
apply (erule_tac conjI)
apply blast
done

lemma ws_prog_ideclD: 
"\<lbrakk>iface G I = Some i; J\<in>set (isuperIfs i); ws_prog G\<rbrakk> \<Longrightarrow>  
  is_iface G J \<and> (J,I)\<notin>(subint1 G)\<^sup>+"
apply (unfold ws_prog_def ws_idecl_def)
apply clarify
apply (drule_tac map_of_SomeD)
apply auto
done

lemma ws_prog_cdeclD: 
"\<lbrakk>class G C = Some c; C\<noteq>Object; ws_prog G\<rbrakk> \<Longrightarrow>  
  is_class G (super c) \<and> (super c,C)\<notin>(subcls1 G)\<^sup>+"
apply (unfold ws_prog_def ws_cdecl_def)
apply clarify
apply (drule_tac map_of_SomeD)
apply auto
done


subsubsection "well-foundedness"

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
  "ws_prog G \<Longrightarrow> (subint1 G)\<inverse> \<inter> (subint1 G)\<^sup>+ = {}"
apply (force dest: subint1D ws_prog_ideclD conjunct2)
done

lemma subcls1_irrefl_lemma1: 
  "ws_prog G \<Longrightarrow> (subcls1 G)\<inverse> \<inter> (subcls1 G)\<^sup>+ = {}"
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

lemmas subint1_acyclic = subint1_irrefl_lemma2 [THEN acyclicI]
lemmas subcls1_acyclic = subcls1_irrefl_lemma2 [THEN acyclicI]


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
apply (erule rev_mp)
apply (rule subint1_induct)
apply  assumption
apply (simp (no_asm)) 
apply safe
apply (blast dest: subint1I ws_prog_ideclD)
done


lemma ws_subcls1_induct: "\<lbrakk>is_class G C; ws_prog G;  
  \<And>C c. \<lbrakk>class G C = Some c;  
 (C \<noteq> Object \<longrightarrow> (C,(super c))\<in>subcls1 G \<and> 
                  P (super c) \<and> is_class G (super c))\<rbrakk> \<Longrightarrow> P C
 \<rbrakk> \<Longrightarrow> P C"
apply (erule rev_mp)
apply (rule subcls1_induct)
apply  assumption
apply (simp (no_asm)) 
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
    assume   hyp:"\<forall> S. G\<turnstile>C \<prec>\<^sub>C1 S \<longrightarrow> is_class G S \<longrightarrow> P S"
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
by (auto intro: ws_class_induct)

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
    assume   hyp:"\<forall> S. G\<turnstile>C \<prec>\<^sub>C1 S \<longrightarrow> (\<forall> s. class G S = Some s \<longrightarrow> P S s)"
       and iscls:"class G C = Some c"
    show "P C c"
    proof (cases "C=Object")
      case True with iscls init show "P C c" by auto
    next
      case False
      with ws iscls obtain sc where
        sc: "class G (super c) = Some sc"
        by (auto dest: ws_prog_cdeclD)
      from iscls False have "G\<turnstile>C \<prec>\<^sub>C1 (super c)" by (rule subcls1I)
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

subsubsection "general recursion operators for the interface and class hiearchies"

function iface_rec  :: "prog \<Rightarrow> qtname \<Rightarrow> (qtname \<Rightarrow> iface \<Rightarrow> 'a set \<Rightarrow> 'a) \<Rightarrow> 'a"
where
[simp del]: "iface_rec G I f = 
  (case iface G I of 
         None \<Rightarrow> undefined 
       | Some i \<Rightarrow> if ws_prog G 
                      then f I i 
                               ((\<lambda>J. iface_rec G J f)`set (isuperIfs i))
                      else undefined)"
by auto
termination
by (relation "inv_image (same_fst ws_prog (\<lambda>G. (subint1 G)\<inverse>)) (%(x,y,z). (x,y))")
 (auto simp: wf_subint1 subint1I wf_same_fst)

lemma iface_rec: 
"\<lbrakk>iface G I = Some i; ws_prog G\<rbrakk> \<Longrightarrow> 
 iface_rec G I f = f I i ((\<lambda>J. iface_rec G J f)`set (isuperIfs i))"
apply (subst iface_rec.simps)
apply simp
done


function
  class_rec  :: "prog \<Rightarrow> qtname \<Rightarrow> 'a \<Rightarrow> (qtname \<Rightarrow> class \<Rightarrow> 'a     \<Rightarrow> 'a) \<Rightarrow> 'a"
where
[simp del]: "class_rec G C t f = 
  (case class G C of 
           None \<Rightarrow> undefined 
         | Some c \<Rightarrow> if ws_prog G 
                        then f C c 
                                 (if C = Object then t 
                                                else class_rec G (super c) t f)
                        else undefined)"

by auto
termination
by (relation "inv_image (same_fst ws_prog (\<lambda>G. (subcls1 G)\<inverse>)) (%(x,y,z,w). (x,y))")
 (auto simp: wf_subcls1 subcls1I wf_same_fst)

lemma class_rec: "\<lbrakk>class G C = Some c; ws_prog G\<rbrakk> \<Longrightarrow>  
 class_rec G C t f = 
   f C c (if C = Object then t else class_rec G (super c) t f)"
apply (subst class_rec.simps)
apply simp
done

definition
  imethds :: "prog \<Rightarrow> qtname \<Rightarrow> (sig,qtname \<times> mhead) tables" where
  \<comment> \<open>methods of an interface, with overriding and inheritance, cf. 9.2\<close>
  "imethds G I = iface_rec G I
              (\<lambda>I i ts. (Un_tables ts) \<oplus>\<oplus> 
                        (set_option \<circ> table_of (map (\<lambda>(s,m). (s,I,m)) (imethods i))))"
        


end

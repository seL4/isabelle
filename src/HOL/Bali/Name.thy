(*  Title:      HOL/Bali/Name.thy
    Author:     David von Oheimb
*)
subsection \<open>Java names\<close>

theory Name imports Basis begin

(* cf. 6.5 *) 
typedecl tnam   \<comment> \<open>ordinary type name, i.e. class or interface name\<close>
typedecl pname  \<comment> \<open>package name\<close>
typedecl mname  \<comment> \<open>method name\<close>
typedecl vname  \<comment> \<open>variable or field name\<close>
typedecl label  \<comment> \<open>label as destination of break or continue\<close>

datatype ename        \<comment> \<open>expression name\<close> 
        = VNam vname 
        | Res         \<comment> \<open>special name to model the return value of methods\<close>

datatype lname        \<comment> \<open>names for local variables and the This pointer\<close>
        = EName ename 
        | This
abbreviation VName   :: "vname \<Rightarrow> lname"
      where "VName n == EName (VNam n)"

abbreviation Result :: lname
      where "Result == EName Res"

datatype xname          \<comment> \<open>names of standard exceptions\<close>
        = Throwable
        | NullPointer | OutOfMemory | ClassCast   
        | NegArrSize  | IndOutBound | ArrStore

lemma xn_cases: 
  "xn = Throwable   \<or> xn = NullPointer \<or>  
         xn = OutOfMemory \<or> xn = ClassCast \<or> 
         xn = NegArrSize  \<or> xn = IndOutBound \<or> xn = ArrStore"
apply (induct xn)
apply auto
done


datatype tname  \<comment> \<open>type names for standard classes and other type names\<close>
        = Object'
        | SXcpt'   xname
        | TName   tnam

record   qtname = \<comment> \<open>qualified tname cf. 6.5.3, 6.5.4\<close>
          pid :: pname  
          tid :: tname

class has_pname =
  fixes pname :: "'a \<Rightarrow> pname"

instantiation pname :: has_pname
begin

definition
  pname_pname_def: "pname (p::pname) \<equiv> p"

instance ..

end

class has_tname =
  fixes tname :: "'a \<Rightarrow> tname"

instantiation tname :: has_tname
begin

definition
  tname_tname_def: "tname (t::tname) = t"

instance ..

end

definition
  qtname_qtname_def: "qtname (q::'a qtname_scheme) = q"

translations
  (type) "qtname" <= (type) "\<lparr>pid::pname,tid::tname\<rparr>"
  (type) "'a qtname_scheme" <= (type) "\<lparr>pid::pname,tid::tname,\<dots>::'a\<rparr>"


axiomatization java_lang::pname \<comment> \<open>package java.lang\<close>

definition
  Object :: qtname
  where "Object = \<lparr>pid = java_lang, tid = Object'\<rparr>"

definition SXcpt :: "xname \<Rightarrow> qtname"
  where "SXcpt = (\<lambda>x.  \<lparr>pid = java_lang, tid = SXcpt' x\<rparr>)"

lemma Object_neq_SXcpt [simp]: "Object \<noteq> SXcpt xn"
by (simp add: Object_def SXcpt_def)

lemma SXcpt_inject [simp]: "(SXcpt xn = SXcpt xm) = (xn = xm)"
by (simp add: SXcpt_def)

end

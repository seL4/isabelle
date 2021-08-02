theory OO imports Main begin

subsection "Towards an OO Language: A Language of Records"

(* FIXME: move to HOL/Fun *)
abbreviation fun_upd2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c"
  ("_/'((2_,_ :=/ _)')" [1000,0,0,0] 900)
where "f(x,y := z) == f(x := (f x)(y := z))"

type_synonym addr = nat
datatype ref = null | Ref addr

type_synonym obj = "string \<Rightarrow> ref"
type_synonym venv = "string \<Rightarrow> ref"
type_synonym store = "addr \<Rightarrow> obj"

datatype exp =
  Null |
  New |
  V string |
  Faccess exp string       ("_\<bullet>/_" [63,1000] 63) |
  Vassign string exp       ("(_ ::=/ _)" [1000,61] 62) |
  Fassign exp string exp   ("(_\<bullet>_ ::=/ _)" [63,0,62] 62) |
  Mcall exp string exp     ("(_\<bullet>/_<_>)" [63,0,0] 63) |
  Seq exp exp              ("_;/ _" [61,60] 60) |
  If bexp exp exp          ("IF _/ THEN (2_)/ ELSE (2_)" [0,0,61] 61)
and bexp = B bool | Not bexp | And bexp bexp | Eq exp exp

type_synonym menv = "string \<Rightarrow> exp"
type_synonym config = "venv \<times> store \<times> addr"

inductive
  big_step :: "menv \<Rightarrow> exp \<times> config \<Rightarrow> ref \<times> config \<Rightarrow> bool"
    ("(_ \<turnstile>/ (_/ \<Rightarrow> _))" [60,0,60] 55) and
  bval ::  "menv \<Rightarrow> bexp \<times> config \<Rightarrow> bool \<times> config \<Rightarrow> bool"
    ("_ \<turnstile> _ \<rightarrow> _" [60,0,60] 55)
where
Null:
"me \<turnstile> (Null,c) \<Rightarrow> (null,c)" |
New:
"me \<turnstile> (New,ve,s,n) \<Rightarrow> (Ref n,ve,s(n := (\<lambda>f. null)),n+1)" |
Vaccess:
"me \<turnstile> (V x,ve,sn) \<Rightarrow> (ve x,ve,sn)" |
Faccess:
"me \<turnstile> (e,c) \<Rightarrow> (Ref a,ve',s',n') \<Longrightarrow>
 me \<turnstile> (e\<bullet>f,c) \<Rightarrow> (s' a f,ve',s',n')" |
Vassign:
"me \<turnstile> (e,c) \<Rightarrow> (r,ve',sn') \<Longrightarrow>
 me \<turnstile> (x ::= e,c) \<Rightarrow> (r,ve'(x:=r),sn')" |
Fassign:
"\<lbrakk> me \<turnstile> (oe,c\<^sub>1) \<Rightarrow> (Ref a,c\<^sub>2);  me \<turnstile> (e,c\<^sub>2) \<Rightarrow> (r,ve\<^sub>3,s\<^sub>3,n\<^sub>3) \<rbrakk> \<Longrightarrow>
 me \<turnstile> (oe\<bullet>f ::= e,c\<^sub>1) \<Rightarrow> (r,ve\<^sub>3,s\<^sub>3(a,f := r),n\<^sub>3)" |
Mcall:
"\<lbrakk> me \<turnstile> (oe,c\<^sub>1) \<Rightarrow> (or,c\<^sub>2);  me \<turnstile> (pe,c\<^sub>2) \<Rightarrow> (pr,ve\<^sub>3,sn\<^sub>3);
   ve = (\<lambda>x. null)(''this'' := or, ''param'' := pr);
   me \<turnstile> (me m,ve,sn\<^sub>3) \<Rightarrow> (r,ve',sn\<^sub>4) \<rbrakk>
  \<Longrightarrow>
 me \<turnstile> (oe\<bullet>m<pe>,c\<^sub>1) \<Rightarrow> (r,ve\<^sub>3,sn\<^sub>4)" for or |
Seq:
"\<lbrakk> me \<turnstile> (e\<^sub>1,c\<^sub>1) \<Rightarrow> (r,c\<^sub>2);  me \<turnstile> (e\<^sub>2,c\<^sub>2) \<Rightarrow> c\<^sub>3 \<rbrakk> \<Longrightarrow>
 me \<turnstile> (e\<^sub>1; e\<^sub>2,c\<^sub>1) \<Rightarrow> c\<^sub>3" |
IfTrue:
"\<lbrakk> me \<turnstile> (b,c\<^sub>1) \<rightarrow> (True,c\<^sub>2);  me \<turnstile> (e\<^sub>1,c\<^sub>2) \<Rightarrow> c\<^sub>3 \<rbrakk> \<Longrightarrow>
 me \<turnstile> (IF b THEN e\<^sub>1 ELSE e\<^sub>2,c\<^sub>1) \<Rightarrow> c\<^sub>3" |
IfFalse:
"\<lbrakk> me \<turnstile> (b,c\<^sub>1) \<rightarrow> (False,c\<^sub>2);  me \<turnstile> (e\<^sub>2,c\<^sub>2) \<Rightarrow> c\<^sub>3 \<rbrakk> \<Longrightarrow>
 me \<turnstile> (IF b THEN e\<^sub>1 ELSE e\<^sub>2,c\<^sub>1) \<Rightarrow> c\<^sub>3" |

"me \<turnstile> (B bv,c) \<rightarrow> (bv,c)" |

"me \<turnstile> (b,c\<^sub>1) \<rightarrow> (bv,c\<^sub>2) \<Longrightarrow> me \<turnstile> (Not b,c\<^sub>1) \<rightarrow> (\<not>bv,c\<^sub>2)" |

"\<lbrakk> me \<turnstile> (b\<^sub>1,c\<^sub>1) \<rightarrow> (bv\<^sub>1,c\<^sub>2);  me \<turnstile> (b\<^sub>2,c\<^sub>2) \<rightarrow> (bv\<^sub>2,c\<^sub>3) \<rbrakk> \<Longrightarrow>
 me \<turnstile> (And b\<^sub>1 b\<^sub>2,c\<^sub>1) \<rightarrow> (bv\<^sub>1\<and>bv\<^sub>2,c\<^sub>3)" |

"\<lbrakk> me \<turnstile> (e\<^sub>1,c\<^sub>1) \<Rightarrow> (r\<^sub>1,c\<^sub>2);  me \<turnstile> (e\<^sub>2,c\<^sub>2) \<Rightarrow> (r\<^sub>2,c\<^sub>3) \<rbrakk> \<Longrightarrow>
 me \<turnstile> (Eq e\<^sub>1 e\<^sub>2,c\<^sub>1) \<rightarrow> (r\<^sub>1=r\<^sub>2,c\<^sub>3)"


code_pred (modes: i => i => o => bool) big_step .

text\<open>Example: natural numbers encoded as objects with a predecessor
field. Null is zero. Method succ adds an object in front, method add
adds as many objects in front as the parameter specifies.

First, the method bodies:\<close>

definition
"m_succ  =  (''s'' ::= New)\<bullet>''pred'' ::= V ''this''; V ''s''"

definition "m_add =
  IF Eq (V ''param'') Null
  THEN V ''this''
  ELSE V ''this''\<bullet>''succ''<Null>\<bullet>''add''<V ''param''\<bullet>''pred''>"

text\<open>The method environment:\<close>
definition
"menv = (\<lambda>m. Null)(''succ'' := m_succ, ''add'' := m_add)"

text\<open>The main code, adding 1 and 2:\<close>
definition "main =
  ''1'' ::= Null\<bullet>''succ''<Null>;
  ''2'' ::= V ''1''\<bullet>''succ''<Null>;
  V ''2'' \<bullet> ''add'' <V ''1''>"

text\<open>Execution of semantics. The final variable environment and store are
converted into lists of references based on given lists of variable and field
names to extract.\<close>

values
 "{(r, map ve' [''1'',''2''], map (\<lambda>n. map (s' n)[''pred'']) [0..<n])|
    r ve' s' n. menv \<turnstile> (main, \<lambda>x. null, nth[], 0) \<Rightarrow> (r,ve',s',n)}"

end

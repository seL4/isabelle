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
"\<lbrakk> me \<turnstile> (oe,c\<^isub>1) \<Rightarrow> (Ref a,c\<^isub>2);  me \<turnstile> (e,c\<^isub>2) \<Rightarrow> (r,ve\<^isub>3,s\<^isub>3,n\<^isub>3) \<rbrakk> \<Longrightarrow>
 me \<turnstile> (oe\<bullet>f ::= e,c\<^isub>1) \<Rightarrow> (r,ve\<^isub>3,s\<^isub>3(a,f := r),n\<^isub>3)" |
Mcall:
"\<lbrakk> me \<turnstile> (oe,c\<^isub>1) \<Rightarrow> (or,c\<^isub>2);  me \<turnstile> (pe,c\<^isub>2) \<Rightarrow> (pr,ve\<^isub>3,sn\<^isub>3);
   ve = (\<lambda>x. null)(''this'' := or, ''param'' := pr);
   me \<turnstile> (me m,ve,sn\<^isub>3) \<Rightarrow> (r,ve',sn\<^isub>4) \<rbrakk>
  \<Longrightarrow>
 me \<turnstile> (oe\<bullet>m<pe>,c\<^isub>1) \<Rightarrow> (r,ve\<^isub>3,sn\<^isub>4)" |
Seq:
"\<lbrakk> me \<turnstile> (e\<^isub>1,c\<^isub>1) \<Rightarrow> (r,c\<^isub>2);  me \<turnstile> (e\<^isub>2,c\<^isub>2) \<Rightarrow> c\<^isub>3 \<rbrakk> \<Longrightarrow>
 me \<turnstile> (e\<^isub>1; e\<^isub>2,c\<^isub>1) \<Rightarrow> c\<^isub>3" |
IfTrue:
"\<lbrakk> me \<turnstile> (b,c\<^isub>1) \<rightarrow> (True,c\<^isub>2);  me \<turnstile> (e\<^isub>1,c\<^isub>2) \<Rightarrow> c\<^isub>3 \<rbrakk> \<Longrightarrow>
 me \<turnstile> (IF b THEN e\<^isub>1 ELSE e\<^isub>2,c\<^isub>1) \<Rightarrow> c\<^isub>3" |
IfFalse:
"\<lbrakk> me \<turnstile> (b,c\<^isub>1) \<rightarrow> (False,c\<^isub>2);  me \<turnstile> (e\<^isub>2,c\<^isub>2) \<Rightarrow> c\<^isub>3 \<rbrakk> \<Longrightarrow>
 me \<turnstile> (IF b THEN e\<^isub>1 ELSE e\<^isub>2,c\<^isub>1) \<Rightarrow> c\<^isub>3" |

"me \<turnstile> (B bv,c) \<rightarrow> (bv,c)" |

"me \<turnstile> (b,c\<^isub>1) \<rightarrow> (bv,c\<^isub>2) \<Longrightarrow> me \<turnstile> (Not b,c\<^isub>1) \<rightarrow> (\<not>bv,c\<^isub>2)" |

"\<lbrakk> me \<turnstile> (b\<^isub>1,c\<^isub>1) \<rightarrow> (bv\<^isub>1,c\<^isub>2);  me \<turnstile> (b\<^isub>2,c\<^isub>2) \<rightarrow> (bv\<^isub>2,c\<^isub>3) \<rbrakk> \<Longrightarrow>
 me \<turnstile> (And b\<^isub>1 b\<^isub>2,c\<^isub>1) \<rightarrow> (bv\<^isub>1\<and>bv\<^isub>2,c\<^isub>3)" |

"\<lbrakk> me \<turnstile> (e\<^isub>1,c\<^isub>1) \<Rightarrow> (r\<^isub>1,c\<^isub>2);  me \<turnstile> (e\<^isub>2,c\<^isub>2) \<Rightarrow> (r\<^isub>2,c\<^isub>3) \<rbrakk> \<Longrightarrow>
 me \<turnstile> (Eq e\<^isub>1 e\<^isub>2,c\<^isub>1) \<rightarrow> (r\<^isub>1=r\<^isub>2,c\<^isub>3)"


code_pred (modes: i => i => o => bool) big_step .

text{* Example: natural numbers encoded as objects with a predecessor
field. Null is zero. Method succ adds an object in front, method add
adds as many objects in front as the parameter specifies.

First, the method bodies: *}

definition
"m_succ  =  (''s'' ::= New)\<bullet>''pred'' ::= V ''this''; V ''s''"

definition "m_add =
  IF Eq (V ''param'') Null
  THEN V ''this''
  ELSE V ''this''\<bullet>''succ''<Null>\<bullet>''add''<V ''param''\<bullet>''pred''>"

text{* The method environment: *}
definition
"menv = (\<lambda>m. Null)(''succ'' := m_succ, ''add'' := m_add)"

text{* The main code, adding 1 and 2: *}
definition "main =
  ''1'' ::= Null\<bullet>''succ''<Null>;
  ''2'' ::= V ''1''\<bullet>''succ''<Null>;
  V ''2'' \<bullet> ''add'' <V ''1''>"

text{* Execution of semantics. The final variable environment and store are
converted into lists of references based on given lists of variable and field
names to extract. *}

values
 "{(r, map ve' [''1'',''2''], map (\<lambda>n. map (s' n)[''pred'']) [0..<n])|
    r ve' s' n. menv \<turnstile> (main, \<lambda>x. null, nth[], 0) \<Rightarrow> (r,ve',s',n)}"

end

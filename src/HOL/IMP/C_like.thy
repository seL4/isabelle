theory C_like imports Main begin

subsection "A C-like Language"

type_synonym state = "nat \<Rightarrow> nat"

datatype aexp = N nat | Deref aexp (\<open>!\<close>) | Plus aexp aexp

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> nat" where
"aval (N n) s = n" |
"aval (!a) s = s(aval a s)" |
"aval (Plus a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s + aval a\<^sub>2 s"

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

primrec bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc v) _ = v" |
"bval (Not b) s = (\<not> bval b s)" |
"bval (And b\<^sub>1 b\<^sub>2) s = (if bval b\<^sub>1 s then bval b\<^sub>2 s else False)" |
"bval (Less a\<^sub>1 a\<^sub>2) s = (aval a\<^sub>1 s < aval a\<^sub>2 s)"


datatype
  com = SKIP 
      | Assign aexp aexp         (\<open>_ ::= _\<close> [61, 61] 61)
      | New    aexp aexp
      | Seq    com  com          (\<open>_;/ _\<close>  [60, 61] 60)
      | If     bexp com com     (\<open>(IF _/ THEN _/ ELSE _)\<close>  [0, 0, 61] 61)
      | While  bexp com         (\<open>(WHILE _/ DO _)\<close>  [0, 61] 61)

inductive
  big_step :: "com \<times> state \<times> nat \<Rightarrow> state \<times> nat \<Rightarrow> bool"  (infix \<open>\<Rightarrow>\<close> 55)
where
Skip:    "(SKIP,sn) \<Rightarrow> sn" |
Assign:  "(lhs ::= a,s,n) \<Rightarrow> (s(aval lhs s := aval a s),n)" |
New:     "(New lhs a,s,n) \<Rightarrow> (s(aval lhs s := n), n+aval a s)"  |
Seq:    "\<lbrakk> (c\<^sub>1,sn\<^sub>1) \<Rightarrow> sn\<^sub>2;  (c\<^sub>2,sn\<^sub>2) \<Rightarrow> sn\<^sub>3 \<rbrakk> \<Longrightarrow>
          (c\<^sub>1;c\<^sub>2, sn\<^sub>1) \<Rightarrow> sn\<^sub>3" |

IfTrue:  "\<lbrakk> bval b s;  (c\<^sub>1,s,n) \<Rightarrow> tn \<rbrakk> \<Longrightarrow>
         (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s,n) \<Rightarrow> tn" |
IfFalse: "\<lbrakk> \<not>bval b s;  (c\<^sub>2,s,n) \<Rightarrow> tn \<rbrakk> \<Longrightarrow>
         (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s,n) \<Rightarrow> tn" |

WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c,s,n) \<Rightarrow> (s,n)" |
WhileTrue:
  "\<lbrakk> bval b s\<^sub>1;  (c,s\<^sub>1,n) \<Rightarrow> sn\<^sub>2;  (WHILE b DO c, sn\<^sub>2) \<Rightarrow> sn\<^sub>3 \<rbrakk> \<Longrightarrow>
   (WHILE b DO c, s\<^sub>1,n) \<Rightarrow> sn\<^sub>3"

code_pred big_step .

declare [[values_timeout = 3600]]

text\<open>Examples:\<close>

definition
"array_sum =
 WHILE Less (!(N 0)) (Plus (!(N 1)) (N 1))
 DO ( N 2 ::= Plus (!(N 2)) (!(!(N 0)));
      N 0 ::= Plus (!(N 0)) (N 1) )"

text \<open>To show the first n variables in a \<^typ>\<open>nat \<Rightarrow> nat\<close> state:\<close>
definition 
  "list t n = map t [0 ..< n]"

values "{list t n |t n. (array_sum, nth[3,4,0,3,7],5) \<Rightarrow> (t,n)}"

definition
"linked_list_sum =
 WHILE Less (N 0) (!(N 0))
 DO ( N 1 ::= Plus(!(N 1)) (!(!(N 0)));
      N 0 ::= !(Plus(!(N 0))(N 1)) )"

values "{list t n |t n. (linked_list_sum, nth[4,0,3,0,7,2],6) \<Rightarrow> (t,n)}"

definition
"array_init =
 New (N 0) (!(N 1)); N 2 ::= !(N 0);
 WHILE Less (!(N 2)) (Plus (!(N 0)) (!(N 1)))
 DO ( !(N 2) ::= !(N 2);
      N 2 ::= Plus (!(N 2)) (N 1) )"

values "{list t n |t n. (array_init, nth[5,2,7],3) \<Rightarrow> (t,n)}"

definition
"linked_list_init =
 WHILE Less (!(N 1)) (!(N 0))
 DO ( New (N 3) (N 2);
      N 1 ::=  Plus (!(N 1)) (N 1);
      !(N 3) ::= !(N 1);
      Plus (!(N 3)) (N 1) ::= !(N 2);
      N 2 ::= !(N 3) )"

values "{list t n |t n. (linked_list_init, nth[2,0,0,0],4) \<Rightarrow> (t,n)}"

end

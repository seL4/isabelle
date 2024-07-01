(*  Title:      HOL/Examples/Ackermann.thy
    Author:     Larry Paulson
*)

section \<open>A Tail-Recursive, Stack-Based Ackermann's Function\<close>

theory Ackermann
  imports "HOL-Library.Multiset_Order" "HOL-Library.Product_Lexorder"
begin

text \<open>
  This theory investigates a stack-based implementation of Ackermann's
  function. Let's recall the traditional definition, as modified by Péter
  Rózsa and Raphael Robinson.
\<close>
fun ack :: "[nat, nat] \<Rightarrow> nat"
  where
    "ack 0 n             = Suc n"
  | "ack (Suc m) 0       = ack m 1"
  | "ack (Suc m) (Suc n) = ack m (ack (Suc m) n)"


subsection \<open>Example of proving termination by reasoning about the domain\<close>

text \<open>The stack-based version uses lists.\<close>

function (domintros) ackloop :: "nat list \<Rightarrow> nat"
  where
    "ackloop (n # 0 # l)         = ackloop (Suc n # l)"
  | "ackloop (0 # Suc m # l)     = ackloop (1 # m # l)"
  | "ackloop (Suc n # Suc m # l) = ackloop (n # Suc m # m # l)"
  | "ackloop [m] = m"
  | "ackloop [] =  0"
  by pat_completeness auto

text \<open>
  The key task is to prove termination. In the first recursive call, the head of
  the list gets bigger while the list gets shorter, suggesting that the length
  of the list should be the primary termination criterion. But in the third
  recursive call, the list gets longer. The idea of trying a multiset-based
  termination argument is frustrated by the second recursive call when \<open>m = 0\<close>:
  the list elements are simply permuted.

  Fortunately, the function definition package allows us to define a function
  and only later identify its domain of termination. Instead, it makes all the
  recursion equations conditional on satisfying the function's domain predicate.
  Here we shall eventually be able to show that the predicate is always
  satisfied.
\<close>

text \<open>@{thm [display] ackloop.domintros[no_vars]}\<close>
declare ackloop.domintros [simp]

text \<open>
  Termination is trivial if the length of the list is less then two. The
  following lemma is the key to proving termination for longer lists.
\<close>
lemma "ackloop_dom (ack m n # l) \<Longrightarrow> ackloop_dom (n # m # l)"
proof (induction m arbitrary: n l)
  case 0
  then show ?case
    by auto
next
  case (Suc m)
  show ?case
    using Suc.prems
    by (induction n arbitrary: l) (simp_all add: Suc)
qed

text \<open>
  The proof above (which actually is unused) can be expressed concisely as
  follows.
\<close>
lemma ackloop_dom_longer:
  "ackloop_dom (ack m n # l) \<Longrightarrow> ackloop_dom (n # m # l)"
  by (induction m n arbitrary: l rule: ack.induct) auto

text \<open>
  This function codifies what @{term ackloop} is designed to do. Proving the
  two functions equivalent also shows that @{term ackloop} can be used to
  compute Ackermann's function.
\<close>
fun acklist :: "nat list \<Rightarrow> nat"
  where
    "acklist (n#m#l) = acklist (ack m n # l)"
  | "acklist [m] = m"
  | "acklist [] =  0"

text \<open>The induction rule for @{term acklist} is @{thm [display] acklist.induct[no_vars]}.\<close>

lemma ackloop_dom: "ackloop_dom l"
  by (induction l rule: acklist.induct) (auto simp: ackloop_dom_longer)

termination ackloop
  by (simp add: ackloop_dom)

text \<open>
  This result is trivial even by inspection of the function definitions (which
  faithfully follow the definition of Ackermann's function). All that we
  needed was termination.
\<close>
lemma ackloop_acklist: "ackloop l = acklist l"
  by (induction l rule: ackloop.induct) auto

theorem ack: "ack m n = ackloop [n,m]"
  by (simp add: ackloop_acklist)


subsection \<open>Example of proving termination using a multiset ordering\<close>

text \<open>
  This termination proof uses the argument from
  Nachum Dershowitz and Zohar Manna. Proving termination with multiset orderings.
  Communications of the ACM 22 (8) 1979, 465--476.
\<close>

text \<open>
  Setting up the termination proof. Note that Dershowitz had @{term z} as a
  global variable. The top two stack elements are treated differently from the
  rest.
\<close>
fun ack_mset :: "nat list \<Rightarrow> (nat\<times>nat) multiset"
  where
    "ack_mset [] = {#}"
  | "ack_mset [x] = {#}"
  | "ack_mset (z#y#l) = mset ((y,z) # map (\<lambda>x. (Suc x, 0)) l)"

lemma case1: "ack_mset (Suc n # l) < add_mset (0,n) {# (Suc x, 0). x \<in># mset l #}"
proof (cases l)
  case (Cons m list)
  have "{#(m, Suc n)#} < {#(Suc m, 0)#}"
    by auto
  also have "\<dots> \<le> {#(Suc m, 0), (0,n)#}"
    by auto
  finally show ?thesis
    by (simp add: Cons)
next
  case Nil
  then show ?thesis by auto
qed

text \<open>
  The stack-based version again. We need a fresh copy because we've already
  proved the termination of @{term ackloop}.
\<close>
function Ackloop :: "nat list \<Rightarrow> nat"
  where
    "Ackloop (n # 0 # l)         = Ackloop (Suc n # l)"
  | "Ackloop (0 # Suc m # l)     = Ackloop (1 # m # l)"
  | "Ackloop (Suc n # Suc m # l) = Ackloop (n # Suc m # m # l)"
  | "Ackloop [m] = m"
  | "Ackloop [] =  0"
  by pat_completeness auto


text \<open>
  In each recursive call, the function @{term ack_mset} decreases according to
  the multiset ordering.
\<close>
termination
  by (relation "inv_image {(x,y). x<y} ack_mset") (auto simp: wf case1)

text \<open>
  Another shortcut compared with before: equivalence follows directly from
  this lemma.
\<close>
lemma Ackloop_ack: "Ackloop (n # m # l) = Ackloop (ack m n # l)"
  by (induction m n arbitrary: l rule: ack.induct) auto

theorem "ack m n = Ackloop [n,m]"
  by (simp add: Ackloop_ack)

end

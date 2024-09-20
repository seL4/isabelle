(* Author: Andreas Lochbihler, Digital Asset *)

theory Code_Lazy_Demo imports
  "HOL-Library.Code_Lazy"
  "HOL-Library.Debug"
  "HOL-Library.RBT_Impl"
begin

text \<open>This theory demonstrates the use of the \<^theory>\<open>HOL-Library.Code_Lazy\<close> theory.\<close>

section \<open>Streams\<close>

text \<open>Lazy evaluation for streams\<close>

codatatype 'a stream = 
  SCons (shd: 'a) (stl: "'a stream") (infixr \<open>##\<close> 65)

primcorec up :: "nat \<Rightarrow> nat stream" where
  "up n = n ## up (n + 1)"

primrec stake :: "nat \<Rightarrow> 'a stream \<Rightarrow> 'a list" where
  "stake 0 xs = []"
| "stake (Suc n) xs = shd xs # stake n (stl xs)"

code_thms up stake \<comment> \<open>The original code equations\<close>

code_lazy_type stream

code_thms up stake \<comment> \<open>The lazified code equations\<close>

value "stake 5 (up 3)"


section \<open>Finite lazy lists\<close>

text \<open>Lazy types need not be infinite. We can also have lazy types that are finite.\<close>

datatype 'a llist
  = LNil (\<open>\<^bold>\<lbrakk>\<^bold>\<rbrakk>\<close>) 
  | LCons (lhd: 'a) (ltl: "'a llist") (infixr \<open>###\<close> 65)

nonterminal llist_args
syntax
  "" :: "'a \<Rightarrow> llist_args"  (\<open>_\<close>)
  "_llist_args" :: "'a \<Rightarrow> llist_args \<Rightarrow> llist_args"  (\<open>_,/ _\<close>)
  "_llist" :: "llist_args => 'a list"    (\<open>\<^bold>\<lbrakk>(_)\<^bold>\<rbrakk>\<close>)
syntax_consts
  "_llist_args" "_llist" == LCons
translations
  "\<^bold>\<lbrakk>x, xs\<^bold>\<rbrakk>" == "x###\<^bold>\<lbrakk>xs\<^bold>\<rbrakk>"
  "\<^bold>\<lbrakk>x\<^bold>\<rbrakk>" == "x###\<^bold>\<lbrakk>\<^bold>\<rbrakk>"

fun lnth :: "nat \<Rightarrow> 'a llist \<Rightarrow> 'a" where
  "lnth 0 (x ### xs) = x"
| "lnth (Suc n) (x ### xs) = lnth n xs"

definition llist :: "nat llist" where
  "llist = \<^bold>\<lbrakk>1, 2, 3, hd [], 4\<^bold>\<rbrakk>"

code_lazy_type llist

value [code] "llist"
value [code] "lnth 2 llist"
value [code] "let x = lnth 2 llist in (x, llist)"

fun lfilter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where
  "lfilter P \<^bold>\<lbrakk>\<^bold>\<rbrakk> = \<^bold>\<lbrakk>\<^bold>\<rbrakk>"
| "lfilter P (x ### xs) = 
   (if P x then x ### lfilter P xs else lfilter P xs)"

export_code lfilter in SML file_prefix lfilter

value [code] "lfilter odd llist"

value [code] "lhd (lfilter odd llist)"


section \<open>Iterator for red-black trees\<close>

text \<open>Thanks to laziness, we do not need to program a complicated iterator for a tree. 
  A conversion function to lazy lists is enough.\<close>

primrec lappend :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> 'a llist"
  (infixr \<open>@@\<close> 65) where
  "\<^bold>\<lbrakk>\<^bold>\<rbrakk> @@ ys = ys"
| "(x ### xs) @@ ys = x ### (xs @@ ys)"

primrec rbt_iterator :: "('a, 'b) rbt \<Rightarrow> ('a \<times> 'b) llist" where
  "rbt_iterator rbt.Empty = \<^bold>\<lbrakk>\<^bold>\<rbrakk>"
| "rbt_iterator (Branch _ l k v r) = 
   (let _ = Debug.flush (STR ''tick'') in 
   rbt_iterator l @@ (k, v) ### rbt_iterator r)"

definition tree :: "(nat, unit) rbt"
  where "tree = fold (\<lambda>k. rbt_insert k ()) [0..<100] rbt.Empty"

definition find_min :: "('a :: linorder, 'b) rbt \<Rightarrow> ('a \<times> 'b) option" where
  "find_min rbt = 
  (case rbt_iterator rbt of \<^bold>\<lbrakk>\<^bold>\<rbrakk> \<Rightarrow> None 
   | kv ### _ \<Rightarrow> Some kv)"

value "find_min tree" \<comment> \<open>Observe that \<^const>\<open>rbt_iterator\<close> is evaluated only for going down 
  to the first leaf, not for the whole tree (as seen by the ticks).\<close>

text \<open>With strict lists, the whole tree is converted into a list.\<close>

deactivate_lazy_type llist
value "find_min tree"
activate_lazy_type llist



section \<open>Branching datatypes\<close>

datatype tree
  = L              (\<open>\<spadesuit>\<close>) 
  | Node tree tree (infix \<open>\<triangle>\<close> 900)

notation (output) Node (\<open>\<triangle>(//\<^bold>l: _//\<^bold>r: _)\<close>)

code_lazy_type tree

fun mk_tree :: "nat \<Rightarrow> tree" where mk_tree_0:
  "mk_tree 0 = \<spadesuit>"
| "mk_tree (Suc n) = (let t = mk_tree n in t \<triangle> t)"

declare mk_tree.simps [code]

code_thms mk_tree

function subtree :: "bool list \<Rightarrow> tree \<Rightarrow> tree" where
  "subtree [] t = t"
| "subtree (True # p) (l \<triangle> r) = subtree p l"
| "subtree (False # p) (l \<triangle> r) = subtree p r"
| "subtree _ \<spadesuit> = \<spadesuit>"
  by pat_completeness auto
termination by lexicographic_order

value [code] "mk_tree 10"
value [code] "let t = mk_tree 10; _ = subtree [True, True, False, False] t in t"
  \<comment> \<open>Since \<^const>\<open>mk_tree\<close> shares the two subtrees of a node thanks to the let binding,
      digging into one subtree spreads to the whole tree.\<close>
value [code] "let t = mk_tree 3; _ = subtree [True, True, False, False] t in t"

lemma mk_tree_Suc_debug [code]: \<comment> \<open>Make the evaluation visible with tracing.\<close>
  "mk_tree (Suc n) = 
  (let _ = Debug.flush (STR ''tick''); t = mk_tree n in t \<triangle> t)"
  by simp

value [code] "mk_tree 10"
  \<comment> \<open>The recursive call to \<^const>\<open>mk_tree\<close> is not guarded by a lazy constructor,
      so all the suspensions are built up immediately.\<close>

lemma mk_tree_Suc [code]: "mk_tree (Suc n) = mk_tree n \<triangle> mk_tree n"
  \<comment> \<open>In this code equation, there is no sharing and the recursive calls are guarded by a constructor.\<close>
  by(simp add: Let_def)

value [code] "mk_tree 10"
value [code] "let t = mk_tree 10; _ = subtree [True, True, False, False] t in t"

lemma mk_tree_Suc_debug' [code]: 
  "mk_tree (Suc n) = (let _ = Debug.flush (STR ''tick'') in mk_tree n \<triangle> mk_tree n)"
  by(simp add: Let_def)

value [code] "mk_tree 10" \<comment> \<open>Only one tick thanks to the guarding constructor\<close>
value [code] "let t = mk_tree 10; _ = subtree [True, True, False, False] t in t"
value [code] "let t = mk_tree 3; _ = subtree [True, True, False, False] t in t"


section \<open>Pattern matching elimination\<close>

text \<open>The pattern matching elimination handles deep pattern matches and overlapping equations
 and only eliminates necessary pattern matches.\<close>

function crazy :: "nat llist llist \<Rightarrow> tree \<Rightarrow> bool \<Rightarrow> unit" where
  "crazy (\<^bold>\<lbrakk>0\<^bold>\<rbrakk> ### xs) _ _    = Debug.flush (1 :: integer)"
| "crazy xs          \<spadesuit> True = Debug.flush (2 :: integer)"
| "crazy xs          t  b   = Debug.flush (3 :: integer)"
  by pat_completeness auto
termination by lexicographic_order

code_thms crazy

end
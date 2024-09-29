(*  Title:      ZF/List.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

section\<open>Lists in Zermelo-Fraenkel Set Theory\<close>

theory List imports Datatype ArithSimp begin

consts
  list       :: "i\<Rightarrow>i"

datatype
  "list(A)" = Nil | Cons ("a \<in> A", "l \<in> list(A)")

notation Nil (\<open>[]\<close>)

nonterminal list_args
syntax
  "" :: "i \<Rightarrow> list_args"  (\<open>_\<close>)
  "_List_args" :: "[i, list_args] \<Rightarrow> list_args"  (\<open>_,/ _\<close>)
  "_List" :: "list_args \<Rightarrow> i"  (\<open>[(\<open>notation=\<open>mixfix list enumeration\<close>\<close>_)]\<close>)
syntax_consts
  Cons
translations
  "[x, xs]"     == "CONST Cons(x, [xs])"
  "[x]"         == "CONST Cons(x, [])"

consts
  length :: "i\<Rightarrow>i"
  hd     :: "i\<Rightarrow>i"
  tl     :: "i\<Rightarrow>i"

primrec
  "length([]) = 0"
  "length(Cons(a,l)) = succ(length(l))"

primrec
  "hd([]) = 0"
  "hd(Cons(a,l)) = a"

primrec
  "tl([]) = []"
  "tl(Cons(a,l)) = l"


consts
  map         :: "[i\<Rightarrow>i, i] \<Rightarrow> i"
  set_of_list :: "i\<Rightarrow>i"
  app         :: "[i,i]\<Rightarrow>i"                        (infixr \<open>@\<close> 60)

(*map is a binding operator -- it applies to meta-level functions, not
object-level functions.  This simplifies the final form of term_rec_conv,
although complicating its derivation.*)
primrec
  "map(f,[]) = []"
  "map(f,Cons(a,l)) = Cons(f(a), map(f,l))"

primrec
  "set_of_list([]) = 0"
  "set_of_list(Cons(a,l)) = cons(a, set_of_list(l))"

primrec
  app_Nil:  "[] @ ys = ys"
  app_Cons: "(Cons(a,l)) @ ys = Cons(a, l @ ys)"


consts
  rev :: "i\<Rightarrow>i"
  flat       :: "i\<Rightarrow>i"
  list_add   :: "i\<Rightarrow>i"

primrec
  "rev([]) = []"
  "rev(Cons(a,l)) = rev(l) @ [a]"

primrec
  "flat([]) = []"
  "flat(Cons(l,ls)) = l @ flat(ls)"

primrec
  "list_add([]) = 0"
  "list_add(Cons(a,l)) = a #+ list_add(l)"

consts
  drop       :: "[i,i]\<Rightarrow>i"

primrec
  drop_0:    "drop(0,l) = l"
  drop_succ: "drop(succ(i), l) = tl (drop(i,l))"


(*** Thanks to Sidi Ehmety for the following ***)

definition
(* Function `take' returns the first n elements of a list *)
  take     :: "[i,i]\<Rightarrow>i"  where
  "take(n, as) \<equiv> list_rec(\<lambda>n\<in>nat. [],
                \<lambda>a l r. \<lambda>n\<in>nat. nat_case([], \<lambda>m. Cons(a, r`m), n), as)`n"

definition
  nth :: "[i, i]\<Rightarrow>i"  where
  \<comment> \<open>returns the (n+1)th element of a list, or 0 if the
   list is too short.\<close>
  "nth(n, as) \<equiv> list_rec(\<lambda>n\<in>nat. 0,
                          \<lambda>a l r. \<lambda>n\<in>nat. nat_case(a, \<lambda>m. r`m, n), as) ` n"

definition
  list_update :: "[i, i, i]\<Rightarrow>i"  where
  "list_update(xs, i, v) \<equiv> list_rec(\<lambda>n\<in>nat. Nil,
      \<lambda>u us vs. \<lambda>n\<in>nat. nat_case(Cons(v, us), \<lambda>m. Cons(u, vs`m), n), xs)`i"

consts
  filter :: "[i\<Rightarrow>o, i] \<Rightarrow> i"
  upt :: "[i, i] \<Rightarrow>i"

primrec
  "filter(P, Nil) = Nil"
  "filter(P, Cons(x, xs)) =
     (if P(x) then Cons(x, filter(P, xs)) else filter(P, xs))"

primrec
  "upt(i, 0) = Nil"
  "upt(i, succ(j)) = (if i \<le> j then upt(i, j)@[j] else Nil)"

definition
  min :: "[i,i] \<Rightarrow>i"  where
    "min(x, y) \<equiv> (if x \<le> y then x else y)"

definition
  max :: "[i, i] \<Rightarrow>i"  where
    "max(x, y) \<equiv> (if x \<le> y then y else x)"

(*** Aspects of the datatype definition ***)

declare list.intros [simp,TC]

(*An elimination rule, for type-checking*)
inductive_cases ConsE: "Cons(a,l) \<in> list(A)"

lemma Cons_type_iff [simp]: "Cons(a,l) \<in> list(A) \<longleftrightarrow> a \<in> A \<and> l \<in> list(A)"
by (blast elim: ConsE)

(*Proving freeness results*)
lemma Cons_iff: "Cons(a,l)=Cons(a',l') \<longleftrightarrow> a=a' \<and> l=l'"
by auto

lemma Nil_Cons_iff: "\<not> Nil=Cons(a,l)"
by auto

lemma list_unfold: "list(A) = {0} + (A * list(A))"
by (blast intro!: list.intros [unfolded list.con_defs]
          elim: list.cases [unfolded list.con_defs])


(**  Lemmas to justify using "list" in other recursive type definitions **)

lemma list_mono: "A<=B \<Longrightarrow> list(A) \<subseteq> list(B)"
  unfolding list.defs 
apply (rule lfp_mono)
apply (simp_all add: list.bnd_mono)
apply (assumption | rule univ_mono basic_monos)+
done

(*There is a similar proof by list induction.*)
lemma list_univ: "list(univ(A)) \<subseteq> univ(A)"
  unfolding list.defs list.con_defs
apply (rule lfp_lowerbound)
apply (rule_tac [2] A_subset_univ [THEN univ_mono])
apply (blast intro!: zero_in_univ Inl_in_univ Inr_in_univ Pair_in_univ)
done

(*These two theorems justify datatypes involving list(nat), list(A), ...*)
lemmas list_subset_univ = subset_trans [OF list_mono list_univ]

lemma list_into_univ: "\<lbrakk>l \<in> list(A);  A \<subseteq> univ(B)\<rbrakk> \<Longrightarrow> l \<in> univ(B)"
by (blast intro: list_subset_univ [THEN subsetD])

lemma list_case_type:
    "\<lbrakk>l \<in> list(A);
        c \<in> C(Nil);
        \<And>x y. \<lbrakk>x \<in> A;  y \<in> list(A)\<rbrakk> \<Longrightarrow> h(x,y): C(Cons(x,y))
\<rbrakk> \<Longrightarrow> list_case(c,h,l) \<in> C(l)"
by (erule list.induct, auto)

lemma list_0_triv: "list(0) = {Nil}"
apply (rule equalityI, auto)
apply (induct_tac x, auto)
done


(*** List functions ***)

lemma tl_type: "l \<in> list(A) \<Longrightarrow> tl(l) \<in> list(A)"
apply (induct_tac "l")
apply (simp_all (no_asm_simp) add: list.intros)
done

(** drop **)

lemma drop_Nil [simp]: "i \<in> nat \<Longrightarrow> drop(i, Nil) = Nil"
apply (induct_tac "i")
apply (simp_all (no_asm_simp))
done

lemma drop_succ_Cons [simp]: "i \<in> nat \<Longrightarrow> drop(succ(i), Cons(a,l)) = drop(i,l)"
apply (rule sym)
apply (induct_tac "i")
apply (simp (no_asm))
apply (simp (no_asm_simp))
done

lemma drop_type [simp,TC]: "\<lbrakk>i \<in> nat; l \<in> list(A)\<rbrakk> \<Longrightarrow> drop(i,l) \<in> list(A)"
apply (induct_tac "i")
apply (simp_all (no_asm_simp) add: tl_type)
done

declare drop_succ [simp del]


(** Type checking -- proved by induction, as usual **)

lemma list_rec_type [TC]:
    "\<lbrakk>l \<in> list(A);
        c \<in> C(Nil);
        \<And>x y r. \<lbrakk>x \<in> A;  y \<in> list(A);  r \<in> C(y)\<rbrakk> \<Longrightarrow> h(x,y,r): C(Cons(x,y))
\<rbrakk> \<Longrightarrow> list_rec(c,h,l) \<in> C(l)"
by (induct_tac "l", auto)

(** map **)

lemma map_type [TC]:
    "\<lbrakk>l \<in> list(A);  \<And>x. x \<in> A \<Longrightarrow> h(x): B\<rbrakk> \<Longrightarrow> map(h,l) \<in> list(B)"
apply (simp add: map_list_def)
apply (typecheck add: list.intros list_rec_type, blast)
done

lemma map_type2 [TC]: "l \<in> list(A) \<Longrightarrow> map(h,l) \<in> list({h(u). u \<in> A})"
apply (erule map_type)
apply (erule RepFunI)
done

(** length **)

lemma length_type [TC]: "l \<in> list(A) \<Longrightarrow> length(l) \<in> nat"
by (simp add: length_list_def)

lemma lt_length_in_nat:
   "\<lbrakk>x < length(xs); xs \<in> list(A)\<rbrakk> \<Longrightarrow> x \<in> nat"
by (frule lt_nat_in_nat, typecheck)

(** app **)

lemma app_type [TC]: "\<lbrakk>xs: list(A);  ys: list(A)\<rbrakk> \<Longrightarrow> xs@ys \<in> list(A)"
by (simp add: app_list_def)

(** rev **)

lemma rev_type [TC]: "xs: list(A) \<Longrightarrow> rev(xs) \<in> list(A)"
by (simp add: rev_list_def)


(** flat **)

lemma flat_type [TC]: "ls: list(list(A)) \<Longrightarrow> flat(ls) \<in> list(A)"
by (simp add: flat_list_def)


(** set_of_list **)

lemma set_of_list_type [TC]: "l \<in> list(A) \<Longrightarrow> set_of_list(l) \<in> Pow(A)"
  unfolding set_of_list_list_def
apply (erule list_rec_type, auto)
done

lemma set_of_list_append:
     "xs: list(A) \<Longrightarrow> set_of_list (xs@ys) = set_of_list(xs) \<union> set_of_list(ys)"
apply (erule list.induct)
apply (simp_all (no_asm_simp) add: Un_cons)
done


(** list_add **)

lemma list_add_type [TC]: "xs: list(nat) \<Longrightarrow> list_add(xs) \<in> nat"
by (simp add: list_add_list_def)


(*** theorems about map ***)

lemma map_ident [simp]: "l \<in> list(A) \<Longrightarrow> map(\<lambda>u. u, l) = l"
apply (induct_tac "l")
apply (simp_all (no_asm_simp))
done

lemma map_compose: "l \<in> list(A) \<Longrightarrow> map(h, map(j,l)) = map(\<lambda>u. h(j(u)), l)"
apply (induct_tac "l")
apply (simp_all (no_asm_simp))
done

lemma map_app_distrib: "xs: list(A) \<Longrightarrow> map(h, xs@ys) = map(h,xs) @ map(h,ys)"
apply (induct_tac "xs")
apply (simp_all (no_asm_simp))
done

lemma map_flat: "ls: list(list(A)) \<Longrightarrow> map(h, flat(ls)) = flat(map(map(h),ls))"
apply (induct_tac "ls")
apply (simp_all (no_asm_simp) add: map_app_distrib)
done

lemma list_rec_map:
     "l \<in> list(A) \<Longrightarrow>
      list_rec(c, d, map(h,l)) =
      list_rec(c, \<lambda>x xs r. d(h(x), map(h,xs), r), l)"
apply (induct_tac "l")
apply (simp_all (no_asm_simp))
done

(** theorems about list(Collect(A,P)) -- used in Induct/Term.thy **)

(* @{term"c \<in> list(Collect(B,P)) \<Longrightarrow> c \<in> list"} *)
lemmas list_CollectD = Collect_subset [THEN list_mono, THEN subsetD]

lemma map_list_Collect: "l \<in> list({x \<in> A. h(x)=j(x)}) \<Longrightarrow> map(h,l) = map(j,l)"
apply (induct_tac "l")
apply (simp_all (no_asm_simp))
done

(*** theorems about length ***)

lemma length_map [simp]: "xs: list(A) \<Longrightarrow> length(map(h,xs)) = length(xs)"
by (induct_tac "xs", simp_all)

lemma length_app [simp]:
     "\<lbrakk>xs: list(A); ys: list(A)\<rbrakk>
      \<Longrightarrow> length(xs@ys) = length(xs) #+ length(ys)"
by (induct_tac "xs", simp_all)

lemma length_rev [simp]: "xs: list(A) \<Longrightarrow> length(rev(xs)) = length(xs)"
apply (induct_tac "xs")
apply (simp_all (no_asm_simp) add: length_app)
done

lemma length_flat:
     "ls: list(list(A)) \<Longrightarrow> length(flat(ls)) = list_add(map(length,ls))"
apply (induct_tac "ls")
apply (simp_all (no_asm_simp) add: length_app)
done

(** Length and drop **)

(*Lemma for the inductive step of drop_length*)
lemma drop_length_Cons [rule_format]:
     "xs: list(A) \<Longrightarrow>
           \<forall>x.  \<exists>z zs. drop(length(xs), Cons(x,xs)) = Cons(z,zs)"
by (erule list.induct, simp_all)

lemma drop_length [rule_format]:
     "l \<in> list(A) \<Longrightarrow> \<forall>i \<in> length(l). (\<exists>z zs. drop(i,l) = Cons(z,zs))"
apply (erule list.induct, simp_all, safe)
apply (erule drop_length_Cons)
apply (rule natE)
apply (erule Ord_trans [OF asm_rl length_type Ord_nat], assumption, simp_all)
apply (blast intro: succ_in_naturalD length_type)
done


(*** theorems about app ***)

lemma app_right_Nil [simp]: "xs: list(A) \<Longrightarrow> xs@Nil=xs"
by (erule list.induct, simp_all)

lemma app_assoc: "xs: list(A) \<Longrightarrow> (xs@ys)@zs = xs@(ys@zs)"
by (induct_tac "xs", simp_all)

lemma flat_app_distrib: "ls: list(list(A)) \<Longrightarrow> flat(ls@ms) = flat(ls)@flat(ms)"
apply (induct_tac "ls")
apply (simp_all (no_asm_simp) add: app_assoc)
done

(*** theorems about rev ***)

lemma rev_map_distrib: "l \<in> list(A) \<Longrightarrow> rev(map(h,l)) = map(h,rev(l))"
apply (induct_tac "l")
apply (simp_all (no_asm_simp) add: map_app_distrib)
done

(*Simplifier needs the premises as assumptions because rewriting will not
  instantiate the variable ?A in the rules' typing conditions; note that
  rev_type does not instantiate ?A.  Only the premises do.
*)
lemma rev_app_distrib:
     "\<lbrakk>xs: list(A);  ys: list(A)\<rbrakk> \<Longrightarrow> rev(xs@ys) = rev(ys)@rev(xs)"
apply (erule list.induct)
apply (simp_all add: app_assoc)
done

lemma rev_rev_ident [simp]: "l \<in> list(A) \<Longrightarrow> rev(rev(l))=l"
apply (induct_tac "l")
apply (simp_all (no_asm_simp) add: rev_app_distrib)
done

lemma rev_flat: "ls: list(list(A)) \<Longrightarrow> rev(flat(ls)) = flat(map(rev,rev(ls)))"
apply (induct_tac "ls")
apply (simp_all add: map_app_distrib flat_app_distrib rev_app_distrib)
done


(*** theorems about list_add ***)

lemma list_add_app:
     "\<lbrakk>xs: list(nat);  ys: list(nat)\<rbrakk>
      \<Longrightarrow> list_add(xs@ys) = list_add(ys) #+ list_add(xs)"
apply (induct_tac "xs", simp_all)
done

lemma list_add_rev: "l \<in> list(nat) \<Longrightarrow> list_add(rev(l)) = list_add(l)"
apply (induct_tac "l")
apply (simp_all (no_asm_simp) add: list_add_app)
done

lemma list_add_flat:
     "ls: list(list(nat)) \<Longrightarrow> list_add(flat(ls)) = list_add(map(list_add,ls))"
apply (induct_tac "ls")
apply (simp_all (no_asm_simp) add: list_add_app)
done

(** New induction rules **)

lemma list_append_induct [case_names Nil snoc, consumes 1]:
    "\<lbrakk>l \<in> list(A);
        P(Nil);
        \<And>x y. \<lbrakk>x \<in> A;  y \<in> list(A);  P(y)\<rbrakk> \<Longrightarrow> P(y @ [x])
\<rbrakk> \<Longrightarrow> P(l)"
apply (subgoal_tac "P(rev(rev(l)))", simp)
apply (erule rev_type [THEN list.induct], simp_all)
done

lemma list_complete_induct_lemma [rule_format]:
 assumes ih:
    "\<And>l. \<lbrakk>l \<in> list(A);
             \<forall>l' \<in> list(A). length(l') < length(l) \<longrightarrow> P(l')\<rbrakk>
          \<Longrightarrow> P(l)"
  shows "n \<in> nat \<Longrightarrow> \<forall>l \<in> list(A). length(l) < n \<longrightarrow> P(l)"
apply (induct_tac n, simp)
apply (blast intro: ih elim!: leE)
done

theorem list_complete_induct:
      "\<lbrakk>l \<in> list(A);
          \<And>l. \<lbrakk>l \<in> list(A);
                  \<forall>l' \<in> list(A). length(l') < length(l) \<longrightarrow> P(l')\<rbrakk>
               \<Longrightarrow> P(l)
\<rbrakk> \<Longrightarrow> P(l)"
apply (rule list_complete_induct_lemma [of A])
   prefer 4 apply (rule le_refl, simp)
  apply blast
 apply simp
apply assumption
done


(*** Thanks to Sidi Ehmety for these results about min, take, etc. ***)

(** min FIXME: replace by Int! **)
(* Min theorems are also true for i, j ordinals *)
lemma min_sym: "\<lbrakk>i \<in> nat; j \<in> nat\<rbrakk> \<Longrightarrow> min(i,j)=min(j,i)"
  unfolding min_def
apply (auto dest!: not_lt_imp_le dest: lt_not_sym intro: le_anti_sym)
done

lemma min_type [simp,TC]: "\<lbrakk>i \<in> nat; j \<in> nat\<rbrakk> \<Longrightarrow> min(i,j):nat"
by (unfold min_def, auto)

lemma min_0 [simp]: "i \<in> nat \<Longrightarrow> min(0,i) = 0"
  unfolding min_def
apply (auto dest: not_lt_imp_le)
done

lemma min_02 [simp]: "i \<in> nat \<Longrightarrow> min(i, 0) = 0"
  unfolding min_def
apply (auto dest: not_lt_imp_le)
done

lemma lt_min_iff: "\<lbrakk>i \<in> nat; j \<in> nat; k \<in> nat\<rbrakk> \<Longrightarrow> i<min(j,k) \<longleftrightarrow> i<j \<and> i<k"
  unfolding min_def
apply (auto dest!: not_lt_imp_le intro: lt_trans2 lt_trans)
done

lemma min_succ_succ [simp]:
     "\<lbrakk>i \<in> nat; j \<in> nat\<rbrakk> \<Longrightarrow>  min(succ(i), succ(j))= succ(min(i, j))"
apply (unfold min_def, auto)
done

(*** more theorems about lists ***)

(** filter **)

lemma filter_append [simp]:
     "xs:list(A) \<Longrightarrow> filter(P, xs@ys) = filter(P, xs) @ filter(P, ys)"
by (induct_tac "xs", auto)

lemma filter_type [simp,TC]: "xs:list(A) \<Longrightarrow> filter(P, xs):list(A)"
by (induct_tac "xs", auto)

lemma length_filter: "xs:list(A) \<Longrightarrow> length(filter(P, xs)) \<le> length(xs)"
apply (induct_tac "xs", auto)
apply (rule_tac j = "length (l) " in le_trans)
apply (auto simp add: le_iff)
done

lemma filter_is_subset: "xs:list(A) \<Longrightarrow> set_of_list(filter(P,xs)) \<subseteq> set_of_list(xs)"
by (induct_tac "xs", auto)

lemma filter_False [simp]: "xs:list(A) \<Longrightarrow> filter(\<lambda>p. False, xs) = Nil"
by (induct_tac "xs", auto)

lemma filter_True [simp]: "xs:list(A) \<Longrightarrow> filter(\<lambda>p. True, xs) = xs"
by (induct_tac "xs", auto)

(** length **)

lemma length_is_0_iff [simp]: "xs:list(A) \<Longrightarrow> length(xs)=0 \<longleftrightarrow> xs=Nil"
by (erule list.induct, auto)

lemma length_is_0_iff2 [simp]: "xs:list(A) \<Longrightarrow> 0 = length(xs) \<longleftrightarrow> xs=Nil"
by (erule list.induct, auto)

lemma length_tl [simp]: "xs:list(A) \<Longrightarrow> length(tl(xs)) = length(xs) #- 1"
by (erule list.induct, auto)

lemma length_greater_0_iff: "xs:list(A) \<Longrightarrow> 0<length(xs) \<longleftrightarrow> xs \<noteq> Nil"
by (erule list.induct, auto)

lemma length_succ_iff: "xs:list(A) \<Longrightarrow> length(xs)=succ(n) \<longleftrightarrow> (\<exists>y ys. xs=Cons(y, ys) \<and> length(ys)=n)"
by (erule list.induct, auto)

(** more theorems about append **)

lemma append_is_Nil_iff [simp]:
     "xs:list(A) \<Longrightarrow> (xs@ys = Nil) \<longleftrightarrow> (xs=Nil \<and> ys = Nil)"
by (erule list.induct, auto)

lemma append_is_Nil_iff2 [simp]:
     "xs:list(A) \<Longrightarrow> (Nil = xs@ys) \<longleftrightarrow> (xs=Nil \<and> ys = Nil)"
by (erule list.induct, auto)

lemma append_left_is_self_iff [simp]:
     "xs:list(A) \<Longrightarrow> (xs@ys = xs) \<longleftrightarrow> (ys = Nil)"
by (erule list.induct, auto)

lemma append_left_is_self_iff2 [simp]:
     "xs:list(A) \<Longrightarrow> (xs = xs@ys) \<longleftrightarrow> (ys = Nil)"
by (erule list.induct, auto)

(*TOO SLOW as a default simprule!*)
lemma append_left_is_Nil_iff [rule_format]:
     "\<lbrakk>xs:list(A); ys:list(A); zs:list(A)\<rbrakk> \<Longrightarrow>
   length(ys)=length(zs) \<longrightarrow> (xs@ys=zs \<longleftrightarrow> (xs=Nil \<and> ys=zs))"
apply (erule list.induct)
apply (auto simp add: length_app)
done

(*TOO SLOW as a default simprule!*)
lemma append_left_is_Nil_iff2 [rule_format]:
     "\<lbrakk>xs:list(A); ys:list(A); zs:list(A)\<rbrakk> \<Longrightarrow>
   length(ys)=length(zs) \<longrightarrow> (zs=ys@xs \<longleftrightarrow> (xs=Nil \<and> ys=zs))"
apply (erule list.induct)
apply (auto simp add: length_app)
done

lemma append_eq_append_iff [rule_format]:
     "xs:list(A) \<Longrightarrow> \<forall>ys \<in> list(A).
      length(xs)=length(ys) \<longrightarrow> (xs@us = ys@vs) \<longleftrightarrow> (xs=ys \<and> us=vs)"
apply (erule list.induct)
apply (simp (no_asm_simp))
apply clarify
apply (erule_tac a = ys in list.cases, auto)
done
declare append_eq_append_iff [simp]

lemma append_eq_append [rule_format]:
  "xs:list(A) \<Longrightarrow>
   \<forall>ys \<in> list(A). \<forall>us \<in> list(A). \<forall>vs \<in> list(A).
   length(us) = length(vs) \<longrightarrow> (xs@us = ys@vs) \<longrightarrow> (xs=ys \<and> us=vs)"
apply (induct_tac "xs")
apply (force simp add: length_app, clarify)
apply (erule_tac a = ys in list.cases, simp)
apply (subgoal_tac "Cons (a, l) @ us =vs")
 apply (drule rev_iffD1 [OF _ append_left_is_Nil_iff], simp_all, blast)
done

lemma append_eq_append_iff2 [simp]:
 "\<lbrakk>xs:list(A); ys:list(A); us:list(A); vs:list(A); length(us)=length(vs)\<rbrakk>
  \<Longrightarrow>  xs@us = ys@vs \<longleftrightarrow> (xs=ys \<and> us=vs)"
apply (rule iffI)
apply (rule append_eq_append, auto)
done

lemma append_self_iff [simp]:
     "\<lbrakk>xs:list(A); ys:list(A); zs:list(A)\<rbrakk> \<Longrightarrow> xs@ys=xs@zs \<longleftrightarrow> ys=zs"
by simp

lemma append_self_iff2 [simp]:
     "\<lbrakk>xs:list(A); ys:list(A); zs:list(A)\<rbrakk> \<Longrightarrow> ys@xs=zs@xs \<longleftrightarrow> ys=zs"
by simp

(* Can also be proved from append_eq_append_iff2,
but the proof requires two more hypotheses: x \<in> A and y \<in> A *)
lemma append1_eq_iff [rule_format]:
     "xs:list(A) \<Longrightarrow> \<forall>ys \<in> list(A). xs@[x] = ys@[y] \<longleftrightarrow> (xs = ys \<and> x=y)"
apply (erule list.induct)
 apply clarify
 apply (erule list.cases)
 apply simp_all
txt\<open>Inductive step\<close>
apply clarify
apply (erule_tac a=ys in list.cases, simp_all)
done
declare append1_eq_iff [simp]

lemma append_right_is_self_iff [simp]:
     "\<lbrakk>xs:list(A); ys:list(A)\<rbrakk> \<Longrightarrow> (xs@ys = ys) \<longleftrightarrow> (xs=Nil)"
by (simp (no_asm_simp) add: append_left_is_Nil_iff)

lemma append_right_is_self_iff2 [simp]:
     "\<lbrakk>xs:list(A); ys:list(A)\<rbrakk> \<Longrightarrow> (ys = xs@ys) \<longleftrightarrow> (xs=Nil)"
apply (rule iffI)
apply (drule sym, auto)
done

lemma hd_append [rule_format]:
     "xs:list(A) \<Longrightarrow> xs \<noteq> Nil \<longrightarrow> hd(xs @ ys) = hd(xs)"
by (induct_tac "xs", auto)
declare hd_append [simp]

lemma tl_append [rule_format]:
     "xs:list(A) \<Longrightarrow> xs\<noteq>Nil \<longrightarrow> tl(xs @ ys) = tl(xs)@ys"
by (induct_tac "xs", auto)
declare tl_append [simp]

(** rev **)
lemma rev_is_Nil_iff [simp]: "xs:list(A) \<Longrightarrow> (rev(xs) = Nil \<longleftrightarrow> xs = Nil)"
by (erule list.induct, auto)

lemma Nil_is_rev_iff [simp]: "xs:list(A) \<Longrightarrow> (Nil = rev(xs) \<longleftrightarrow> xs = Nil)"
by (erule list.induct, auto)

lemma rev_is_rev_iff [rule_format]:
     "xs:list(A) \<Longrightarrow> \<forall>ys \<in> list(A). rev(xs)=rev(ys) \<longleftrightarrow> xs=ys"
apply (erule list.induct, force, clarify)
apply (erule_tac a = ys in list.cases, auto)
done
declare rev_is_rev_iff [simp]

lemma rev_list_elim [rule_format]:
     "xs:list(A) \<Longrightarrow>
      (xs=Nil \<longrightarrow> P) \<longrightarrow> (\<forall>ys \<in> list(A). \<forall>y \<in> A. xs =ys@[y] \<longrightarrow>P)\<longrightarrow>P"
by (erule list_append_induct, auto)


(** more theorems about drop **)

lemma length_drop [rule_format]:
     "n \<in> nat \<Longrightarrow> \<forall>xs \<in> list(A). length(drop(n, xs)) = length(xs) #- n"
apply (erule nat_induct)
apply (auto elim: list.cases)
done
declare length_drop [simp]

lemma drop_all [rule_format]:
     "n \<in> nat \<Longrightarrow> \<forall>xs \<in> list(A). length(xs) \<le> n \<longrightarrow> drop(n, xs)=Nil"
apply (erule nat_induct)
apply (auto elim: list.cases)
done
declare drop_all [simp]

lemma drop_append [rule_format]:
     "n \<in> nat \<Longrightarrow>
      \<forall>xs \<in> list(A). drop(n, xs@ys) = drop(n,xs) @ drop(n #- length(xs), ys)"
apply (induct_tac "n")
apply (auto elim: list.cases)
done

lemma drop_drop:
    "m \<in> nat \<Longrightarrow> \<forall>xs \<in> list(A). \<forall>n \<in> nat. drop(n, drop(m, xs))=drop(n #+ m, xs)"
apply (induct_tac "m")
apply (auto elim: list.cases)
done

(** take **)

lemma take_0 [simp]: "xs:list(A) \<Longrightarrow> take(0, xs) =  Nil"
  unfolding take_def
apply (erule list.induct, auto)
done

lemma take_succ_Cons [simp]:
    "n \<in> nat \<Longrightarrow> take(succ(n), Cons(a, xs)) = Cons(a, take(n, xs))"
by (simp add: take_def)

(* Needed for proving take_all *)
lemma take_Nil [simp]: "n \<in> nat \<Longrightarrow> take(n, Nil) = Nil"
by (unfold take_def, auto)

lemma take_all [rule_format]:
     "n \<in> nat \<Longrightarrow> \<forall>xs \<in> list(A). length(xs) \<le> n  \<longrightarrow> take(n, xs) = xs"
apply (erule nat_induct)
apply (auto elim: list.cases)
done
declare take_all [simp]

lemma take_type [rule_format]:
     "xs:list(A) \<Longrightarrow> \<forall>n \<in> nat. take(n, xs):list(A)"
apply (erule list.induct, simp, clarify)
apply (erule natE, auto)
done
declare take_type [simp,TC]

lemma take_append [rule_format]:
 "xs:list(A) \<Longrightarrow>
  \<forall>ys \<in> list(A). \<forall>n \<in> nat. take(n, xs @ ys) =
                            take(n, xs) @ take(n #- length(xs), ys)"
apply (erule list.induct, simp, clarify)
apply (erule natE, auto)
done
declare take_append [simp]

lemma take_take [rule_format]:
   "m \<in> nat \<Longrightarrow>
    \<forall>xs \<in> list(A). \<forall>n \<in> nat. take(n, take(m,xs))= take(min(n, m), xs)"
apply (induct_tac "m", auto)
apply (erule_tac a = xs in list.cases)
apply (auto simp add: take_Nil)
apply (erule_tac n=n in natE)
apply (auto intro: take_0 take_type)
done

(** nth **)

lemma nth_0 [simp]: "nth(0, Cons(a, l)) = a"
by (simp add: nth_def)

lemma nth_Cons [simp]: "n \<in> nat \<Longrightarrow> nth(succ(n), Cons(a,l)) = nth(n,l)"
by (simp add: nth_def)

lemma nth_empty [simp]: "nth(n, Nil) = 0"
by (simp add: nth_def)

lemma nth_type [rule_format]:
     "xs:list(A) \<Longrightarrow> \<forall>n. n < length(xs) \<longrightarrow> nth(n,xs) \<in> A"
apply (erule list.induct, simp, clarify)
apply (subgoal_tac "n \<in> nat")
 apply (erule natE, auto dest!: le_in_nat)
done
declare nth_type [simp,TC]

lemma nth_eq_0 [rule_format]:
     "xs:list(A) \<Longrightarrow> \<forall>n \<in> nat. length(xs) \<le> n \<longrightarrow> nth(n,xs) = 0"
apply (erule list.induct, simp, clarify)
apply (erule natE, auto)
done

lemma nth_append [rule_format]:
  "xs:list(A) \<Longrightarrow>
   \<forall>n \<in> nat. nth(n, xs @ ys) = (if n < length(xs) then nth(n,xs)
                                else nth(n #- length(xs), ys))"
apply (induct_tac "xs", simp, clarify)
apply (erule natE, auto)
done

lemma set_of_list_conv_nth:
    "xs:list(A)
     \<Longrightarrow> set_of_list(xs) = {x \<in> A. \<exists>i\<in>nat. i<length(xs) \<and> x = nth(i,xs)}"
apply (induct_tac "xs", simp_all)
apply (rule equalityI, auto)
apply (rule_tac x = 0 in bexI, auto)
apply (erule natE, auto)
done

(* Other theorems about lists *)

lemma nth_take_lemma [rule_format]:
 "k \<in> nat \<Longrightarrow>
  \<forall>xs \<in> list(A). (\<forall>ys \<in> list(A). k \<le> length(xs) \<longrightarrow> k \<le> length(ys) \<longrightarrow>
      (\<forall>i \<in> nat. i<k \<longrightarrow> nth(i,xs) = nth(i,ys))\<longrightarrow> take(k,xs) = take(k,ys))"
apply (induct_tac "k")
apply (simp_all (no_asm_simp) add: lt_succ_eq_0_disj all_conj_distrib)
apply clarify
(*Both lists are non-empty*)
apply (erule_tac a=xs in list.cases, simp)
apply (erule_tac a=ys in list.cases, clarify)
apply (simp (no_asm_use) )
apply clarify
apply (simp (no_asm_simp))
apply (rule conjI, force)
apply (rename_tac y ys z zs)
apply (drule_tac x = zs and x1 = ys in bspec [THEN bspec], auto)
done

lemma nth_equalityI [rule_format]:
     "\<lbrakk>xs:list(A); ys:list(A); length(xs) = length(ys);
         \<forall>i \<in> nat. i < length(xs) \<longrightarrow> nth(i,xs) = nth(i,ys)\<rbrakk>
      \<Longrightarrow> xs = ys"
apply (subgoal_tac "length (xs) \<le> length (ys) ")
apply (cut_tac k="length(xs)" and xs=xs and ys=ys in nth_take_lemma)
apply (simp_all add: take_all)
done

(*The famous take-lemma*)

lemma take_equalityI [rule_format]:
    "\<lbrakk>xs:list(A); ys:list(A); (\<forall>i \<in> nat. take(i, xs) = take(i,ys))\<rbrakk>
     \<Longrightarrow> xs = ys"
apply (case_tac "length (xs) \<le> length (ys) ")
apply (drule_tac x = "length (ys) " in bspec)
apply (drule_tac [3] not_lt_imp_le)
apply (subgoal_tac [5] "length (ys) \<le> length (xs) ")
apply (rule_tac [6] j = "succ (length (ys))" in le_trans)
apply (rule_tac [6] leI)
apply (drule_tac [5] x = "length (xs) " in bspec)
apply (simp_all add: take_all)
done

lemma nth_drop [rule_format]:
  "n \<in> nat \<Longrightarrow> \<forall>i \<in> nat. \<forall>xs \<in> list(A). nth(i, drop(n, xs)) = nth(n #+ i, xs)"
apply (induct_tac "n", simp_all, clarify)
apply (erule list.cases, auto)
done

lemma take_succ [rule_format]:
  "xs\<in>list(A)
   \<Longrightarrow> \<forall>i. i < length(xs) \<longrightarrow> take(succ(i), xs) = take(i,xs) @ [nth(i, xs)]"
apply (induct_tac "xs", auto)
apply (subgoal_tac "i\<in>nat")
apply (erule natE)
apply (auto simp add: le_in_nat)
done

lemma take_add [rule_format]:
     "\<lbrakk>xs\<in>list(A); j\<in>nat\<rbrakk>
      \<Longrightarrow> \<forall>i\<in>nat. take(i #+ j, xs) = take(i,xs) @ take(j, drop(i,xs))"
apply (induct_tac "xs", simp_all, clarify)
apply (erule_tac n = i in natE, simp_all)
done

lemma length_take:
     "l\<in>list(A) \<Longrightarrow> \<forall>n\<in>nat. length(take(n,l)) = min(n, length(l))"
apply (induct_tac "l", safe, simp_all)
apply (erule natE, simp_all)
done

subsection\<open>The function zip\<close>

text\<open>Crafty definition to eliminate a type argument\<close>

consts
  zip_aux        :: "[i,i]\<Rightarrow>i"

primrec (*explicit lambda is required because both arguments of "un" vary*)
  "zip_aux(B,[]) =
     (\<lambda>ys \<in> list(B). list_case([], \<lambda>y l. [], ys))"

  "zip_aux(B,Cons(x,l)) =
     (\<lambda>ys \<in> list(B).
        list_case(Nil, \<lambda>y zs. Cons(\<langle>x,y\<rangle>, zip_aux(B,l)`zs), ys))"

definition
  zip :: "[i, i]\<Rightarrow>i"  where
   "zip(xs, ys) \<equiv> zip_aux(set_of_list(ys),xs)`ys"


(* zip equations *)

lemma list_on_set_of_list: "xs \<in> list(A) \<Longrightarrow> xs \<in> list(set_of_list(xs))"
apply (induct_tac xs, simp_all)
apply (blast intro: list_mono [THEN subsetD])
done

lemma zip_Nil [simp]: "ys:list(A) \<Longrightarrow> zip(Nil, ys)=Nil"
apply (simp add: zip_def list_on_set_of_list [of _ A])
apply (erule list.cases, simp_all)
done

lemma zip_Nil2 [simp]: "xs:list(A) \<Longrightarrow> zip(xs, Nil)=Nil"
apply (simp add: zip_def list_on_set_of_list [of _ A])
apply (erule list.cases, simp_all)
done

lemma zip_aux_unique [rule_format]:
     "\<lbrakk>B<=C;  xs \<in> list(A)\<rbrakk>
      \<Longrightarrow> \<forall>ys \<in> list(B). zip_aux(C,xs) ` ys = zip_aux(B,xs) ` ys"
apply (induct_tac xs)
 apply simp_all
 apply (blast intro: list_mono [THEN subsetD], clarify)
apply (erule_tac a=ys in list.cases, auto)
apply (blast intro: list_mono [THEN subsetD])
done

lemma zip_Cons_Cons [simp]:
     "\<lbrakk>xs:list(A); ys:list(B); x \<in> A; y \<in> B\<rbrakk> \<Longrightarrow>
      zip(Cons(x,xs), Cons(y, ys)) = Cons(\<langle>x,y\<rangle>, zip(xs, ys))"
apply (simp add: zip_def, auto)
apply (rule zip_aux_unique, auto)
apply (simp add: list_on_set_of_list [of _ B])
apply (blast intro: list_on_set_of_list list_mono [THEN subsetD])
done

lemma zip_type [rule_format]:
     "xs:list(A) \<Longrightarrow> \<forall>ys \<in> list(B). zip(xs, ys):list(A*B)"
apply (induct_tac "xs")
apply (simp (no_asm))
apply clarify
apply (erule_tac a = ys in list.cases, auto)
done
declare zip_type [simp,TC]

(* zip length *)
lemma length_zip [rule_format]:
     "xs:list(A) \<Longrightarrow> \<forall>ys \<in> list(B). length(zip(xs,ys)) =
                                     min(length(xs), length(ys))"
  unfolding min_def
apply (induct_tac "xs", simp_all, clarify)
apply (erule_tac a = ys in list.cases, auto)
done
declare length_zip [simp]

lemma zip_append1 [rule_format]:
 "\<lbrakk>ys:list(A); zs:list(B)\<rbrakk> \<Longrightarrow>
  \<forall>xs \<in> list(A). zip(xs @ ys, zs) =
                 zip(xs, take(length(xs), zs)) @ zip(ys, drop(length(xs),zs))"
apply (induct_tac "zs", force, clarify)
apply (erule_tac a = xs in list.cases, simp_all)
done

lemma zip_append2 [rule_format]:
 "\<lbrakk>xs:list(A); zs:list(B)\<rbrakk> \<Longrightarrow> \<forall>ys \<in> list(B). zip(xs, ys@zs) =
       zip(take(length(ys), xs), ys) @ zip(drop(length(ys), xs), zs)"
apply (induct_tac "xs", force, clarify)
apply (erule_tac a = ys in list.cases, auto)
done

lemma zip_append [simp]:
 "\<lbrakk>length(xs) = length(us); length(ys) = length(vs);
     xs:list(A); us:list(B); ys:list(A); vs:list(B)\<rbrakk>
  \<Longrightarrow> zip(xs@ys,us@vs) = zip(xs, us) @ zip(ys, vs)"
by (simp (no_asm_simp) add: zip_append1 drop_append diff_self_eq_0)


lemma zip_rev [rule_format]:
 "ys:list(B) \<Longrightarrow> \<forall>xs \<in> list(A).
    length(xs) = length(ys) \<longrightarrow> zip(rev(xs), rev(ys)) = rev(zip(xs, ys))"
apply (induct_tac "ys", force, clarify)
apply (erule_tac a = xs in list.cases)
apply (auto simp add: length_rev)
done
declare zip_rev [simp]

lemma nth_zip [rule_format]:
   "ys:list(B) \<Longrightarrow> \<forall>i \<in> nat. \<forall>xs \<in> list(A).
                    i < length(xs) \<longrightarrow> i < length(ys) \<longrightarrow>
                    nth(i,zip(xs, ys)) = <nth(i,xs),nth(i, ys)>"
apply (induct_tac "ys", force, clarify)
apply (erule_tac a = xs in list.cases, simp)
apply (auto elim: natE)
done
declare nth_zip [simp]

lemma set_of_list_zip [rule_format]:
     "\<lbrakk>xs:list(A); ys:list(B); i \<in> nat\<rbrakk>
      \<Longrightarrow> set_of_list(zip(xs, ys)) =
          {\<langle>x, y\<rangle>:A*B. \<exists>i\<in>nat. i < min(length(xs), length(ys))
          \<and> x = nth(i, xs) \<and> y = nth(i, ys)}"
by (force intro!: Collect_cong simp add: lt_min_iff set_of_list_conv_nth)

(** list_update **)

lemma list_update_Nil [simp]: "i \<in> nat \<Longrightarrow>list_update(Nil, i, v) = Nil"
by (unfold list_update_def, auto)

lemma list_update_Cons_0 [simp]: "list_update(Cons(x, xs), 0, v)= Cons(v, xs)"
by (unfold list_update_def, auto)

lemma list_update_Cons_succ [simp]:
  "n \<in> nat \<Longrightarrow>
    list_update(Cons(x, xs), succ(n), v)= Cons(x, list_update(xs, n, v))"
apply (unfold list_update_def, auto)
done

lemma list_update_type [rule_format]:
     "\<lbrakk>xs:list(A); v \<in> A\<rbrakk> \<Longrightarrow> \<forall>n \<in> nat. list_update(xs, n, v):list(A)"
apply (induct_tac "xs")
apply (simp (no_asm))
apply clarify
apply (erule natE, auto)
done
declare list_update_type [simp,TC]

lemma length_list_update [rule_format]:
     "xs:list(A) \<Longrightarrow> \<forall>i \<in> nat. length(list_update(xs, i, v))=length(xs)"
apply (induct_tac "xs")
apply (simp (no_asm))
apply clarify
apply (erule natE, auto)
done
declare length_list_update [simp]

lemma nth_list_update [rule_format]:
     "\<lbrakk>xs:list(A)\<rbrakk> \<Longrightarrow> \<forall>i \<in> nat. \<forall>j \<in> nat. i < length(xs)  \<longrightarrow>
         nth(j, list_update(xs, i, x)) = (if i=j then x else nth(j, xs))"
apply (induct_tac "xs")
 apply simp_all
apply clarify
apply (rename_tac i j)
apply (erule_tac n=i in natE)
apply (erule_tac [2] n=j in natE)
apply (erule_tac n=j in natE, simp_all, force)
done

lemma nth_list_update_eq [simp]:
     "\<lbrakk>i < length(xs); xs:list(A)\<rbrakk> \<Longrightarrow> nth(i, list_update(xs, i,x)) = x"
by (simp (no_asm_simp) add: lt_length_in_nat nth_list_update)


lemma nth_list_update_neq [rule_format]:
  "xs:list(A) \<Longrightarrow>
     \<forall>i \<in> nat. \<forall>j \<in> nat. i \<noteq> j \<longrightarrow> nth(j, list_update(xs,i,x)) = nth(j,xs)"
apply (induct_tac "xs")
 apply (simp (no_asm))
apply clarify
apply (erule natE)
apply (erule_tac [2] natE, simp_all)
apply (erule natE, simp_all)
done
declare nth_list_update_neq [simp]

lemma list_update_overwrite [rule_format]:
     "xs:list(A) \<Longrightarrow> \<forall>i \<in> nat. i < length(xs)
   \<longrightarrow> list_update(list_update(xs, i, x), i, y) = list_update(xs, i,y)"
apply (induct_tac "xs")
 apply (simp (no_asm))
apply clarify
apply (erule natE, auto)
done
declare list_update_overwrite [simp]

lemma list_update_same_conv [rule_format]:
     "xs:list(A) \<Longrightarrow>
      \<forall>i \<in> nat. i < length(xs) \<longrightarrow>
                 (list_update(xs, i, x) = xs) \<longleftrightarrow> (nth(i, xs) = x)"
apply (induct_tac "xs")
 apply (simp (no_asm))
apply clarify
apply (erule natE, auto)
done

lemma update_zip [rule_format]:
     "ys:list(B) \<Longrightarrow>
      \<forall>i \<in> nat. \<forall>xy \<in> A*B. \<forall>xs \<in> list(A).
        length(xs) = length(ys) \<longrightarrow>
        list_update(zip(xs, ys), i, xy) = zip(list_update(xs, i, fst(xy)),
                                              list_update(ys, i, snd(xy)))"
apply (induct_tac "ys")
 apply auto
apply (erule_tac a = xs in list.cases)
apply (auto elim: natE)
done

lemma set_update_subset_cons [rule_format]:
  "xs:list(A) \<Longrightarrow>
   \<forall>i \<in> nat. set_of_list(list_update(xs, i, x)) \<subseteq> cons(x, set_of_list(xs))"
apply (induct_tac "xs")
 apply simp
apply (rule ballI)
apply (erule natE, simp_all, auto)
done

lemma set_of_list_update_subsetI:
     "\<lbrakk>set_of_list(xs) \<subseteq> A; xs:list(A); x \<in> A; i \<in> nat\<rbrakk>
   \<Longrightarrow> set_of_list(list_update(xs, i,x)) \<subseteq> A"
apply (rule subset_trans)
apply (rule set_update_subset_cons, auto)
done

(** upt **)

lemma upt_rec:
     "j \<in> nat \<Longrightarrow> upt(i,j) = (if i<j then Cons(i, upt(succ(i), j)) else Nil)"
apply (induct_tac "j", auto)
apply (drule not_lt_imp_le)
apply (auto simp: lt_Ord intro: le_anti_sym)
done

lemma upt_conv_Nil [simp]: "\<lbrakk>j \<le> i; j \<in> nat\<rbrakk> \<Longrightarrow> upt(i,j) = Nil"
apply (subst upt_rec, auto)
apply (auto simp add: le_iff)
apply (drule lt_asym [THEN notE], auto)
done

(*Only needed if upt_Suc is deleted from the simpset*)
lemma upt_succ_append:
     "\<lbrakk>i \<le> j; j \<in> nat\<rbrakk> \<Longrightarrow> upt(i,succ(j)) = upt(i, j)@[j]"
by simp

lemma upt_conv_Cons:
     "\<lbrakk>i<j; j \<in> nat\<rbrakk>  \<Longrightarrow> upt(i,j) = Cons(i,upt(succ(i),j))"
apply (rule trans)
apply (rule upt_rec, auto)
done

lemma upt_type [simp,TC]: "j \<in> nat \<Longrightarrow> upt(i,j):list(nat)"
by (induct_tac "j", auto)

(*LOOPS as a simprule, since j<=j*)
lemma upt_add_eq_append:
     "\<lbrakk>i \<le> j; j \<in> nat; k \<in> nat\<rbrakk> \<Longrightarrow> upt(i, j #+k) = upt(i,j)@upt(j,j#+k)"
apply (induct_tac "k")
apply (auto simp add: app_assoc app_type)
apply (rule_tac j = j in le_trans, auto)
done

lemma length_upt [simp]: "\<lbrakk>i \<in> nat; j \<in> nat\<rbrakk> \<Longrightarrow>length(upt(i,j)) = j #- i"
apply (induct_tac "j")
apply (rule_tac [2] sym)
apply (auto dest!: not_lt_imp_le simp add: diff_succ diff_is_0_iff)
done

lemma nth_upt [simp]:
     "\<lbrakk>i \<in> nat; j \<in> nat; k \<in> nat; i #+ k < j\<rbrakk> \<Longrightarrow> nth(k, upt(i,j)) = i #+ k"
apply (rotate_tac -1, erule rev_mp)
apply (induct_tac "j", simp)
apply (auto dest!: not_lt_imp_le
            simp add: nth_append le_iff less_diff_conv add_commute)
done

lemma take_upt [rule_format]:
     "\<lbrakk>m \<in> nat; n \<in> nat\<rbrakk> \<Longrightarrow>
         \<forall>i \<in> nat. i #+ m \<le> n \<longrightarrow> take(m, upt(i,n)) = upt(i,i#+m)"
apply (induct_tac "m")
apply (simp (no_asm_simp) add: take_0)
apply clarify
apply (subst upt_rec, simp)
apply (rule sym)
apply (subst upt_rec, simp)
apply (simp_all del: upt.simps)
apply (rule_tac j = "succ (i #+ x) " in lt_trans2)
apply auto
done
declare take_upt [simp]

lemma map_succ_upt:
     "\<lbrakk>m \<in> nat; n \<in> nat\<rbrakk> \<Longrightarrow> map(succ, upt(m,n))= upt(succ(m), succ(n))"
apply (induct_tac "n")
apply (auto simp add: map_app_distrib)
done

lemma nth_map [rule_format]:
     "xs:list(A) \<Longrightarrow>
      \<forall>n \<in> nat. n < length(xs) \<longrightarrow> nth(n, map(f, xs)) = f(nth(n, xs))"
apply (induct_tac "xs", simp)
apply (rule ballI)
apply (induct_tac "n", auto)
done
declare nth_map [simp]

lemma nth_map_upt [rule_format]:
     "\<lbrakk>m \<in> nat; n \<in> nat\<rbrakk> \<Longrightarrow>
      \<forall>i \<in> nat. i < n #- m \<longrightarrow> nth(i, map(f, upt(m,n))) = f(m #+ i)"
apply (rule_tac n = m and m = n in diff_induct, typecheck, simp, simp)
apply (subst map_succ_upt [symmetric], simp_all, clarify)
apply (subgoal_tac "i < length (upt (0, x))")
 prefer 2
 apply (simp add: less_diff_conv)
 apply (rule_tac j = "succ (i #+ y) " in lt_trans2)
  apply simp
 apply simp
apply (subgoal_tac "i < length (upt (y, x))")
 apply (simp_all add: add_commute less_diff_conv)
done

(** sublist (a generalization of nth to sets) **)

definition
  sublist :: "[i, i] \<Rightarrow> i"  where
    "sublist(xs, A)\<equiv>
     map(fst, (filter(\<lambda>p. snd(p): A, zip(xs, upt(0,length(xs))))))"

lemma sublist_0 [simp]: "xs:list(A) \<Longrightarrow>sublist(xs, 0) =Nil"
by (unfold sublist_def, auto)

lemma sublist_Nil [simp]: "sublist(Nil, A) = Nil"
by (unfold sublist_def, auto)

lemma sublist_shift_lemma:
 "\<lbrakk>xs:list(B); i \<in> nat\<rbrakk> \<Longrightarrow>
  map(fst, filter(\<lambda>p. snd(p):A, zip(xs, upt(i,i #+ length(xs))))) =
  map(fst, filter(\<lambda>p. snd(p):nat \<and> snd(p) #+ i \<in> A, zip(xs,upt(0,length(xs)))))"
apply (erule list_append_induct)
apply (simp (no_asm_simp))
apply (auto simp add: add_commute length_app filter_append map_app_distrib)
done

lemma sublist_type [simp,TC]:
     "xs:list(B) \<Longrightarrow> sublist(xs, A):list(B)"
  unfolding sublist_def
apply (induct_tac "xs")
apply (auto simp add: filter_append map_app_distrib)
done

lemma upt_add_eq_append2:
     "\<lbrakk>i \<in> nat; j \<in> nat\<rbrakk> \<Longrightarrow> upt(0, i #+ j) = upt(0, i) @ upt(i, i #+ j)"
by (simp add: upt_add_eq_append [of 0] nat_0_le)

lemma sublist_append:
 "\<lbrakk>xs:list(B); ys:list(B)\<rbrakk> \<Longrightarrow>
  sublist(xs@ys, A) = sublist(xs, A) @ sublist(ys, {j \<in> nat. j #+ length(xs): A})"
  unfolding sublist_def
apply (erule_tac l = ys in list_append_induct, simp)
apply (simp (no_asm_simp) add: upt_add_eq_append2 app_assoc [symmetric])
apply (auto simp add: sublist_shift_lemma length_type map_app_distrib app_assoc)
apply (simp_all add: add_commute)
done


lemma sublist_Cons:
     "\<lbrakk>xs:list(B); x \<in> B\<rbrakk> \<Longrightarrow>
      sublist(Cons(x, xs), A) =
      (if 0 \<in> A then [x] else []) @ sublist(xs, {j \<in> nat. succ(j) \<in> A})"
apply (erule_tac l = xs in list_append_induct)
apply (simp (no_asm_simp) add: sublist_def)
apply (simp del: app_Cons add: app_Cons [symmetric] sublist_append, simp)
done

lemma sublist_singleton [simp]:
     "sublist([x], A) = (if 0 \<in> A then [x] else [])"
by (simp add: sublist_Cons)

lemma sublist_upt_eq_take [rule_format]:
    "xs:list(A) \<Longrightarrow> \<forall>n\<in>nat. sublist(xs,n) = take(n,xs)"
apply (erule list.induct, simp)
apply (clarify )
apply (erule natE)
apply (simp_all add: nat_eq_Collect_lt Ord_mem_iff_lt sublist_Cons)
done
declare sublist_upt_eq_take [simp]

lemma sublist_Int_eq:
     "xs \<in> list(B) \<Longrightarrow> sublist(xs, A \<inter> nat) = sublist(xs, A)"
apply (erule list.induct)
apply (simp_all add: sublist_Cons)
done

text\<open>Repetition of a List Element\<close>

consts   repeat :: "[i,i]\<Rightarrow>i"
primrec
  "repeat(a,0) = []"

  "repeat(a,succ(n)) = Cons(a,repeat(a,n))"

lemma length_repeat: "n \<in> nat \<Longrightarrow> length(repeat(a,n)) = n"
by (induct_tac n, auto)

lemma repeat_succ_app: "n \<in> nat \<Longrightarrow> repeat(a,succ(n)) = repeat(a,n) @ [a]"
apply (induct_tac n)
apply (simp_all del: app_Cons add: app_Cons [symmetric])
done

lemma repeat_type [TC]: "\<lbrakk>a \<in> A; n \<in> nat\<rbrakk> \<Longrightarrow> repeat(a,n) \<in> list(A)"
by (induct_tac n, auto)

end

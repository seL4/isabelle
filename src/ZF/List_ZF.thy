(*  Title:      ZF/List_ZF.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

header{*Lists in Zermelo-Fraenkel Set Theory*}

theory List_ZF imports Datatype_ZF ArithSimp begin

consts
  list       :: "i=>i"

datatype
  "list(A)" = Nil | Cons ("a:A", "l: list(A)")


syntax
 "_Nil" :: i  ("[]")
 "_List" :: "is => i"  ("[(_)]")

translations
  "[x, xs]"     == "CONST Cons(x, [xs])"
  "[x]"         == "CONST Cons(x, [])"
  "[]"          == "CONST Nil"


consts
  length :: "i=>i"
  hd     :: "i=>i"
  tl     :: "i=>i"

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
  map         :: "[i=>i, i] => i"
  set_of_list :: "i=>i"
  app         :: "[i,i]=>i"                        (infixr "@" 60)

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
  rev :: "i=>i"
  flat       :: "i=>i"
  list_add   :: "i=>i"

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
  drop       :: "[i,i]=>i"

primrec
  drop_0:    "drop(0,l) = l"
  drop_succ: "drop(succ(i), l) = tl (drop(i,l))"


(*** Thanks to Sidi Ehmety for the following ***)

definition
(* Function `take' returns the first n elements of a list *)
  take     :: "[i,i]=>i"  where
  "take(n, as) == list_rec(lam n:nat. [],
                %a l r. lam n:nat. nat_case([], %m. Cons(a, r`m), n), as)`n"

definition
  nth :: "[i, i]=>i"  where
  --{*returns the (n+1)th element of a list, or 0 if the
   list is too short.*}
  "nth(n, as) == list_rec(lam n:nat. 0,
                          %a l r. lam n:nat. nat_case(a, %m. r`m, n), as) ` n"

definition
  list_update :: "[i, i, i]=>i"  where
  "list_update(xs, i, v) == list_rec(lam n:nat. Nil,
      %u us vs. lam n:nat. nat_case(Cons(v, us), %m. Cons(u, vs`m), n), xs)`i"

consts
  filter :: "[i=>o, i] => i"
  upt :: "[i, i] =>i"

primrec
  "filter(P, Nil) = Nil"
  "filter(P, Cons(x, xs)) =
     (if P(x) then Cons(x, filter(P, xs)) else filter(P, xs))"

primrec
  "upt(i, 0) = Nil"
  "upt(i, succ(j)) = (if i le j then upt(i, j)@[j] else Nil)"

definition
  min :: "[i,i] =>i"  where
    "min(x, y) == (if x le y then x else y)"

definition
  max :: "[i, i] =>i"  where
    "max(x, y) == (if x le y then y else x)"

(*** Aspects of the datatype definition ***)

declare list.intros [simp,TC]

(*An elimination rule, for type-checking*)
inductive_cases ConsE: "Cons(a,l) : list(A)"

lemma Cons_type_iff [simp]: "Cons(a,l) \<in> list(A) <-> a \<in> A & l \<in> list(A)"
by (blast elim: ConsE) 

(*Proving freeness results*)
lemma Cons_iff: "Cons(a,l)=Cons(a',l') <-> a=a' & l=l'"
by auto

lemma Nil_Cons_iff: "~ Nil=Cons(a,l)"
by auto

lemma list_unfold: "list(A) = {0} + (A * list(A))"
by (blast intro!: list.intros [unfolded list.con_defs]
          elim: list.cases [unfolded list.con_defs])


(**  Lemmas to justify using "list" in other recursive type definitions **)

lemma list_mono: "A<=B ==> list(A) <= list(B)"
apply (unfold list.defs )
apply (rule lfp_mono)
apply (simp_all add: list.bnd_mono)
apply (assumption | rule univ_mono basic_monos)+
done

(*There is a similar proof by list induction.*)
lemma list_univ: "list(univ(A)) <= univ(A)"
apply (unfold list.defs list.con_defs)
apply (rule lfp_lowerbound)
apply (rule_tac [2] A_subset_univ [THEN univ_mono])
apply (blast intro!: zero_in_univ Inl_in_univ Inr_in_univ Pair_in_univ)
done

(*These two theorems justify datatypes involving list(nat), list(A), ...*)
lemmas list_subset_univ = subset_trans [OF list_mono list_univ]

lemma list_into_univ: "[| l: list(A);  A <= univ(B) |] ==> l: univ(B)"
by (blast intro: list_subset_univ [THEN subsetD])

lemma list_case_type:
    "[| l: list(A);
        c: C(Nil);
        !!x y. [| x: A;  y: list(A) |] ==> h(x,y): C(Cons(x,y))
     |] ==> list_case(c,h,l) : C(l)"
by (erule list.induct, auto)

lemma list_0_triv: "list(0) = {Nil}"
apply (rule equalityI, auto) 
apply (induct_tac x, auto) 
done


(*** List functions ***)

lemma tl_type: "l: list(A) ==> tl(l) : list(A)"
apply (induct_tac "l")
apply (simp_all (no_asm_simp) add: list.intros)
done

(** drop **)

lemma drop_Nil [simp]: "i:nat ==> drop(i, Nil) = Nil"
apply (induct_tac "i")
apply (simp_all (no_asm_simp))
done

lemma drop_succ_Cons [simp]: "i:nat ==> drop(succ(i), Cons(a,l)) = drop(i,l)"
apply (rule sym)
apply (induct_tac "i")
apply (simp (no_asm))
apply (simp (no_asm_simp))
done

lemma drop_type [simp,TC]: "[| i:nat; l: list(A) |] ==> drop(i,l) : list(A)"
apply (induct_tac "i")
apply (simp_all (no_asm_simp) add: tl_type)
done

declare drop_succ [simp del]


(** Type checking -- proved by induction, as usual **)

lemma list_rec_type [TC]:
    "[| l: list(A);
        c: C(Nil);
        !!x y r. [| x:A;  y: list(A);  r: C(y) |] ==> h(x,y,r): C(Cons(x,y))
     |] ==> list_rec(c,h,l) : C(l)"
by (induct_tac "l", auto)

(** map **)

lemma map_type [TC]:
    "[| l: list(A);  !!x. x: A ==> h(x): B |] ==> map(h,l) : list(B)"
apply (simp add: map_list_def)
apply (typecheck add: list.intros list_rec_type, blast)
done

lemma map_type2 [TC]: "l: list(A) ==> map(h,l) : list({h(u). u:A})"
apply (erule map_type)
apply (erule RepFunI)
done

(** length **)

lemma length_type [TC]: "l: list(A) ==> length(l) : nat"
by (simp add: length_list_def)

lemma lt_length_in_nat:
   "[|x < length(xs); xs \<in> list(A)|] ==> x \<in> nat"
by (frule lt_nat_in_nat, typecheck) 

(** app **)

lemma app_type [TC]: "[| xs: list(A);  ys: list(A) |] ==> xs@ys : list(A)"
by (simp add: app_list_def)

(** rev **)

lemma rev_type [TC]: "xs: list(A) ==> rev(xs) : list(A)"
by (simp add: rev_list_def)


(** flat **)

lemma flat_type [TC]: "ls: list(list(A)) ==> flat(ls) : list(A)"
by (simp add: flat_list_def)


(** set_of_list **)

lemma set_of_list_type [TC]: "l: list(A) ==> set_of_list(l) : Pow(A)"
apply (unfold set_of_list_list_def)
apply (erule list_rec_type, auto)
done

lemma set_of_list_append:
     "xs: list(A) ==> set_of_list (xs@ys) = set_of_list(xs) Un set_of_list(ys)"
apply (erule list.induct)
apply (simp_all (no_asm_simp) add: Un_cons)
done


(** list_add **)

lemma list_add_type [TC]: "xs: list(nat) ==> list_add(xs) : nat"
by (simp add: list_add_list_def)


(*** theorems about map ***)

lemma map_ident [simp]: "l: list(A) ==> map(%u. u, l) = l"
apply (induct_tac "l")
apply (simp_all (no_asm_simp))
done

lemma map_compose: "l: list(A) ==> map(h, map(j,l)) = map(%u. h(j(u)), l)"
apply (induct_tac "l")
apply (simp_all (no_asm_simp))
done

lemma map_app_distrib: "xs: list(A) ==> map(h, xs@ys) = map(h,xs) @ map(h,ys)"
apply (induct_tac "xs")
apply (simp_all (no_asm_simp))
done

lemma map_flat: "ls: list(list(A)) ==> map(h, flat(ls)) = flat(map(map(h),ls))"
apply (induct_tac "ls")
apply (simp_all (no_asm_simp) add: map_app_distrib)
done

lemma list_rec_map:
     "l: list(A) ==>
      list_rec(c, d, map(h,l)) =
      list_rec(c, %x xs r. d(h(x), map(h,xs), r), l)"
apply (induct_tac "l")
apply (simp_all (no_asm_simp))
done

(** theorems about list(Collect(A,P)) -- used in Induct/Term.thy **)

(* c : list(Collect(B,P)) ==> c : list(B) *)
lemmas list_CollectD = Collect_subset [THEN list_mono, THEN subsetD]

lemma map_list_Collect: "l: list({x:A. h(x)=j(x)}) ==> map(h,l) = map(j,l)"
apply (induct_tac "l")
apply (simp_all (no_asm_simp))
done

(*** theorems about length ***)

lemma length_map [simp]: "xs: list(A) ==> length(map(h,xs)) = length(xs)"
by (induct_tac "xs", simp_all)

lemma length_app [simp]:
     "[| xs: list(A); ys: list(A) |]
      ==> length(xs@ys) = length(xs) #+ length(ys)"
by (induct_tac "xs", simp_all)

lemma length_rev [simp]: "xs: list(A) ==> length(rev(xs)) = length(xs)"
apply (induct_tac "xs")
apply (simp_all (no_asm_simp) add: length_app)
done

lemma length_flat:
     "ls: list(list(A)) ==> length(flat(ls)) = list_add(map(length,ls))"
apply (induct_tac "ls")
apply (simp_all (no_asm_simp) add: length_app)
done

(** Length and drop **)

(*Lemma for the inductive step of drop_length*)
lemma drop_length_Cons [rule_format]:
     "xs: list(A) ==>
           \<forall>x.  EX z zs. drop(length(xs), Cons(x,xs)) = Cons(z,zs)"
by (erule list.induct, simp_all)

lemma drop_length [rule_format]:
     "l: list(A) ==> \<forall>i \<in> length(l). (EX z zs. drop(i,l) = Cons(z,zs))"
apply (erule list.induct, simp_all, safe)
apply (erule drop_length_Cons)
apply (rule natE)
apply (erule Ord_trans [OF asm_rl length_type Ord_nat], assumption, simp_all)
apply (blast intro: succ_in_naturalD length_type)
done


(*** theorems about app ***)

lemma app_right_Nil [simp]: "xs: list(A) ==> xs@Nil=xs"
by (erule list.induct, simp_all)

lemma app_assoc: "xs: list(A) ==> (xs@ys)@zs = xs@(ys@zs)"
by (induct_tac "xs", simp_all)

lemma flat_app_distrib: "ls: list(list(A)) ==> flat(ls@ms) = flat(ls)@flat(ms)"
apply (induct_tac "ls")
apply (simp_all (no_asm_simp) add: app_assoc)
done

(*** theorems about rev ***)

lemma rev_map_distrib: "l: list(A) ==> rev(map(h,l)) = map(h,rev(l))"
apply (induct_tac "l")
apply (simp_all (no_asm_simp) add: map_app_distrib)
done

(*Simplifier needs the premises as assumptions because rewriting will not
  instantiate the variable ?A in the rules' typing conditions; note that
  rev_type does not instantiate ?A.  Only the premises do.
*)
lemma rev_app_distrib:
     "[| xs: list(A);  ys: list(A) |] ==> rev(xs@ys) = rev(ys)@rev(xs)"
apply (erule list.induct)
apply (simp_all add: app_assoc)
done

lemma rev_rev_ident [simp]: "l: list(A) ==> rev(rev(l))=l"
apply (induct_tac "l")
apply (simp_all (no_asm_simp) add: rev_app_distrib)
done

lemma rev_flat: "ls: list(list(A)) ==> rev(flat(ls)) = flat(map(rev,rev(ls)))"
apply (induct_tac "ls")
apply (simp_all add: map_app_distrib flat_app_distrib rev_app_distrib)
done


(*** theorems about list_add ***)

lemma list_add_app:
     "[| xs: list(nat);  ys: list(nat) |]
      ==> list_add(xs@ys) = list_add(ys) #+ list_add(xs)"
apply (induct_tac "xs", simp_all)
done

lemma list_add_rev: "l: list(nat) ==> list_add(rev(l)) = list_add(l)"
apply (induct_tac "l")
apply (simp_all (no_asm_simp) add: list_add_app)
done

lemma list_add_flat:
     "ls: list(list(nat)) ==> list_add(flat(ls)) = list_add(map(list_add,ls))"
apply (induct_tac "ls")
apply (simp_all (no_asm_simp) add: list_add_app)
done

(** New induction rules **)

lemma list_append_induct [case_names Nil snoc, consumes 1]:
    "[| l: list(A);
        P(Nil);
        !!x y. [| x: A;  y: list(A);  P(y) |] ==> P(y @ [x])
     |] ==> P(l)"
apply (subgoal_tac "P(rev(rev(l)))", simp)
apply (erule rev_type [THEN list.induct], simp_all)
done

lemma list_complete_induct_lemma [rule_format]:
 assumes ih: 
    "\<And>l. [| l \<in> list(A); 
             \<forall>l' \<in> list(A). length(l') < length(l) --> P(l')|] 
          ==> P(l)"
  shows "n \<in> nat ==> \<forall>l \<in> list(A). length(l) < n --> P(l)"
apply (induct_tac n, simp)
apply (blast intro: ih elim!: leE) 
done

theorem list_complete_induct:
      "[| l \<in> list(A); 
          \<And>l. [| l \<in> list(A); 
                  \<forall>l' \<in> list(A). length(l') < length(l) --> P(l')|] 
               ==> P(l)
       |] ==> P(l)"
apply (rule list_complete_induct_lemma [of A]) 
   prefer 4 apply (rule le_refl, simp) 
  apply blast 
 apply simp 
apply assumption
done


(*** Thanks to Sidi Ehmety for these results about min, take, etc. ***)

(** min FIXME: replace by Int! **)
(* Min theorems are also true for i, j ordinals *)
lemma min_sym: "[| i:nat; j:nat |] ==> min(i,j)=min(j,i)"
apply (unfold min_def)
apply (auto dest!: not_lt_imp_le dest: lt_not_sym intro: le_anti_sym)
done

lemma min_type [simp,TC]: "[| i:nat; j:nat |] ==> min(i,j):nat"
by (unfold min_def, auto)

lemma min_0 [simp]: "i:nat ==> min(0,i) = 0"
apply (unfold min_def)
apply (auto dest: not_lt_imp_le)
done

lemma min_02 [simp]: "i:nat ==> min(i, 0) = 0"
apply (unfold min_def)
apply (auto dest: not_lt_imp_le)
done

lemma lt_min_iff: "[| i:nat; j:nat; k:nat |] ==> i<min(j,k) <-> i<j & i<k"
apply (unfold min_def)
apply (auto dest!: not_lt_imp_le intro: lt_trans2 lt_trans)
done

lemma min_succ_succ [simp]:
     "[| i:nat; j:nat |] ==>  min(succ(i), succ(j))= succ(min(i, j))"
apply (unfold min_def, auto)
done

(*** more theorems about lists ***)

(** filter **)

lemma filter_append [simp]:
     "xs:list(A) ==> filter(P, xs@ys) = filter(P, xs) @ filter(P, ys)"
by (induct_tac "xs", auto)

lemma filter_type [simp,TC]: "xs:list(A) ==> filter(P, xs):list(A)"
by (induct_tac "xs", auto)

lemma length_filter: "xs:list(A) ==> length(filter(P, xs)) le length(xs)"
apply (induct_tac "xs", auto)
apply (rule_tac j = "length (l) " in le_trans)
apply (auto simp add: le_iff)
done

lemma filter_is_subset: "xs:list(A) ==> set_of_list(filter(P,xs)) <= set_of_list(xs)"
by (induct_tac "xs", auto)

lemma filter_False [simp]: "xs:list(A) ==> filter(%p. False, xs) = Nil"
by (induct_tac "xs", auto)

lemma filter_True [simp]: "xs:list(A) ==> filter(%p. True, xs) = xs"
by (induct_tac "xs", auto)

(** length **)

lemma length_is_0_iff [simp]: "xs:list(A) ==> length(xs)=0 <-> xs=Nil"
by (erule list.induct, auto)

lemma length_is_0_iff2 [simp]: "xs:list(A) ==> 0 = length(xs) <-> xs=Nil"
by (erule list.induct, auto)

lemma length_tl [simp]: "xs:list(A) ==> length(tl(xs)) = length(xs) #- 1"
by (erule list.induct, auto)

lemma length_greater_0_iff: "xs:list(A) ==> 0<length(xs) <-> xs ~= Nil"
by (erule list.induct, auto)

lemma length_succ_iff: "xs:list(A) ==> length(xs)=succ(n) <-> (EX y ys. xs=Cons(y, ys) & length(ys)=n)"
by (erule list.induct, auto)

(** more theorems about append **)

lemma append_is_Nil_iff [simp]:
     "xs:list(A) ==> (xs@ys = Nil) <-> (xs=Nil & ys = Nil)"
by (erule list.induct, auto)

lemma append_is_Nil_iff2 [simp]:
     "xs:list(A) ==> (Nil = xs@ys) <-> (xs=Nil & ys = Nil)"
by (erule list.induct, auto)

lemma append_left_is_self_iff [simp]:
     "xs:list(A) ==> (xs@ys = xs) <-> (ys = Nil)"
by (erule list.induct, auto)

lemma append_left_is_self_iff2 [simp]:
     "xs:list(A) ==> (xs = xs@ys) <-> (ys = Nil)"
by (erule list.induct, auto)

(*TOO SLOW as a default simprule!*)
lemma append_left_is_Nil_iff [rule_format]:
     "[| xs:list(A); ys:list(A); zs:list(A) |] ==>
   length(ys)=length(zs) --> (xs@ys=zs <-> (xs=Nil & ys=zs))"
apply (erule list.induct)
apply (auto simp add: length_app)
done

(*TOO SLOW as a default simprule!*)
lemma append_left_is_Nil_iff2 [rule_format]:
     "[| xs:list(A); ys:list(A); zs:list(A) |] ==>
   length(ys)=length(zs) --> (zs=ys@xs <-> (xs=Nil & ys=zs))"
apply (erule list.induct)
apply (auto simp add: length_app)
done

lemma append_eq_append_iff [rule_format,simp]:
     "xs:list(A) ==> \<forall>ys \<in> list(A).
      length(xs)=length(ys) --> (xs@us = ys@vs) <-> (xs=ys & us=vs)"
apply (erule list.induct)
apply (simp (no_asm_simp))
apply clarify
apply (erule_tac a = ys in list.cases, auto)
done

lemma append_eq_append [rule_format]:
  "xs:list(A) ==>
   \<forall>ys \<in> list(A). \<forall>us \<in> list(A). \<forall>vs \<in> list(A).
   length(us) = length(vs) --> (xs@us = ys@vs) --> (xs=ys & us=vs)"
apply (induct_tac "xs")
apply (force simp add: length_app, clarify)
apply (erule_tac a = ys in list.cases, simp)
apply (subgoal_tac "Cons (a, l) @ us =vs")
 apply (drule rev_iffD1 [OF _ append_left_is_Nil_iff], simp_all, blast)
done

lemma append_eq_append_iff2 [simp]:
 "[| xs:list(A); ys:list(A); us:list(A); vs:list(A); length(us)=length(vs) |]
  ==>  xs@us = ys@vs <-> (xs=ys & us=vs)"
apply (rule iffI)
apply (rule append_eq_append, auto)
done

lemma append_self_iff [simp]:
     "[| xs:list(A); ys:list(A); zs:list(A) |] ==> xs@ys=xs@zs <-> ys=zs"
by simp

lemma append_self_iff2 [simp]:
     "[| xs:list(A); ys:list(A); zs:list(A) |] ==> ys@xs=zs@xs <-> ys=zs"
by simp

(* Can also be proved from append_eq_append_iff2,
but the proof requires two more hypotheses: x:A and y:A *)
lemma append1_eq_iff [rule_format,simp]:
     "xs:list(A) ==> \<forall>ys \<in> list(A). xs@[x] = ys@[y] <-> (xs = ys & x=y)"
apply (erule list.induct)  
 apply clarify 
 apply (erule list.cases)
 apply simp_all
txt{*Inductive step*}  
apply clarify 
apply (erule_tac a=ys in list.cases, simp_all)  
done


lemma append_right_is_self_iff [simp]:
     "[| xs:list(A); ys:list(A) |] ==> (xs@ys = ys) <-> (xs=Nil)"
by (simp (no_asm_simp) add: append_left_is_Nil_iff)

lemma append_right_is_self_iff2 [simp]:
     "[| xs:list(A); ys:list(A) |] ==> (ys = xs@ys) <-> (xs=Nil)"
apply (rule iffI)
apply (drule sym, auto) 
done

lemma hd_append [rule_format,simp]:
     "xs:list(A) ==> xs ~= Nil --> hd(xs @ ys) = hd(xs)"
by (induct_tac "xs", auto)

lemma tl_append [rule_format,simp]:
     "xs:list(A) ==> xs~=Nil --> tl(xs @ ys) = tl(xs)@ys"
by (induct_tac "xs", auto)

(** rev **)
lemma rev_is_Nil_iff [simp]: "xs:list(A) ==> (rev(xs) = Nil <-> xs = Nil)"
by (erule list.induct, auto)

lemma Nil_is_rev_iff [simp]: "xs:list(A) ==> (Nil = rev(xs) <-> xs = Nil)"
by (erule list.induct, auto)

lemma rev_is_rev_iff [rule_format,simp]:
     "xs:list(A) ==> \<forall>ys \<in> list(A). rev(xs)=rev(ys) <-> xs=ys"
apply (erule list.induct, force, clarify)
apply (erule_tac a = ys in list.cases, auto)
done

lemma rev_list_elim [rule_format]:
     "xs:list(A) ==>
      (xs=Nil --> P) --> (\<forall>ys \<in> list(A). \<forall>y \<in> A. xs =ys@[y] -->P)-->P"
by (erule list_append_induct, auto)


(** more theorems about drop **)

lemma length_drop [rule_format,simp]:
     "n:nat ==> \<forall>xs \<in> list(A). length(drop(n, xs)) = length(xs) #- n"
apply (erule nat_induct)
apply (auto elim: list.cases)
done

lemma drop_all [rule_format,simp]:
     "n:nat ==> \<forall>xs \<in> list(A). length(xs) le n --> drop(n, xs)=Nil"
apply (erule nat_induct)
apply (auto elim: list.cases)
done

lemma drop_append [rule_format]:
     "n:nat ==> 
      \<forall>xs \<in> list(A). drop(n, xs@ys) = drop(n,xs) @ drop(n #- length(xs), ys)"
apply (induct_tac "n")
apply (auto elim: list.cases)
done

lemma drop_drop:
    "m:nat ==> \<forall>xs \<in> list(A). \<forall>n \<in> nat. drop(n, drop(m, xs))=drop(n #+ m, xs)"
apply (induct_tac "m")
apply (auto elim: list.cases)
done

(** take **)

lemma take_0 [simp]: "xs:list(A) ==> take(0, xs) =  Nil"
apply (unfold take_def)
apply (erule list.induct, auto)
done

lemma take_succ_Cons [simp]:
    "n:nat ==> take(succ(n), Cons(a, xs)) = Cons(a, take(n, xs))"
by (simp add: take_def)

(* Needed for proving take_all *)
lemma take_Nil [simp]: "n:nat ==> take(n, Nil) = Nil"
by (unfold take_def, auto)

lemma take_all [rule_format,simp]:
     "n:nat ==> \<forall>xs \<in> list(A). length(xs) le n  --> take(n, xs) = xs"
apply (erule nat_induct)
apply (auto elim: list.cases) 
done

lemma take_type [rule_format,simp,TC]:
     "xs:list(A) ==> \<forall>n \<in> nat. take(n, xs):list(A)"
apply (erule list.induct, simp, clarify) 
apply (erule natE, auto)
done

lemma take_append [rule_format,simp]:
 "xs:list(A) ==>
  \<forall>ys \<in> list(A). \<forall>n \<in> nat. take(n, xs @ ys) =
                            take(n, xs) @ take(n #- length(xs), ys)"
apply (erule list.induct, simp, clarify) 
apply (erule natE, auto)
done

lemma take_take [rule_format]:
   "m : nat ==>
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

lemma nth_Cons [simp]: "n:nat ==> nth(succ(n), Cons(a,l)) = nth(n,l)"
by (simp add: nth_def) 

lemma nth_empty [simp]: "nth(n, Nil) = 0"
by (simp add: nth_def) 

lemma nth_type [rule_format,simp,TC]:
     "xs:list(A) ==> \<forall>n. n < length(xs) --> nth(n,xs) : A"
apply (erule list.induct, simp, clarify)
apply (subgoal_tac "n \<in> nat")  
 apply (erule natE, auto dest!: le_in_nat)
done

lemma nth_eq_0 [rule_format]:
     "xs:list(A) ==> \<forall>n \<in> nat. length(xs) le n --> nth(n,xs) = 0"
apply (erule list.induct, simp, clarify) 
apply (erule natE, auto)
done

lemma nth_append [rule_format]:
  "xs:list(A) ==> 
   \<forall>n \<in> nat. nth(n, xs @ ys) = (if n < length(xs) then nth(n,xs)
                                else nth(n #- length(xs), ys))"
apply (induct_tac "xs", simp, clarify) 
apply (erule natE, auto)
done

lemma set_of_list_conv_nth:
    "xs:list(A)
     ==> set_of_list(xs) = {x:A. EX i:nat. i<length(xs) & x = nth(i,xs)}"
apply (induct_tac "xs", simp_all)
apply (rule equalityI, auto)
apply (rule_tac x = 0 in bexI, auto)
apply (erule natE, auto)
done

(* Other theorems about lists *)

lemma nth_take_lemma [rule_format]:
 "k:nat ==>
  \<forall>xs \<in> list(A). (\<forall>ys \<in> list(A). k le length(xs) --> k le length(ys) -->
      (\<forall>i \<in> nat. i<k --> nth(i,xs) = nth(i,ys))--> take(k,xs) = take(k,ys))"
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
     "[| xs:list(A); ys:list(A); length(xs) = length(ys);
         \<forall>i \<in> nat. i < length(xs) --> nth(i,xs) = nth(i,ys) |]
      ==> xs = ys"
apply (subgoal_tac "length (xs) le length (ys) ")
apply (cut_tac k="length(xs)" and xs=xs and ys=ys in nth_take_lemma) 
apply (simp_all add: take_all)
done

(*The famous take-lemma*)

lemma take_equalityI [rule_format]:
    "[| xs:list(A); ys:list(A); (\<forall>i \<in> nat. take(i, xs) = take(i,ys)) |] 
     ==> xs = ys"
apply (case_tac "length (xs) le length (ys) ")
apply (drule_tac x = "length (ys) " in bspec)
apply (drule_tac [3] not_lt_imp_le)
apply (subgoal_tac [5] "length (ys) le length (xs) ")
apply (rule_tac [6] j = "succ (length (ys))" in le_trans)
apply (rule_tac [6] leI)
apply (drule_tac [5] x = "length (xs) " in bspec)
apply (simp_all add: take_all)
done

lemma nth_drop [rule_format]:
  "n:nat ==> \<forall>i \<in> nat. \<forall>xs \<in> list(A). nth(i, drop(n, xs)) = nth(n #+ i, xs)"
apply (induct_tac "n", simp_all, clarify)
apply (erule list.cases, auto)  
done

lemma take_succ [rule_format]:
  "xs\<in>list(A) 
   ==> \<forall>i. i < length(xs) --> take(succ(i), xs) = take(i,xs) @ [nth(i, xs)]"
apply (induct_tac "xs", auto)
apply (subgoal_tac "i\<in>nat") 
apply (erule natE)
apply (auto simp add: le_in_nat) 
done

lemma take_add [rule_format]:
     "[|xs\<in>list(A); j\<in>nat|] 
      ==> \<forall>i\<in>nat. take(i #+ j, xs) = take(i,xs) @ take(j, drop(i,xs))"
apply (induct_tac "xs", simp_all, clarify)
apply (erule_tac n = i in natE, simp_all)
done

lemma length_take:
     "l\<in>list(A) ==> \<forall>n\<in>nat. length(take(n,l)) = min(n, length(l))"
apply (induct_tac "l", safe, simp_all)
apply (erule natE, simp_all)
done

subsection{*The function zip*}

text{*Crafty definition to eliminate a type argument*}

consts
  zip_aux        :: "[i,i]=>i"

primrec (*explicit lambda is required because both arguments of "un" vary*)
  "zip_aux(B,[]) =
     (\<lambda>ys \<in> list(B). list_case([], %y l. [], ys))"

  "zip_aux(B,Cons(x,l)) =
     (\<lambda>ys \<in> list(B).
        list_case(Nil, %y zs. Cons(<x,y>, zip_aux(B,l)`zs), ys))"

definition
  zip :: "[i, i]=>i"  where
   "zip(xs, ys) == zip_aux(set_of_list(ys),xs)`ys"


(* zip equations *)

lemma list_on_set_of_list: "xs \<in> list(A) ==> xs \<in> list(set_of_list(xs))"
apply (induct_tac xs, simp_all) 
apply (blast intro: list_mono [THEN subsetD]) 
done

lemma zip_Nil [simp]: "ys:list(A) ==> zip(Nil, ys)=Nil"
apply (simp add: zip_def list_on_set_of_list [of _ A])
apply (erule list.cases, simp_all) 
done

lemma zip_Nil2 [simp]: "xs:list(A) ==> zip(xs, Nil)=Nil"
apply (simp add: zip_def list_on_set_of_list [of _ A])
apply (erule list.cases, simp_all) 
done

lemma zip_aux_unique [rule_format]:
     "[|B<=C;  xs \<in> list(A)|] 
      ==> \<forall>ys \<in> list(B). zip_aux(C,xs) ` ys = zip_aux(B,xs) ` ys"
apply (induct_tac xs) 
 apply simp_all 
 apply (blast intro: list_mono [THEN subsetD], clarify) 
apply (erule_tac a=ys in list.cases, auto) 
apply (blast intro: list_mono [THEN subsetD]) 
done

lemma zip_Cons_Cons [simp]:
     "[| xs:list(A); ys:list(B); x:A; y:B |] ==>
      zip(Cons(x,xs), Cons(y, ys)) = Cons(<x,y>, zip(xs, ys))"
apply (simp add: zip_def, auto) 
apply (rule zip_aux_unique, auto) 
apply (simp add: list_on_set_of_list [of _ B])
apply (blast intro: list_on_set_of_list list_mono [THEN subsetD]) 
done

lemma zip_type [rule_format,simp,TC]:
     "xs:list(A) ==> \<forall>ys \<in> list(B). zip(xs, ys):list(A*B)"
apply (induct_tac "xs")
apply (simp (no_asm))
apply clarify
apply (erule_tac a = ys in list.cases, auto)
done

(* zip length *)
lemma length_zip [rule_format,simp]:
     "xs:list(A) ==> \<forall>ys \<in> list(B). length(zip(xs,ys)) =
                                     min(length(xs), length(ys))"
apply (unfold min_def)
apply (induct_tac "xs", simp_all, clarify) 
apply (erule_tac a = ys in list.cases, auto)
done

lemma zip_append1 [rule_format]:
 "[| ys:list(A); zs:list(B) |] ==>
  \<forall>xs \<in> list(A). zip(xs @ ys, zs) = 
                 zip(xs, take(length(xs), zs)) @ zip(ys, drop(length(xs),zs))"
apply (induct_tac "zs", force, clarify) 
apply (erule_tac a = xs in list.cases, simp_all) 
done

lemma zip_append2 [rule_format]:
 "[| xs:list(A); zs:list(B) |] ==> \<forall>ys \<in> list(B). zip(xs, ys@zs) =
       zip(take(length(ys), xs), ys) @ zip(drop(length(ys), xs), zs)"
apply (induct_tac "xs", force, clarify) 
apply (erule_tac a = ys in list.cases, auto)
done

lemma zip_append [simp]:
 "[| length(xs) = length(us); length(ys) = length(vs);
     xs:list(A); us:list(B); ys:list(A); vs:list(B) |] 
  ==> zip(xs@ys,us@vs) = zip(xs, us) @ zip(ys, vs)"
by (simp (no_asm_simp) add: zip_append1 drop_append diff_self_eq_0)


lemma zip_rev [rule_format,simp]:
 "ys:list(B) ==> \<forall>xs \<in> list(A).
    length(xs) = length(ys) --> zip(rev(xs), rev(ys)) = rev(zip(xs, ys))"
apply (induct_tac "ys", force, clarify) 
apply (erule_tac a = xs in list.cases)
apply (auto simp add: length_rev)
done

lemma nth_zip [rule_format,simp]:
   "ys:list(B) ==> \<forall>i \<in> nat. \<forall>xs \<in> list(A).
                    i < length(xs) --> i < length(ys) -->
                    nth(i,zip(xs, ys)) = <nth(i,xs),nth(i, ys)>"
apply (induct_tac "ys", force, clarify) 
apply (erule_tac a = xs in list.cases, simp) 
apply (auto elim: natE)
done

lemma set_of_list_zip [rule_format]:
     "[| xs:list(A); ys:list(B); i:nat |]
      ==> set_of_list(zip(xs, ys)) =
          {<x, y>:A*B. EX i:nat. i < min(length(xs), length(ys))
          & x = nth(i, xs) & y = nth(i, ys)}"
by (force intro!: Collect_cong simp add: lt_min_iff set_of_list_conv_nth)

(** list_update **)

lemma list_update_Nil [simp]: "i:nat ==>list_update(Nil, i, v) = Nil"
by (unfold list_update_def, auto)

lemma list_update_Cons_0 [simp]: "list_update(Cons(x, xs), 0, v)= Cons(v, xs)"
by (unfold list_update_def, auto)

lemma list_update_Cons_succ [simp]:
  "n:nat ==>
    list_update(Cons(x, xs), succ(n), v)= Cons(x, list_update(xs, n, v))"
apply (unfold list_update_def, auto)
done

lemma list_update_type [rule_format,simp,TC]:
     "[| xs:list(A); v:A |] ==> \<forall>n \<in> nat. list_update(xs, n, v):list(A)"
apply (induct_tac "xs")
apply (simp (no_asm))
apply clarify
apply (erule natE, auto)
done

lemma length_list_update [rule_format,simp]:
     "xs:list(A) ==> \<forall>i \<in> nat. length(list_update(xs, i, v))=length(xs)"
apply (induct_tac "xs")
apply (simp (no_asm))
apply clarify
apply (erule natE, auto)
done

lemma nth_list_update [rule_format]:
     "[| xs:list(A) |] ==> \<forall>i \<in> nat. \<forall>j \<in> nat. i < length(xs)  -->
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
     "[| i < length(xs); xs:list(A) |] ==> nth(i, list_update(xs, i,x)) = x"
by (simp (no_asm_simp) add: lt_length_in_nat nth_list_update)


lemma nth_list_update_neq [rule_format,simp]:
  "xs:list(A) ==> 
     \<forall>i \<in> nat. \<forall>j \<in> nat. i ~= j --> nth(j, list_update(xs,i,x)) = nth(j,xs)"
apply (induct_tac "xs")
 apply (simp (no_asm))
apply clarify
apply (erule natE)
apply (erule_tac [2] natE, simp_all) 
apply (erule natE, simp_all)
done

lemma list_update_overwrite [rule_format,simp]:
     "xs:list(A) ==> \<forall>i \<in> nat. i < length(xs)
   --> list_update(list_update(xs, i, x), i, y) = list_update(xs, i,y)"
apply (induct_tac "xs")
 apply (simp (no_asm))
apply clarify
apply (erule natE, auto)
done

lemma list_update_same_conv [rule_format]:
     "xs:list(A) ==> 
      \<forall>i \<in> nat. i < length(xs) --> 
                 (list_update(xs, i, x) = xs) <-> (nth(i, xs) = x)"
apply (induct_tac "xs")
 apply (simp (no_asm))
apply clarify
apply (erule natE, auto)
done

lemma update_zip [rule_format]:
     "ys:list(B) ==> 
      \<forall>i \<in> nat. \<forall>xy \<in> A*B. \<forall>xs \<in> list(A).
        length(xs) = length(ys) -->
        list_update(zip(xs, ys), i, xy) = zip(list_update(xs, i, fst(xy)),
                                              list_update(ys, i, snd(xy)))"
apply (induct_tac "ys")
 apply auto
apply (erule_tac a = xs in list.cases)
apply (auto elim: natE)
done

lemma set_update_subset_cons [rule_format]:
  "xs:list(A) ==> 
   \<forall>i \<in> nat. set_of_list(list_update(xs, i, x)) <= cons(x, set_of_list(xs))"
apply (induct_tac "xs")
 apply simp
apply (rule ballI)
apply (erule natE, simp_all, auto)
done

lemma set_of_list_update_subsetI:
     "[| set_of_list(xs) <= A; xs:list(A); x:A; i:nat|]
   ==> set_of_list(list_update(xs, i,x)) <= A"
apply (rule subset_trans)
apply (rule set_update_subset_cons, auto)
done

(** upt **)

lemma upt_rec:
     "j:nat ==> upt(i,j) = (if i<j then Cons(i, upt(succ(i), j)) else Nil)"
apply (induct_tac "j", auto)
apply (drule not_lt_imp_le)
apply (auto simp: lt_Ord intro: le_anti_sym)
done

lemma upt_conv_Nil [simp]: "[| j le i; j:nat |] ==> upt(i,j) = Nil"
apply (subst upt_rec, auto)
apply (auto simp add: le_iff)
apply (drule lt_asym [THEN notE], auto)
done

(*Only needed if upt_Suc is deleted from the simpset*)
lemma upt_succ_append:
     "[| i le j; j:nat |] ==> upt(i,succ(j)) = upt(i, j)@[j]"
by simp

lemma upt_conv_Cons:
     "[| i<j; j:nat |]  ==> upt(i,j) = Cons(i,upt(succ(i),j))"
apply (rule trans)
apply (rule upt_rec, auto)
done

lemma upt_type [simp,TC]: "j:nat ==> upt(i,j):list(nat)"
by (induct_tac "j", auto)

(*LOOPS as a simprule, since j<=j*)
lemma upt_add_eq_append:
     "[| i le j; j:nat; k:nat |] ==> upt(i, j #+k) = upt(i,j)@upt(j,j#+k)"
apply (induct_tac "k")
apply (auto simp add: app_assoc app_type)
apply (rule_tac j = j in le_trans, auto)
done

lemma length_upt [simp]: "[| i:nat; j:nat |] ==>length(upt(i,j)) = j #- i"
apply (induct_tac "j")
apply (rule_tac [2] sym)
apply (auto dest!: not_lt_imp_le simp add: diff_succ diff_is_0_iff)
done

lemma nth_upt [rule_format,simp]:
     "[| i:nat; j:nat; k:nat |] ==> i #+ k < j --> nth(k, upt(i,j)) = i #+ k"
apply (induct_tac "j", simp)
apply (simp add: nth_append le_iff)
apply (auto dest!: not_lt_imp_le 
            simp add: nth_append less_diff_conv add_commute)
done

lemma take_upt [rule_format,simp]:
     "[| m:nat; n:nat |] ==>
         \<forall>i \<in> nat. i #+ m le n --> take(m, upt(i,n)) = upt(i,i#+m)"
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

lemma map_succ_upt:
     "[| m:nat; n:nat |] ==> map(succ, upt(m,n))= upt(succ(m), succ(n))"
apply (induct_tac "n")
apply (auto simp add: map_app_distrib)
done

lemma nth_map [rule_format,simp]:
     "xs:list(A) ==>
      \<forall>n \<in> nat. n < length(xs) --> nth(n, map(f, xs)) = f(nth(n, xs))"
apply (induct_tac "xs", simp)
apply (rule ballI)
apply (induct_tac "n", auto)
done

lemma nth_map_upt [rule_format]:
     "[| m:nat; n:nat |] ==>
      \<forall>i \<in> nat. i < n #- m --> nth(i, map(f, upt(m,n))) = f(m #+ i)"
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
  sublist :: "[i, i] => i"  where
    "sublist(xs, A)==
     map(fst, (filter(%p. snd(p): A, zip(xs, upt(0,length(xs))))))"

lemma sublist_0 [simp]: "xs:list(A) ==>sublist(xs, 0) =Nil"
by (unfold sublist_def, auto)

lemma sublist_Nil [simp]: "sublist(Nil, A) = Nil"
by (unfold sublist_def, auto)

lemma sublist_shift_lemma:
 "[| xs:list(B); i:nat |] ==>
  map(fst, filter(%p. snd(p):A, zip(xs, upt(i,i #+ length(xs))))) =
  map(fst, filter(%p. snd(p):nat & snd(p) #+ i:A, zip(xs,upt(0,length(xs)))))"
apply (erule list_append_induct)
apply (simp (no_asm_simp))
apply (auto simp add: add_commute length_app filter_append map_app_distrib)
done

lemma sublist_type [simp,TC]:
     "xs:list(B) ==> sublist(xs, A):list(B)"
apply (unfold sublist_def)
apply (induct_tac "xs")
apply (auto simp add: filter_append map_app_distrib)
done

lemma upt_add_eq_append2:
     "[| i:nat; j:nat |] ==> upt(0, i #+ j) = upt(0, i) @ upt(i, i #+ j)"
by (simp add: upt_add_eq_append [of 0] nat_0_le)

lemma sublist_append:
 "[| xs:list(B); ys:list(B)  |] ==>
  sublist(xs@ys, A) = sublist(xs, A) @ sublist(ys, {j:nat. j #+ length(xs): A})"
apply (unfold sublist_def)
apply (erule_tac l = ys in list_append_induct, simp)
apply (simp (no_asm_simp) add: upt_add_eq_append2 app_assoc [symmetric])
apply (auto simp add: sublist_shift_lemma length_type map_app_distrib app_assoc)
apply (simp_all add: add_commute)
done


lemma sublist_Cons:
     "[| xs:list(B); x:B |] ==>
      sublist(Cons(x, xs), A) = 
      (if 0:A then [x] else []) @ sublist(xs, {j:nat. succ(j) : A})"
apply (erule_tac l = xs in list_append_induct)
apply (simp (no_asm_simp) add: sublist_def)  
apply (simp del: app_Cons add: app_Cons [symmetric] sublist_append, simp) 
done

lemma sublist_singleton [simp]:
     "sublist([x], A) = (if 0 : A then [x] else [])"
by (simp add: sublist_Cons)

lemma sublist_upt_eq_take [rule_format, simp]:
    "xs:list(A) ==> ALL n:nat. sublist(xs,n) = take(n,xs)"
apply (erule list.induct, simp) 
apply (clarify ); 
apply (erule natE) 
apply (simp_all add: nat_eq_Collect_lt Ord_mem_iff_lt sublist_Cons)
done

lemma sublist_Int_eq:
     "xs : list(B) ==> sublist(xs, A \<inter> nat) = sublist(xs, A)"
apply (erule list.induct)
apply (simp_all add: sublist_Cons) 
done

text{*Repetition of a List Element*}

consts   repeat :: "[i,i]=>i"
primrec
  "repeat(a,0) = []"

  "repeat(a,succ(n)) = Cons(a,repeat(a,n))"

lemma length_repeat: "n \<in> nat ==> length(repeat(a,n)) = n"
by (induct_tac n, auto)

lemma repeat_succ_app: "n \<in> nat ==> repeat(a,succ(n)) = repeat(a,n) @ [a]"
apply (induct_tac n)
apply (simp_all del: app_Cons add: app_Cons [symmetric])
done

lemma repeat_type [TC]: "[|a \<in> A; n \<in> nat|] ==> repeat(a,n) \<in> list(A)"
by (induct_tac n, auto)

end

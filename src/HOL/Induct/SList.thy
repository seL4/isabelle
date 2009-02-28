(*  Title:      SList.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     B. Wolff, University of Bremen

Enriched theory of lists; mutual indirect recursive data-types.

Definition of type 'a list (strict lists) by a least fixed point

We use          list(A) == lfp(%Z. {NUMB(0)} <+> A <*> Z)
and not         list    == lfp(%Z. {NUMB(0)} <+> range(Leaf) <*> Z)

so that list can serve as a "functor" for defining other recursive types.

This enables the conservative construction of mutual recursive data-types
such as

datatype 'a m = Node 'a * ('a m) list

Tidied by lcp.  Still needs removal of nat_rec.
*)

header {* Extended List Theory (old) *}

theory SList
imports Sexp
begin

(*Hilbert_Choice is needed for the function "inv"*)

(* *********************************************************************** *)
(*                                                                         *)
(* Building up data type                                                   *)
(*                                                                         *)
(* *********************************************************************** *)


(* Defining the Concrete Constructors *)
definition
  NIL  :: "'a item" where
  "NIL = In0(Numb(0))"

definition
  CONS :: "['a item, 'a item] => 'a item" where
  "CONS M N = In1(Scons M N)"

inductive_set
  list :: "'a item set => 'a item set"
  for A :: "'a item set"
  where
    NIL_I:  "NIL: list A"
  | CONS_I: "[| a: A;  M: list A |] ==> CONS a M : list A"


typedef (List)
    'a list = "list(range Leaf) :: 'a item set" 
  by (blast intro: list.NIL_I)

abbreviation "Case == Datatype.Case"
abbreviation "Split == Datatype.Split"

definition
  List_case :: "['b, ['a item, 'a item]=>'b, 'a item] => 'b" where
  "List_case c d = Case(%x. c)(Split(d))"
  
definition
  List_rec  :: "['a item, 'b, ['a item, 'a item, 'b]=>'b] => 'b" where
  "List_rec M c d = wfrec (pred_sexp^+)
                           (%g. List_case c (%x y. d x y (g y))) M"


(* *********************************************************************** *)
(*                                                                         *)
(* Abstracting data type                                                   *)
(*                                                                         *)
(* *********************************************************************** *)

(*Declaring the abstract list constructors*)

no_translations
  "[x, xs]" == "x#[xs]"
  "[x]" == "x#[]"
no_notation
  Nil  ("[]") and
  Cons (infixr "#" 65)

definition
  Nil       :: "'a list"                               ("[]") where
   "Nil  = Abs_List(NIL)"

definition
  "Cons"       :: "['a, 'a list] => 'a list"           (infixr "#" 65) where
   "x#xs = Abs_List(CONS (Leaf x)(Rep_List xs))"

definition
  (* list Recursion -- the trancl is Essential; see list.ML *)
  list_rec  :: "['a list, 'b, ['a, 'a list, 'b]=>'b] => 'b" where
   "list_rec l c d =
      List_rec(Rep_List l) c (%x y r. d(inv Leaf x)(Abs_List y) r)"

definition
  list_case :: "['b, ['a, 'a list]=>'b, 'a list] => 'b" where
   "list_case a f xs = list_rec xs a (%x xs r. f x xs)"

(* list Enumeration *)
translations
  "[x, xs]" == "x#[xs]"
  "[x]"     == "x#[]"

  "case xs of [] => a | y#ys => b" == "CONST list_case(a, %y ys. b, xs)"


(* *********************************************************************** *)
(*                                                                         *)
(* Generalized Map Functionals                                             *)
(*                                                                         *)
(* *********************************************************************** *)

  
(* Generalized Map Functionals *)

definition
  Rep_map   :: "('b => 'a item) => ('b list => 'a item)" where
   "Rep_map f xs = list_rec xs  NIL(%x l r. CONS(f x) r)"

definition
  Abs_map   :: "('a item => 'b) => 'a item => 'b list" where
   "Abs_map g M  = List_rec M Nil (%N L r. g(N)#r)"


(**** Function definitions ****)

definition
  null      :: "'a list => bool" where
  "null xs  = list_rec xs True (%x xs r. False)"

definition
  hd        :: "'a list => 'a" where
  "hd xs    = list_rec xs (@x. True) (%x xs r. x)"

definition
  tl        :: "'a list => 'a list" where
  "tl xs    = list_rec xs (@xs. True) (%x xs r. xs)"

definition
  (* a total version of tl: *)
  ttl       :: "'a list => 'a list" where
  "ttl xs   = list_rec xs [] (%x xs r. xs)"

no_notation member  (infixl "mem" 55)

definition
  member :: "['a, 'a list] => bool"    (infixl "mem" 55) where
  "x mem xs = list_rec xs False (%y ys r. if y=x then True else r)"

definition
  list_all  :: "('a => bool) => ('a list => bool)" where
  "list_all P xs = list_rec xs True(%x l r. P(x) & r)"

definition
  map       :: "('a=>'b) => ('a list => 'b list)" where
  "map f xs = list_rec xs [] (%x l r. f(x)#r)"

no_notation append  (infixr "@" 65)

definition
  append    :: "['a list, 'a list] => 'a list"   (infixr "@" 65) where
  "xs@ys = list_rec xs ys (%x l r. x#r)"

definition
  filter    :: "['a => bool, 'a list] => 'a list" where
  "filter P xs = list_rec xs []  (%x xs r. if P(x)then x#r else r)"

definition
  foldl     :: "[['b,'a] => 'b, 'b, 'a list] => 'b" where
  "foldl f a xs = list_rec xs (%a. a)(%x xs r.%a. r(f a x))(a)"

definition
  foldr     :: "[['a,'b] => 'b, 'b, 'a list] => 'b" where
  "foldr f a xs     = list_rec xs a (%x xs r. (f x r))"

definition
  length    :: "'a list => nat" where
  "length xs = list_rec xs 0 (%x xs r. Suc r)"

definition
  drop      :: "['a list,nat] => 'a list" where
  "drop t n = (nat_rec(%x. x)(%m r xs. r(ttl xs)))(n)(t)"

definition
  copy      :: "['a, nat] => 'a list"  where     (* make list of n copies of x *)
  "copy t   = nat_rec [] (%m xs. t # xs)"

definition
  flat      :: "'a list list => 'a list" where
  "flat     = foldr (op @) []"

definition
  nth       :: "[nat, 'a list] => 'a" where
  "nth      = nat_rec hd (%m r xs. r(tl xs))"

definition
  rev       :: "'a list => 'a list" where
  "rev xs   = list_rec xs [] (%x xs xsa. xsa @ [x])"

(* miscellaneous definitions *)
definition
  zipWith   :: "['a * 'b => 'c, 'a list * 'b list] => 'c list" where
  "zipWith f S = (list_rec (fst S)  (%T.[])
                            (%x xs r. %T. if null T then [] 
                                          else f(x,hd T) # r(tl T)))(snd(S))"

definition
  zip       :: "'a list * 'b list => ('a*'b) list" where
  "zip      = zipWith  (%s. s)"

definition
  unzip     :: "('a*'b) list => ('a list * 'b list)" where
  "unzip    = foldr(% (a,b)(c,d).(a#c,b#d))([],[])"


consts take      :: "['a list,nat] => 'a list"
primrec
  take_0:  "take xs 0 = []"
  take_Suc: "take xs (Suc n) = list_case [] (%x l. x # take l n) xs"

consts enum      :: "[nat,nat] => nat list"
primrec
  enum_0:   "enum i 0 = []"
  enum_Suc: "enum i (Suc j) = (if i <= j then enum i j @ [j] else [])"


no_translations
  "[x\<leftarrow>xs . P]" == "filter (%x. P) xs"

syntax
  (* Special syntax for list_all and filter *)
  "@Alls"       :: "[idt, 'a list, bool] => bool"        ("(2Alls _:_./ _)" 10)

translations
  "[x\<leftarrow>xs. P]" == "CONST filter(%x. P) xs"
  "Alls x:xs. P" == "CONST list_all(%x. P)xs"


lemma ListI: "x : list (range Leaf) ==> x : List"
by (simp add: List_def)

lemma ListD: "x : List ==> x : list (range Leaf)"
by (simp add: List_def)

lemma list_unfold: "list(A) = usum {Numb(0)} (uprod A (list(A)))"
  by (fast intro!: list.intros [unfolded NIL_def CONS_def]
           elim: list.cases [unfolded NIL_def CONS_def])

(*This justifies using list in other recursive type definitions*)
lemma list_mono: "A<=B ==> list(A) <= list(B)"
apply (rule subsetI)
apply (erule list.induct)
apply (auto intro!: list.intros)
done

(*Type checking -- list creates well-founded sets*)
lemma list_sexp: "list(sexp) <= sexp"
apply (rule subsetI)
apply (erule list.induct)
apply (unfold NIL_def CONS_def)
apply (auto intro: sexp.intros sexp_In0I sexp_In1I)
done

(* A <= sexp ==> list(A) <= sexp *)
lemmas list_subset_sexp = subset_trans [OF list_mono list_sexp] 


(*Induction for the type 'a list *)
lemma list_induct:
    "[| P(Nil);    
        !!x xs. P(xs) ==> P(x # xs) |]  ==> P(l)"
apply (unfold Nil_def Cons_def) 
apply (rule Rep_List_inverse [THEN subst])
			 (*types force good instantiation*)
apply (rule Rep_List [unfolded List_def, THEN list.induct], simp)
apply (erule Abs_List_inverse [unfolded List_def, THEN subst], blast) 
done


(*** Isomorphisms ***)

lemma inj_on_Abs_list: "inj_on Abs_List (list(range Leaf))"
apply (rule inj_on_inverseI)
apply (erule Abs_List_inverse [unfolded List_def])
done

(** Distinctness of constructors **)

lemma CONS_not_NIL [iff]: "CONS M N ~= NIL"
by (simp add: NIL_def CONS_def)

lemmas NIL_not_CONS [iff] = CONS_not_NIL [THEN not_sym]
lemmas CONS_neq_NIL = CONS_not_NIL [THEN notE, standard]
lemmas NIL_neq_CONS = sym [THEN CONS_neq_NIL]

lemma Cons_not_Nil [iff]: "x # xs ~= Nil"
apply (unfold Nil_def Cons_def)
apply (rule CONS_not_NIL [THEN inj_on_Abs_list [THEN inj_on_contraD]])
apply (simp_all add: list.intros rangeI Rep_List [unfolded List_def])
done

lemmas Nil_not_Cons [iff] = Cons_not_Nil [THEN not_sym, standard]
lemmas Cons_neq_Nil = Cons_not_Nil [THEN notE, standard]
lemmas Nil_neq_Cons = sym [THEN Cons_neq_Nil]

(** Injectiveness of CONS and Cons **)

lemma CONS_CONS_eq [iff]: "(CONS K M)=(CONS L N) = (K=L & M=N)"
by (simp add: CONS_def)

(*For reasoning about abstract list constructors*)
declare Rep_List [THEN ListD, intro] ListI [intro]
declare list.intros [intro,simp]
declare Leaf_inject [dest!]

lemma Cons_Cons_eq [iff]: "(x#xs=y#ys) = (x=y & xs=ys)"
apply (simp add: Cons_def)
apply (subst Abs_List_inject)
apply (auto simp add: Rep_List_inject)
done

lemmas Cons_inject2 = Cons_Cons_eq [THEN iffD1, THEN conjE, standard]

lemma CONS_D: "CONS M N: list(A) ==> M: A & N: list(A)"
  by (induct L == "CONS M N" set: list) auto

lemma sexp_CONS_D: "CONS M N: sexp ==> M: sexp & N: sexp"
apply (simp add: CONS_def In1_def)
apply (fast dest!: Scons_D)
done


(*Reasoning about constructors and their freeness*)


lemma not_CONS_self: "N: list(A) ==> !M. N ~= CONS M N"
apply (erule list.induct) apply simp_all done

lemma not_Cons_self2: "\<forall>x. l ~= x#l"
by (induct l rule: list_induct) simp_all


lemma neq_Nil_conv2: "(xs ~= []) = (\<exists>y ys. xs = y#ys)"
by (induct xs rule: list_induct) auto

(** Conversion rules for List_case: case analysis operator **)

lemma List_case_NIL [simp]: "List_case c h NIL = c"
by (simp add: List_case_def NIL_def)

lemma List_case_CONS [simp]: "List_case c h (CONS M N) = h M N"
by (simp add: List_case_def CONS_def)


(*** List_rec -- by wf recursion on pred_sexp ***)

(* The trancl(pred_sexp) is essential because pred_sexp_CONS_I1,2 would not
   hold if pred_sexp^+ were changed to pred_sexp. *)

lemma List_rec_unfold_lemma:
     "(%M. List_rec M c d) == 
      wfrec (pred_sexp^+) (%g. List_case c (%x y. d x y (g y)))"
by (simp add: List_rec_def)

lemmas List_rec_unfold = 
    def_wfrec [OF List_rec_unfold_lemma wf_pred_sexp [THEN wf_trancl], 
               standard]


(** pred_sexp lemmas **)

lemma pred_sexp_CONS_I1: 
    "[| M: sexp;  N: sexp |] ==> (M, CONS M N) : pred_sexp^+"
by (simp add: CONS_def In1_def)

lemma pred_sexp_CONS_I2: 
    "[| M: sexp;  N: sexp |] ==> (N, CONS M N) : pred_sexp^+"
by (simp add: CONS_def In1_def)

lemma pred_sexp_CONS_D: 
    "(CONS M1 M2, N) : pred_sexp^+ ==>  
     (M1,N) : pred_sexp^+ & (M2,N) : pred_sexp^+"
apply (frule pred_sexp_subset_Sigma [THEN trancl_subset_Sigma, THEN subsetD])
apply (blast dest!: sexp_CONS_D intro: pred_sexp_CONS_I1 pred_sexp_CONS_I2 
                    trans_trancl [THEN transD])
done


(** Conversion rules for List_rec **)

lemma List_rec_NIL [simp]: "List_rec NIL c h = c"
apply (rule List_rec_unfold [THEN trans])
apply (simp add: List_case_NIL)
done

lemma List_rec_CONS [simp]:
     "[| M: sexp;  N: sexp |] 
      ==> List_rec (CONS M N) c h = h M N (List_rec N c h)"
apply (rule List_rec_unfold [THEN trans])
apply (simp add: pred_sexp_CONS_I2)
done


(*** list_rec -- by List_rec ***)

lemmas Rep_List_in_sexp =
    subsetD [OF range_Leaf_subset_sexp [THEN list_subset_sexp]
                Rep_List [THEN ListD]] 


lemma list_rec_Nil [simp]: "list_rec Nil c h = c"
by (simp add: list_rec_def ListI [THEN Abs_List_inverse] Nil_def)


lemma list_rec_Cons [simp]: "list_rec (a#l) c h = h a l (list_rec l c h)"
by (simp add: list_rec_def ListI [THEN Abs_List_inverse] Cons_def
              Rep_List_inverse Rep_List [THEN ListD] inj_Leaf Rep_List_in_sexp)


(*Type checking.  Useful?*)
lemma List_rec_type:
     "[| M: list(A);      
         A<=sexp;         
         c: C(NIL);       
         !!x y r. [| x: A;  y: list(A);  r: C(y) |] ==> h x y r: C(CONS x y)  
      |] ==> List_rec M c h : C(M :: 'a item)"
apply (erule list.induct, simp) 
apply (insert list_subset_sexp) 
apply (subst List_rec_CONS, blast+)
done



(** Generalized map functionals **)

lemma Rep_map_Nil [simp]: "Rep_map f Nil = NIL"
by (simp add: Rep_map_def)

lemma Rep_map_Cons [simp]: 
    "Rep_map f(x#xs) = CONS(f x)(Rep_map f xs)"
by (simp add: Rep_map_def)

lemma Rep_map_type: "(!!x. f(x): A) ==> Rep_map f xs: list(A)"
apply (simp add: Rep_map_def)
apply (rule list_induct, auto)
done

lemma Abs_map_NIL [simp]: "Abs_map g NIL = Nil"
by (simp add: Abs_map_def)

lemma Abs_map_CONS [simp]: 
    "[| M: sexp;  N: sexp |] ==> Abs_map g (CONS M N) = g(M) # Abs_map g N"
by (simp add: Abs_map_def)

(*Eases the use of primitive recursion.*)
lemma def_list_rec_NilCons:
    "[| !!xs. f(xs) = list_rec xs c h  |] 
     ==> f [] = c & f(x#xs) = h x xs (f xs)"
by simp 



lemma Abs_map_inverse:
     "[| M: list(A);  A<=sexp;  !!z. z: A ==> f(g(z)) = z |]  
      ==> Rep_map f (Abs_map g M) = M"
apply (erule list.induct, simp_all)
apply (insert list_subset_sexp) 
apply (subst Abs_map_CONS, blast)
apply blast 
apply simp 
done

(*Rep_map_inverse is obtained via Abs_Rep_map and map_ident*)

(** list_case **)

(* setting up rewrite sets *)

text{*Better to have a single theorem with a conjunctive conclusion.*}
declare def_list_rec_NilCons [OF list_case_def, simp]

(** list_case **)

lemma expand_list_case: 
 "P(list_case a f xs) = ((xs=[] --> P a ) & (!y ys. xs=y#ys --> P(f y ys)))"
by (induct xs rule: list_induct) simp_all


(**** Function definitions ****)

declare def_list_rec_NilCons [OF null_def, simp]
declare def_list_rec_NilCons [OF hd_def, simp]
declare def_list_rec_NilCons [OF tl_def, simp]
declare def_list_rec_NilCons [OF ttl_def, simp]
declare def_list_rec_NilCons [OF append_def, simp]
declare def_list_rec_NilCons [OF member_def, simp]
declare def_list_rec_NilCons [OF map_def, simp]
declare def_list_rec_NilCons [OF filter_def, simp]
declare def_list_rec_NilCons [OF list_all_def, simp]


(** nth **)

lemma def_nat_rec_0_eta:
    "[| !!n. f = nat_rec c h |] ==> f(0) = c"
by simp

lemma def_nat_rec_Suc_eta:
    "[| !!n. f = nat_rec c h |] ==> f(Suc(n)) = h n (f n)"
by simp

declare def_nat_rec_0_eta [OF nth_def, simp]
declare def_nat_rec_Suc_eta [OF nth_def, simp]


(** length **)

lemma length_Nil [simp]: "length([]) = 0"
by (simp add: length_def)

lemma length_Cons [simp]: "length(a#xs) = Suc(length(xs))"
by (simp add: length_def)


(** @ - append **)

lemma append_assoc [simp]: "(xs@ys)@zs = xs@(ys@zs)"
by (induct xs rule: list_induct) simp_all

lemma append_Nil2 [simp]: "xs @ [] = xs"
by (induct xs rule: list_induct) simp_all

(** mem **)

lemma mem_append [simp]: "x mem (xs@ys) = (x mem xs | x mem ys)"
by (induct xs rule: list_induct) simp_all

lemma mem_filter [simp]: "x mem [x\<leftarrow>xs. P x ] = (x mem xs & P(x))"
by (induct xs rule: list_induct) simp_all

(** list_all **)

lemma list_all_True [simp]: "(Alls x:xs. True) = True"
by (induct xs rule: list_induct) simp_all

lemma list_all_conj [simp]:
     "list_all p (xs@ys) = ((list_all p xs) & (list_all p ys))"
by (induct xs rule: list_induct) simp_all

lemma list_all_mem_conv: "(Alls x:xs. P(x)) = (!x. x mem xs --> P(x))"
apply (induct xs rule: list_induct)
apply simp_all
apply blast 
done

lemma nat_case_dist : "(! n. P n) = (P 0 & (! n. P (Suc n)))"
apply auto
apply (induct_tac n)
apply auto
done


lemma alls_P_eq_P_nth: "(Alls u:A. P u) = (!n. n < length A --> P(nth n A))"
apply (induct_tac A rule: list_induct)
apply simp_all
apply (rule trans)
apply (rule_tac [2] nat_case_dist [symmetric], simp_all)
done


lemma list_all_imp:
     "[| !x. P x --> Q x;  (Alls x:xs. P(x)) |] ==> (Alls x:xs. Q(x))"
by (simp add: list_all_mem_conv)


(** The functional "map" and the generalized functionals **)

lemma Abs_Rep_map: 
     "(!!x. f(x): sexp) ==>  
        Abs_map g (Rep_map f xs) = map (%t. g(f(t))) xs"
apply (induct xs rule: list_induct)
apply (simp_all add: Rep_map_type list_sexp [THEN subsetD])
done


(** Additional mapping lemmas **)

lemma map_ident [simp]: "map(%x. x)(xs) = xs"
by (induct xs rule: list_induct) simp_all

lemma map_append [simp]: "map f (xs@ys) = map f xs  @ map f ys"
by (induct xs rule: list_induct) simp_all

lemma map_compose: "map(f o g)(xs) = map f (map g xs)"
apply (simp add: o_def)
apply (induct xs rule: list_induct)
apply simp_all
done


lemma mem_map_aux1 [rule_format]:
     "x mem (map f q) --> (\<exists>y. y mem q & x = f y)"
by (induct q rule: list_induct) auto

lemma mem_map_aux2 [rule_format]: 
     "(\<exists>y. y mem q & x = f y) --> x mem (map f q)"
by (induct q rule: list_induct) auto

lemma mem_map: "x mem (map f q) = (\<exists>y. y mem q & x = f y)"
apply (rule iffI)
apply (erule mem_map_aux1)
apply (erule mem_map_aux2)
done

lemma hd_append [rule_format]: "A ~= [] --> hd(A @ B) = hd(A)"
by (induct A rule: list_induct) auto

lemma tl_append [rule_format]: "A ~= [] --> tl(A @ B) = tl(A) @ B"
by (induct A rule: list_induct) auto


(** take **)

lemma take_Suc1 [simp]: "take [] (Suc x) = []"
by simp

lemma take_Suc2 [simp]: "take(a#xs)(Suc x) = a#take xs x"
by simp


(** drop **)

lemma drop_0 [simp]: "drop xs 0 = xs"
by (simp add: drop_def)

lemma drop_Suc1 [simp]: "drop [] (Suc x) = []"
apply (induct x) 
apply (simp_all add: drop_def)
done

lemma drop_Suc2 [simp]: "drop(a#xs)(Suc x) = drop xs x"
by (simp add: drop_def)


(** copy **)

lemma copy_0 [simp]: "copy x 0 = []"
by (simp add: copy_def)

lemma copy_Suc [simp]: "copy x (Suc y) = x # copy x y"
by (simp add: copy_def)


(** fold **)

lemma foldl_Nil [simp]: "foldl f a [] = a"
by (simp add: foldl_def)

lemma foldl_Cons [simp]: "foldl f a(x#xs) = foldl f (f a x) xs"
by (simp add: foldl_def)

lemma foldr_Nil [simp]: "foldr f a [] = a"
by (simp add: foldr_def)

lemma foldr_Cons [simp]: "foldr f z(x#xs)  = f x (foldr f z xs)"
by (simp add: foldr_def)


(** flat **)

lemma flat_Nil [simp]: "flat [] = []"
by (simp add: flat_def)

lemma flat_Cons [simp]: "flat (x # xs) = x @ flat xs"
by (simp add: flat_def)

(** rev **)

lemma rev_Nil [simp]: "rev [] = []"
by (simp add: rev_def)

lemma rev_Cons [simp]: "rev (x # xs) = rev xs @ [x]"
by (simp add: rev_def)


(** zip **)

lemma zipWith_Cons_Cons [simp]:
     "zipWith f (a#as,b#bs)   = f(a,b) # zipWith f (as,bs)"
by (simp add: zipWith_def)

lemma zipWith_Nil_Nil [simp]: "zipWith f ([],[])      = []"
by (simp add: zipWith_def)


lemma zipWith_Cons_Nil [simp]: "zipWith f (x,[])  = []"
by (induct x rule: list_induct) (simp_all add: zipWith_def)


lemma zipWith_Nil_Cons [simp]: "zipWith f ([],x) = []"
by (simp add: zipWith_def)

lemma unzip_Nil [simp]: "unzip [] = ([],[])"
by (simp add: unzip_def)



(** SOME LIST THEOREMS **)

(* SQUIGGOL LEMMAS *)

lemma map_compose_ext: "map(f o g) = ((map f) o (map g))"
apply (simp add: o_def)
apply (rule ext)
apply (simp add: map_compose [symmetric] o_def)
done

lemma map_flat: "map f (flat S) = flat(map (map f) S)"
by (induct S rule: list_induct) simp_all

lemma list_all_map_eq: "(Alls u:xs. f(u) = g(u)) --> map f xs = map g xs"
by (induct xs rule: list_induct) simp_all

lemma filter_map_d: "filter p (map f xs) = map f (filter(p o f)(xs))"
by (induct xs rule: list_induct) simp_all

lemma filter_compose: "filter p (filter q xs) = filter(%x. p x & q x) xs"
by (induct xs rule: list_induct) simp_all

(* "filter(p, filter(q,xs)) = filter(q, filter(p,xs))",
   "filter(p, filter(p,xs)) = filter(p,xs)" BIRD's thms.*)
 
lemma filter_append [rule_format, simp]:
     "\<forall>B. filter p (A @ B) = (filter p A @ filter p B)"
by (induct A rule: list_induct) simp_all


(* inits(xs) == map(fst,splits(xs)), 
 
   splits([]) = []
   splits(a # xs) = <[],xs> @ map(%x. <a # fst(x),snd(x)>, splits(xs))
   (x @ y = z) = <x,y> mem splits(z)
   x mem xs & y mem ys = <x,y> mem diag(xs,ys) *)

lemma length_append: "length(xs@ys) = length(xs)+length(ys)"
by (induct xs rule: list_induct) simp_all

lemma length_map: "length(map f xs) = length(xs)"
by (induct xs rule: list_induct) simp_all


lemma take_Nil [simp]: "take [] n = []"
by (induct n) simp_all

lemma take_take_eq [simp]: "\<forall>n. take (take xs n) n = take xs n"
apply (induct xs rule: list_induct)
apply simp_all
apply (rule allI)
apply (induct_tac n)
apply auto
done

lemma take_take_Suc_eq1 [rule_format]:
     "\<forall>n. take (take xs(Suc(n+m))) n = take xs n"
apply (induct_tac xs rule: list_induct)
apply simp_all
apply (rule allI)
apply (induct_tac n)
apply auto
done

declare take_Suc [simp del]

lemma take_take_1: "take (take xs (n+m)) n = take xs n"
apply (induct m)
apply (simp_all add: take_take_Suc_eq1)
done

lemma take_take_Suc_eq2 [rule_format]:
     "\<forall>n. take (take xs n)(Suc(n+m)) = take xs n"
apply (induct_tac xs rule: list_induct)
apply simp_all
apply (rule allI)
apply (induct_tac n)
apply auto
done

lemma take_take_2: "take(take xs n)(n+m) = take xs n"
apply (induct m)
apply (simp_all add: take_take_Suc_eq2)
done

(* length(take(xs,n)) = min(n, length(xs)) *)
(* length(drop(xs,n)) = length(xs) - n *)

lemma drop_Nil [simp]: "drop  [] n  = []"
by (induct n) auto

lemma drop_drop [rule_format]: "\<forall>xs. drop (drop xs m) n = drop xs(m+n)"
apply (induct_tac m)
apply auto
apply (induct_tac xs rule: list_induct)
apply auto
done

lemma take_drop [rule_format]: "\<forall>xs. (take xs n) @ (drop xs n) = xs"
apply (induct_tac n)
apply auto
apply (induct_tac xs rule: list_induct)
apply auto
done

lemma copy_copy: "copy x n @ copy x m = copy x (n+m)"
by (induct n) auto

lemma length_copy: "length(copy x n)  = n"
by (induct n) auto

lemma length_take [rule_format, simp]:
     "\<forall>xs. length(take xs n) = min (length xs) n"
apply (induct n)
 apply auto
apply (induct_tac xs rule: list_induct)
 apply auto
done

lemma length_take_drop: "length(take A k) + length(drop A k) = length(A)" 
by (simp only: length_append [symmetric] take_drop)

lemma take_append [rule_format]: "\<forall>A. length(A) = n --> take(A@B) n = A"
apply (induct n)
apply (rule allI)
apply (rule_tac [2] allI)
apply (induct_tac A rule: list_induct)
apply (induct_tac [3] A rule: list_induct, simp_all)
done

lemma take_append2 [rule_format]:
     "\<forall>A. length(A) = n --> take(A@B) (n+k) = A @ take B k"
apply (induct n)
apply (rule allI)
apply (rule_tac [2] allI)
apply (induct_tac A rule: list_induct)
apply (induct_tac [3] A rule: list_induct, simp_all)
done

lemma take_map [rule_format]: "\<forall>n. take (map f A) n = map f (take A n)"
apply (induct A rule: list_induct)
apply simp_all
apply (rule allI)
apply (induct_tac n)
apply simp_all
done

lemma drop_append [rule_format]: "\<forall>A. length(A) = n --> drop(A@B)n = B"
apply (induct n)
apply (rule allI)
apply (rule_tac [2] allI)
apply (induct_tac A rule: list_induct)
apply (induct_tac [3] A rule: list_induct)
apply simp_all
done

lemma drop_append2 [rule_format]:
     "\<forall>A. length(A) = n --> drop(A@B)(n+k) = drop B k"
apply (induct n)
apply (rule allI)
apply (rule_tac [2] allI)
apply (induct_tac A rule: list_induct)
apply (induct_tac [3] A rule: list_induct)
apply simp_all
done


lemma drop_all [rule_format]: "\<forall>A. length(A) = n --> drop A n = []"
apply (induct n)
apply (rule allI)
apply (rule_tac [2] allI)
apply (induct_tac A rule: list_induct)
apply (induct_tac [3] A rule: list_induct)
apply auto
done

lemma drop_map [rule_format]: "\<forall>n. drop (map f A) n = map f (drop A n)"
apply (induct A rule: list_induct)
apply simp_all
apply (rule allI)
apply (induct_tac n)
apply simp_all
done

lemma take_all [rule_format]: "\<forall>A. length(A) = n --> take A n = A"
apply (induct n)
apply (rule allI)
apply (rule_tac [2] allI)
apply (induct_tac A rule: list_induct)
apply (induct_tac [3] A rule: list_induct)
apply auto
done

lemma foldl_single: "foldl f a [b] = f a b"
by simp_all

lemma foldl_append [simp]:
  "\<And>a. foldl f a (A @ B) = foldl f (foldl f a A) B"
by (induct A rule: list_induct) simp_all

lemma foldl_map:
  "\<And>e. foldl f e (map g S) = foldl (%x y. f x (g y)) e S"
by (induct S rule: list_induct) simp_all

lemma foldl_neutr_distr [rule_format]:
  assumes r_neutr: "\<forall>a. f a e = a" 
      and r_neutl: "\<forall>a. f e a = a"
      and assoc:   "\<forall>a b c. f a (f b c) = f(f a b) c"
  shows "\<forall>y. f y (foldl f e A) = foldl f y A"
apply (induct A rule: list_induct)
apply (simp_all add: r_neutr r_neutl, clarify) 
apply (erule all_dupE) 
apply (rule trans) 
prefer 2 apply assumption
apply (simp (no_asm_use) add: assoc [THEN spec, THEN spec, THEN spec, THEN sym])
apply simp
done

lemma foldl_append_sym: 
"[| !a. f a e = a; !a. f e a = a;           
    !a b c. f a (f b c) = f(f a b) c |]    
  ==> foldl f e (A @ B) = f(foldl f e A)(foldl f e B)"
apply (rule trans)
apply (rule foldl_append)
apply (rule sym) 
apply (rule foldl_neutr_distr, auto)
done

lemma foldr_append [rule_format, simp]:
     "\<forall>a. foldr f a (A @ B) = foldr f (foldr f a B) A"
by (induct A rule: list_induct) simp_all


lemma foldr_map: "\<And>e. foldr f e (map g S) = foldr (f o g) e S"
by (induct S rule: list_induct) (simp_all add: o_def)

lemma foldr_Un_eq_UN: "foldr op Un {} S = (UN X: {t. t mem S}.X)"
by (induct S rule: list_induct) auto

lemma foldr_neutr_distr:
     "[| !a. f e a = a; !a b c. f a (f b c) = f(f a b) c |]    
      ==> foldr f y S = f (foldr f e S) y"
by (induct S rule: list_induct) auto

lemma foldr_append2: 
    "[| !a. f e a = a; !a b c. f a (f b c) = f(f a b) c |]
     ==> foldr f e (A @ B) = f (foldr f e A) (foldr f e B)"
apply auto
apply (rule foldr_neutr_distr)
apply auto
done

lemma foldr_flat: 
    "[| !a. f e a = a; !a b c. f a (f b c) = f(f a b) c |] ==>  
      foldr f e (flat S) = (foldr f e)(map (foldr f e) S)"
apply (induct S rule: list_induct)
apply (simp_all del: foldr_append add: foldr_append2)
done


lemma list_all_map: "(Alls x:map f xs .P(x)) = (Alls x:xs.(P o f)(x))"
by (induct xs rule: list_induct) auto

lemma list_all_and: 
     "(Alls x:xs. P(x)&Q(x)) = ((Alls x:xs. P(x))&(Alls x:xs. Q(x)))"
by (induct xs rule: list_induct) auto


lemma nth_map [rule_format]:
     "\<forall>i. i < length(A)  --> nth i (map f A) = f(nth i A)"
apply (induct A rule: list_induct)
apply simp_all
apply (rule allI)
apply (induct_tac i)
apply auto
done

lemma nth_app_cancel_right [rule_format]:
     "\<forall>i. i < length(A)  --> nth i(A@B) = nth i A"
apply (induct A rule: list_induct)
apply simp_all
apply (rule allI)
apply (induct_tac i)
apply simp_all
done

lemma nth_app_cancel_left [rule_format]:
     "\<forall>n. n = length(A) --> nth(n+i)(A@B) = nth i B"
by (induct A rule: list_induct) simp_all


(** flat **)

lemma flat_append [simp]: "flat(xs@ys) = flat(xs) @ flat(ys)"
by (induct xs rule: list_induct) auto

lemma filter_flat: "filter p (flat S) = flat(map (filter p) S)"
by (induct S rule: list_induct) auto


(** rev **)

lemma rev_append [simp]: "rev(xs@ys) = rev(ys) @ rev(xs)"
by (induct xs rule: list_induct) auto

lemma rev_rev_ident [simp]: "rev(rev l) = l"
by (induct l rule: list_induct) auto

lemma rev_flat: "rev(flat ls) = flat (map rev (rev ls))"
by (induct ls rule: list_induct) auto

lemma rev_map_distrib: "rev(map f l) = map f (rev l)"
by (induct l rule: list_induct) auto

lemma foldl_rev: "foldl f b (rev l) = foldr (%x y. f y x) b l"
by (induct l rule: list_induct) auto

lemma foldr_rev: "foldr f b (rev l) = foldl (%x y. f y x) b l"
apply (rule sym)
apply (rule trans)
apply (rule_tac [2] foldl_rev)
apply simp
done

end

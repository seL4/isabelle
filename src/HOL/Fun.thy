(*  Title:      HOL/Fun.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Notions about functions.
*)

theory Fun = Typedef:

instance set :: (type) order
  by (intro_classes,
      (assumption | rule subset_refl subset_trans subset_antisym psubset_eq)+)

constdefs
  fun_upd :: "('a => 'b) => 'a => 'b => ('a => 'b)"
   "fun_upd f a b == % x. if x=a then b else f x"

nonterminals
  updbinds updbind
syntax
  "_updbind" :: "['a, 'a] => updbind"             ("(2_ :=/ _)")
  ""         :: "updbind => updbinds"             ("_")
  "_updbinds":: "[updbind, updbinds] => updbinds" ("_,/ _")
  "_Update"  :: "['a, updbinds] => 'a"            ("_/'((_)')" [1000,0] 900)

translations
  "_Update f (_updbinds b bs)"  == "_Update (_Update f b) bs"
  "f(x:=y)"                     == "fun_upd f x y"

(* Hint: to define the sum of two functions (or maps), use sum_case.
         A nice infix syntax could be defined (in Datatype.thy or below) by
consts
  fun_sum :: "('a => 'c) => ('b => 'c) => (('a+'b) => 'c)" (infixr "'(+')"80)
translations
 "fun_sum" == sum_case
*)

constdefs
 overwrite :: "('a => 'b) => ('a => 'b) => 'a set => ('a => 'b)"
              ("_/'(_|/_')"  [900,0,0]900)
"f(g|A) == %a. if a : A then g a else f a"

 id :: "'a => 'a"
"id == %x. x"

 comp :: "['b => 'c, 'a => 'b, 'a] => 'c"   (infixl "o" 55)
"f o g == %x. f(g(x))"

text{*compatibility*}
lemmas o_def = comp_def

syntax (xsymbols)
  comp :: "['b => 'c, 'a => 'b, 'a] => 'c"        (infixl "\<circ>" 55)
syntax (HTML output)
  comp :: "['b => 'c, 'a => 'b, 'a] => 'c"        (infixl "\<circ>" 55)


constdefs
  inj_on :: "['a => 'b, 'a set] => bool"         (*injective*)
    "inj_on f A == ! x:A. ! y:A. f(x)=f(y) --> x=y"

text{*A common special case: functions injective over the entire domain type.*}
syntax inj   :: "('a => 'b) => bool"
translations
  "inj f" == "inj_on f UNIV"

constdefs
  surj :: "('a => 'b) => bool"                   (*surjective*)
    "surj f == ! y. ? x. y=f(x)"

  bij :: "('a => 'b) => bool"                    (*bijective*)
    "bij f == inj f & surj f"



text{*As a simplification rule, it replaces all function equalities by
  first-order equalities.*}
lemma expand_fun_eq: "(f = g) = (! x. f(x)=g(x))"
apply (rule iffI)
apply (simp (no_asm_simp))
apply (rule ext, simp (no_asm_simp))
done

lemma apply_inverse:
    "[| f(x)=u;  !!x. P(x) ==> g(f(x)) = x;  P(x) |] ==> x=g(u)"
by auto


text{*The Identity Function: @{term id}*}
lemma id_apply [simp]: "id x = x"
by (simp add: id_def)


subsection{*The Composition Operator: @{term "f \<circ> g"}*}

lemma o_apply [simp]: "(f o g) x = f (g x)"
by (simp add: comp_def)

lemma o_assoc: "f o (g o h) = f o g o h"
by (simp add: comp_def)

lemma id_o [simp]: "id o g = g"
by (simp add: comp_def)

lemma o_id [simp]: "f o id = f"
by (simp add: comp_def)

lemma image_compose: "(f o g) ` r = f`(g`r)"
by (simp add: comp_def, blast)

lemma image_eq_UN: "f`A = (UN x:A. {f x})"
by blast

lemma UN_o: "UNION A (g o f) = UNION (f`A) g"
by (unfold comp_def, blast)


subsection{*The Injectivity Predicate, @{term inj}*}

text{*NB: @{term inj} now just translates to @{term inj_on}*}


text{*For Proofs in @{text "Tools/datatype_rep_proofs"}*}
lemma datatype_injI:
    "(!! x. ALL y. f(x) = f(y) --> x=y) ==> inj(f)"
by (simp add: inj_on_def)

theorem range_ex1_eq: "inj f \<Longrightarrow> b : range f = (EX! x. b = f x)"
  by (unfold inj_on_def, blast)

lemma injD: "[| inj(f); f(x) = f(y) |] ==> x=y"
by (simp add: inj_on_def)

(*Useful with the simplifier*)
lemma inj_eq: "inj(f) ==> (f(x) = f(y)) = (x=y)"
by (force simp add: inj_on_def)


subsection{*The Predicate @{term inj_on}: Injectivity On A Restricted Domain*}

lemma inj_onI:
    "(!! x y. [|  x:A;  y:A;  f(x) = f(y) |] ==> x=y) ==> inj_on f A"
by (simp add: inj_on_def)

lemma inj_on_inverseI: "(!!x. x:A ==> g(f(x)) = x) ==> inj_on f A"
by (auto dest:  arg_cong [of concl: g] simp add: inj_on_def)

lemma inj_onD: "[| inj_on f A;  f(x)=f(y);  x:A;  y:A |] ==> x=y"
by (unfold inj_on_def, blast)

lemma inj_on_iff: "[| inj_on f A;  x:A;  y:A |] ==> (f(x)=f(y)) = (x=y)"
by (blast dest!: inj_onD)

lemma comp_inj_on:
     "[| inj_on f A;  inj_on g (f`A) |] ==> inj_on (g o f) A"
by (simp add: comp_def inj_on_def)

lemma inj_on_contraD: "[| inj_on f A;  ~x=y;  x:A;  y:A |] ==> ~ f(x)=f(y)"
by (unfold inj_on_def, blast)

lemma inj_singleton: "inj (%s. {s})"
by (simp add: inj_on_def)

lemma subset_inj_on: "[| A<=B; inj_on f B |] ==> inj_on f A"
by (unfold inj_on_def, blast)


subsection{*The Predicate @{term surj}: Surjectivity*}

lemma surjI: "(!! x. g(f x) = x) ==> surj g"
apply (simp add: surj_def)
apply (blast intro: sym)
done

lemma surj_range: "surj f ==> range f = UNIV"
by (auto simp add: surj_def)

lemma surjD: "surj f ==> EX x. y = f x"
by (simp add: surj_def)

lemma surjE: "surj f ==> (!!x. y = f x ==> C) ==> C"
by (simp add: surj_def, blast)

lemma comp_surj: "[| surj f;  surj g |] ==> surj (g o f)"
apply (simp add: comp_def surj_def, clarify)
apply (drule_tac x = y in spec, clarify)
apply (drule_tac x = x in spec, blast)
done



subsection{*The Predicate @{term bij}: Bijectivity*}

lemma bijI: "[| inj f; surj f |] ==> bij f"
by (simp add: bij_def)

lemma bij_is_inj: "bij f ==> inj f"
by (simp add: bij_def)

lemma bij_is_surj: "bij f ==> surj f"
by (simp add: bij_def)


subsection{*Facts About the Identity Function*}

text{*We seem to need both the @{term id} forms and the @{term "\<lambda>x. x"}
forms. The latter can arise by rewriting, while @{term id} may be used
explicitly.*}

lemma image_ident [simp]: "(%x. x) ` Y = Y"
by blast

lemma image_id [simp]: "id ` Y = Y"
by (simp add: id_def)

lemma vimage_ident [simp]: "(%x. x) -` Y = Y"
by blast

lemma vimage_id [simp]: "id -` A = A"
by (simp add: id_def)

lemma vimage_image_eq: "f -` (f ` A) = {y. EX x:A. f x = f y}"
by (blast intro: sym)

lemma image_vimage_subset: "f ` (f -` A) <= A"
by blast

lemma image_vimage_eq [simp]: "f ` (f -` A) = A Int range f"
by blast

lemma surj_image_vimage_eq: "surj f ==> f ` (f -` A) = A"
by (simp add: surj_range)

lemma inj_vimage_image_eq: "inj f ==> f -` (f ` A) = A"
by (simp add: inj_on_def, blast)

lemma vimage_subsetD: "surj f ==> f -` B <= A ==> B <= f ` A"
apply (unfold surj_def)
apply (blast intro: sym)
done

lemma vimage_subsetI: "inj f ==> B <= f ` A ==> f -` B <= A"
by (unfold inj_on_def, blast)

lemma vimage_subset_eq: "bij f ==> (f -` B <= A) = (B <= f ` A)"
apply (unfold bij_def)
apply (blast del: subsetI intro: vimage_subsetI vimage_subsetD)
done

lemma image_Int_subset: "f`(A Int B) <= f`A Int f`B"
by blast

lemma image_diff_subset: "f`A - f`B <= f`(A - B)"
by blast

lemma inj_on_image_Int:
   "[| inj_on f C;  A<=C;  B<=C |] ==> f`(A Int B) = f`A Int f`B"
apply (simp add: inj_on_def, blast)
done

lemma inj_on_image_set_diff:
   "[| inj_on f C;  A<=C;  B<=C |] ==> f`(A-B) = f`A - f`B"
apply (simp add: inj_on_def, blast)
done

lemma image_Int: "inj f ==> f`(A Int B) = f`A Int f`B"
by (simp add: inj_on_def, blast)

lemma image_set_diff: "inj f ==> f`(A-B) = f`A - f`B"
by (simp add: inj_on_def, blast)

lemma inj_image_mem_iff: "inj f ==> (f a : f`A) = (a : A)"
by (blast dest: injD)

lemma inj_image_subset_iff: "inj f ==> (f`A <= f`B) = (A<=B)"
by (simp add: inj_on_def, blast)

lemma inj_image_eq_iff: "inj f ==> (f`A = f`B) = (A = B)"
by (blast dest: injD)

lemma image_UN: "(f ` (UNION A B)) = (UN x:A.(f ` (B x)))"
by blast

(*injectivity's required.  Left-to-right inclusion holds even if A is empty*)
lemma image_INT:
   "[| inj_on f C;  ALL x:A. B x <= C;  j:A |]
    ==> f ` (INTER A B) = (INT x:A. f ` B x)"
apply (simp add: inj_on_def, blast)
done

(*Compare with image_INT: no use of inj_on, and if f is surjective then
  it doesn't matter whether A is empty*)
lemma bij_image_INT: "bij f ==> f ` (INTER A B) = (INT x:A. f ` B x)"
apply (simp add: bij_def)
apply (simp add: inj_on_def surj_def, blast)
done

lemma surj_Compl_image_subset: "surj f ==> -(f`A) <= f`(-A)"
by (auto simp add: surj_def)

lemma inj_image_Compl_subset: "inj f ==> f`(-A) <= -(f`A)"
by (auto simp add: inj_on_def)

lemma bij_image_Compl_eq: "bij f ==> f`(-A) = -(f`A)"
apply (simp add: bij_def)
apply (rule equalityI)
apply (simp_all (no_asm_simp) add: inj_image_Compl_subset surj_Compl_image_subset)
done


subsection{*Function Updating*}

lemma fun_upd_idem_iff: "(f(x:=y) = f) = (f x = y)"
apply (simp add: fun_upd_def, safe)
apply (erule subst)
apply (rule_tac [2] ext, auto)
done

(* f x = y ==> f(x:=y) = f *)
lemmas fun_upd_idem = fun_upd_idem_iff [THEN iffD2, standard]

(* f(x := f x) = f *)
declare refl [THEN fun_upd_idem, iff]

lemma fun_upd_apply [simp]: "(f(x:=y))z = (if z=x then y else f z)"
apply (simp (no_asm) add: fun_upd_def)
done

(* fun_upd_apply supersedes these two,   but they are useful
   if fun_upd_apply is intentionally removed from the simpset *)
lemma fun_upd_same: "(f(x:=y)) x = y"
by simp

lemma fun_upd_other: "z~=x ==> (f(x:=y)) z = f z"
by simp

lemma fun_upd_upd [simp]: "f(x:=y,x:=z) = f(x:=z)"
by (simp add: expand_fun_eq)

lemma fun_upd_twist: "a ~= c ==> (m(a:=b))(c:=d) = (m(c:=d))(a:=b)"
by (rule ext, auto)

subsection{* overwrite *}

lemma overwrite_emptyset[simp]: "f(g|{}) = f"
by(simp add:overwrite_def)

lemma overwrite_apply_notin[simp]: "a ~: A ==> (f(g|A)) a = f a"
by(simp add:overwrite_def)

lemma overwrite_apply_in[simp]: "a : A ==> (f(g|A)) a = g a"
by(simp add:overwrite_def)

text{*The ML section includes some compatibility bindings and a simproc
for function updates, in addition to the usual ML-bindings of theorems.*}
ML
{*
val id_def = thm "id_def";
val inj_on_def = thm "inj_on_def";
val surj_def = thm "surj_def";
val bij_def = thm "bij_def";
val fun_upd_def = thm "fun_upd_def";

val o_def = thm "comp_def";
val injI = thm "inj_onI";
val inj_inverseI = thm "inj_on_inverseI";
val set_cs = claset() delrules [equalityI];

val print_translation = [("Pi", dependent_tr' ("@Pi", "op funcset"))];

(* simplifies terms of the form f(...,x:=y,...,x:=z,...) to f(...,x:=z,...) *)
local
  fun gen_fun_upd None T _ _ = None
    | gen_fun_upd (Some f) T x y = Some (Const ("Fun.fun_upd",T) $ f $ x $ y)
  fun dest_fun_T1 (Type (_, T :: Ts)) = T
  fun find_double (t as Const ("Fun.fun_upd",T) $ f $ x $ y) =
    let
      fun find (Const ("Fun.fun_upd",T) $ g $ v $ w) =
            if v aconv x then Some g else gen_fun_upd (find g) T v w
        | find t = None
    in (dest_fun_T1 T, gen_fun_upd (find f) T x y) end

  val ss = simpset ()
  val fun_upd_prover = K (rtac eq_reflection 1 THEN rtac ext 1 THEN simp_tac ss 1)
in
  val fun_upd2_simproc =
    Simplifier.simproc (Theory.sign_of (the_context ()))
      "fun_upd2" ["f(v := w, x := y)"]
      (fn sg => fn _ => fn t =>
        case find_double t of (T, None) => None
        | (T, Some rhs) => Some (Tactic.prove sg [] [] (Term.equals T $ t $ rhs) fun_upd_prover))
end;
Addsimprocs[fun_upd2_simproc];

val expand_fun_eq = thm "expand_fun_eq";
val apply_inverse = thm "apply_inverse";
val id_apply = thm "id_apply";
val o_apply = thm "o_apply";
val o_assoc = thm "o_assoc";
val id_o = thm "id_o";
val o_id = thm "o_id";
val image_compose = thm "image_compose";
val image_eq_UN = thm "image_eq_UN";
val UN_o = thm "UN_o";
val datatype_injI = thm "datatype_injI";
val injD = thm "injD";
val inj_eq = thm "inj_eq";
val inj_onI = thm "inj_onI";
val inj_on_inverseI = thm "inj_on_inverseI";
val inj_onD = thm "inj_onD";
val inj_on_iff = thm "inj_on_iff";
val comp_inj_on = thm "comp_inj_on";
val inj_on_contraD = thm "inj_on_contraD";
val inj_singleton = thm "inj_singleton";
val subset_inj_on = thm "subset_inj_on";
val surjI = thm "surjI";
val surj_range = thm "surj_range";
val surjD = thm "surjD";
val surjE = thm "surjE";
val comp_surj = thm "comp_surj";
val bijI = thm "bijI";
val bij_is_inj = thm "bij_is_inj";
val bij_is_surj = thm "bij_is_surj";
val image_ident = thm "image_ident";
val image_id = thm "image_id";
val vimage_ident = thm "vimage_ident";
val vimage_id = thm "vimage_id";
val vimage_image_eq = thm "vimage_image_eq";
val image_vimage_subset = thm "image_vimage_subset";
val image_vimage_eq = thm "image_vimage_eq";
val surj_image_vimage_eq = thm "surj_image_vimage_eq";
val inj_vimage_image_eq = thm "inj_vimage_image_eq";
val vimage_subsetD = thm "vimage_subsetD";
val vimage_subsetI = thm "vimage_subsetI";
val vimage_subset_eq = thm "vimage_subset_eq";
val image_Int_subset = thm "image_Int_subset";
val image_diff_subset = thm "image_diff_subset";
val inj_on_image_Int = thm "inj_on_image_Int";
val inj_on_image_set_diff = thm "inj_on_image_set_diff";
val image_Int = thm "image_Int";
val image_set_diff = thm "image_set_diff";
val inj_image_mem_iff = thm "inj_image_mem_iff";
val inj_image_subset_iff = thm "inj_image_subset_iff";
val inj_image_eq_iff = thm "inj_image_eq_iff";
val image_UN = thm "image_UN";
val image_INT = thm "image_INT";
val bij_image_INT = thm "bij_image_INT";
val surj_Compl_image_subset = thm "surj_Compl_image_subset";
val inj_image_Compl_subset = thm "inj_image_Compl_subset";
val bij_image_Compl_eq = thm "bij_image_Compl_eq";
val fun_upd_idem_iff = thm "fun_upd_idem_iff";
val fun_upd_idem = thm "fun_upd_idem";
val fun_upd_apply = thm "fun_upd_apply";
val fun_upd_same = thm "fun_upd_same";
val fun_upd_other = thm "fun_upd_other";
val fun_upd_upd = thm "fun_upd_upd";
val fun_upd_twist = thm "fun_upd_twist";
val range_ex1_eq = thm "range_ex1_eq";
*}

end

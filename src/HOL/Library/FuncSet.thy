(*  Title:      HOL/Library/FuncSet.thy
    ID:         $Id$
    Author:     Florian Kammueller and Lawrence C Paulson
*)

header {* Pi and Function Sets *}

theory FuncSet = Main:

constdefs
  Pi :: "['a set, 'a => 'b set] => ('a => 'b) set"
  "Pi A B == {f. \<forall>x. x \<in> A --> f x \<in> B x}"

  extensional :: "'a set => ('a => 'b) set"
  "extensional A == {f. \<forall>x. x~:A --> f x = arbitrary}"

  "restrict" :: "['a => 'b, 'a set] => ('a => 'b)"
  "restrict f A == (%x. if x \<in> A then f x else arbitrary)"

syntax
  "@Pi"  :: "[pttrn, 'a set, 'b set] => ('a => 'b) set"  ("(3PI _:_./ _)" 10)
  funcset :: "['a set, 'b set] => ('a => 'b) set"      (infixr "->" 60)
  "@lam" :: "[pttrn, 'a set, 'a => 'b] => ('a=>'b)"  ("(3%_:_./ _)" [0,0,3] 3)

syntax (xsymbols)
  "@Pi" :: "[pttrn, 'a set, 'b set] => ('a => 'b) set"  ("(3\<Pi> _\<in>_./ _)"   10)
  funcset :: "['a set, 'b set] => ('a => 'b) set"  (infixr "\<rightarrow>" 60)
  "@lam" :: "[pttrn, 'a set, 'a => 'b] => ('a=>'b)"  ("(3\<lambda>_\<in>_./ _)" [0,0,3] 3)

syntax (HTML output)
  "@Pi" :: "[pttrn, 'a set, 'b set] => ('a => 'b) set"  ("(3\<Pi> _\<in>_./ _)"   10)
  "@lam" :: "[pttrn, 'a set, 'a => 'b] => ('a=>'b)"  ("(3\<lambda>_\<in>_./ _)" [0,0,3] 3)

translations
  "PI x:A. B" => "Pi A (%x. B)"
  "A -> B" => "Pi A (_K B)"
  "%x:A. f" == "restrict (%x. f) A"

constdefs
  "compose" :: "['a set, 'b => 'c, 'a => 'b] => ('a => 'c)"
  "compose A g f == \<lambda>x\<in>A. g (f x)"

print_translation {* [("Pi", dependent_tr' ("@Pi", "funcset"))] *}


subsection{*Basic Properties of @{term Pi}*}

lemma Pi_I: "(!!x. x \<in> A ==> f x \<in> B x) ==> f \<in> Pi A B"
  by (simp add: Pi_def)

lemma funcsetI: "(!!x. x \<in> A ==> f x \<in> B) ==> f \<in> A -> B"
  by (simp add: Pi_def)

lemma Pi_mem: "[|f: Pi A B; x \<in> A|] ==> f x \<in> B x"
  by (simp add: Pi_def)

lemma funcset_mem: "[|f \<in> A -> B; x \<in> A|] ==> f x \<in> B"
  by (simp add: Pi_def)

lemma funcset_image: "f \<in> A\<rightarrow>B ==> f ` A \<subseteq> B"
by (auto simp add: Pi_def)

lemma Pi_eq_empty: "((PI x: A. B x) = {}) = (\<exists>x\<in>A. B(x) = {})"
apply (simp add: Pi_def, auto)
txt{*Converse direction requires Axiom of Choice to exhibit a function
picking an element from each non-empty @{term "B x"}*}
apply (drule_tac x = "%u. SOME y. y \<in> B u" in spec, auto)
apply (cut_tac P= "%y. y \<in> B x" in some_eq_ex, auto)
done

lemma Pi_empty [simp]: "Pi {} B = UNIV"
  by (simp add: Pi_def)

lemma Pi_UNIV [simp]: "A -> UNIV = UNIV"
  by (simp add: Pi_def)

text{*Covariance of Pi-sets in their second argument*}
lemma Pi_mono: "(!!x. x \<in> A ==> B x <= C x) ==> Pi A B <= Pi A C"
  by (simp add: Pi_def, blast)

text{*Contravariance of Pi-sets in their first argument*}
lemma Pi_anti_mono: "A' <= A ==> Pi A B <= Pi A' B"
  by (simp add: Pi_def, blast)


subsection{*Composition With a Restricted Domain: @{term compose}*}

lemma funcset_compose:
    "[| f \<in> A -> B; g \<in> B -> C |]==> compose A g f \<in> A -> C"
  by (simp add: Pi_def compose_def restrict_def)

lemma compose_assoc:
    "[| f \<in> A -> B; g \<in> B -> C; h \<in> C -> D |]
      ==> compose A h (compose A g f) = compose A (compose B h g) f"
  by (simp add: expand_fun_eq Pi_def compose_def restrict_def)

lemma compose_eq: "x \<in> A ==> compose A g f x = g(f(x))"
  by (simp add: compose_def restrict_def)

lemma surj_compose: "[| f ` A = B; g ` B = C |] ==> compose A g f ` A = C"
  by (auto simp add: image_def compose_eq)

lemma inj_on_compose:
    "[| f ` A = B; inj_on f A; inj_on g B |] ==> inj_on (compose A g f) A"
  by (auto simp add: inj_on_def compose_eq)


subsection{*Bounded Abstraction: @{term restrict}*}

lemma restrict_in_funcset: "(!!x. x \<in> A ==> f x \<in> B) ==> (\<lambda>x\<in>A. f x) \<in> A -> B"
  by (simp add: Pi_def restrict_def)

lemma restrictI: "(!!x. x \<in> A ==> f x \<in> B x) ==> (\<lambda>x\<in>A. f x) \<in> Pi A B"
  by (simp add: Pi_def restrict_def)

lemma restrict_apply [simp]:
    "(\<lambda>y\<in>A. f y) x = (if x \<in> A then f x else arbitrary)"
  by (simp add: restrict_def)

lemma restrict_ext:
    "(!!x. x \<in> A ==> f x = g x) ==> (\<lambda>x\<in>A. f x) = (\<lambda>x\<in>A. g x)"
  by (simp add: expand_fun_eq Pi_def Pi_def restrict_def)

lemma inj_on_restrict_eq: "inj_on (restrict f A) A = inj_on f A"
  by (simp add: inj_on_def restrict_def)

lemma Id_compose:
    "[|f \<in> A -> B;  f \<in> extensional A|] ==> compose A (\<lambda>y\<in>B. y) f = f"
  by (auto simp add: expand_fun_eq compose_def extensional_def Pi_def)

lemma compose_Id:
    "[|g \<in> A -> B;  g \<in> extensional A|] ==> compose A g (\<lambda>x\<in>A. x) = g"
  by (auto simp add: expand_fun_eq compose_def extensional_def Pi_def)


subsection{*Extensionality*}

lemma extensional_arb: "[|f \<in> extensional A; x\<notin> A|] ==> f x = arbitrary"
  by (simp add: extensional_def)

lemma restrict_extensional [simp]: "restrict f A \<in> extensional A"
  by (simp add: restrict_def extensional_def)

lemma compose_extensional [simp]: "compose A f g \<in> extensional A"
  by (simp add: compose_def)

lemma extensionalityI:
    "[| f \<in> extensional A; g \<in> extensional A;
      !!x. x\<in>A ==> f x = g x |] ==> f = g"
  by (force simp add: expand_fun_eq extensional_def)

lemma Inv_funcset: "f ` A = B ==> (\<lambda>x\<in>B. Inv A f x) : B -> A"
  by (unfold Inv_def) (fast intro: restrict_in_funcset someI2)

lemma compose_Inv_id:
    "[| inj_on f A;  f ` A = B |]
      ==> compose A (\<lambda>y\<in>B. Inv A f y) f = (\<lambda>x\<in>A. x)"
  apply (simp add: compose_def)
  apply (rule restrict_ext, auto)
  apply (erule subst)
  apply (simp add: Inv_f_f)
  done

lemma compose_id_Inv:
    "f ` A = B ==> compose B f (\<lambda>y\<in>B. Inv A f y) = (\<lambda>x\<in>B. x)"
  apply (simp add: compose_def)
  apply (rule restrict_ext)
  apply (simp add: f_Inv_f)
  done


subsection{*Bijections Between Sets*}

text{*The basic definition could be moved to @{text "Fun.thy"}, but most of
the theorems belong here, or need at least @{term Hilbert_Choice}.*}

constdefs
  bij_betw :: "['a => 'b, 'a set, 'b set] => bool"         (*bijective*)
    "bij_betw f A B == inj_on f A & f ` A = B"

lemma bij_betw_imp_inj_on: "bij_betw f A B \<Longrightarrow> inj_on f A"
by (simp add: bij_betw_def)

lemma bij_betw_imp_funcset: "bij_betw f A B \<Longrightarrow> f \<in> A \<rightarrow> B"
by (auto simp add: bij_betw_def inj_on_Inv Pi_def)

lemma bij_betw_Inv: "bij_betw f A B \<Longrightarrow> bij_betw (Inv A f) B A"
apply (auto simp add: bij_betw_def inj_on_Inv Inv_mem) 
apply (simp add: image_compose [symmetric] o_def) 
apply (simp add: image_def Inv_f_f) 
done

lemma bij_betw_compose:
    "[| bij_betw f A B; bij_betw g B C |] ==> bij_betw (compose A g f) A C"
apply (simp add: bij_betw_def compose_eq inj_on_compose)
apply (auto simp add: compose_def image_def)
done


subsection{*Cardinality*}

lemma card_inj: "[|f \<in> A\<rightarrow>B; inj_on f A; finite B|] ==> card(A) \<le> card(B)"
apply (rule card_inj_on_le)
apply (auto simp add: Pi_def)
done

lemma card_bij:
     "[|f \<in> A\<rightarrow>B; inj_on f A;
        g \<in> B\<rightarrow>A; inj_on g B; finite A; finite B|] ==> card(A) = card(B)"
by (blast intro: card_inj order_antisym)

end

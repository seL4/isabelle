(*  Title:      HOL/Isar_examples/W_correct.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Correctness of Milner's type inference algorithm W (let-free version).
*)

header {* Milner's type inference algorithm~W (let-free version) *};

theory W_correct = Main + Type:;

text_raw {*
  \footnote{Based upon \url{http://isabelle.in.tum.de/library/HOL/W0}
  by Dieter Nazareth and Tobias Nipkow.}
*};


subsection "Mini ML with type inference rules";

datatype
  expr = Var nat | Abs expr | App expr expr;


text {* Type inference rules. *};

consts
  has_type :: "(typ list * expr * typ) set";

syntax
  "_has_type" :: "[typ list, expr, typ] => bool"
    ("((_) |-/ (_) :: (_))" [60, 0, 60] 60);
translations
  "a |- e :: t" == "(a,e,t) : has_type";

inductive has_type
  intros [simp]
    Var: "n < length a ==> a |- Var n :: a ! n"
    Abs: "t1#a |- e :: t2 ==> a |- Abs e :: t1 -> t2"
    App: "a |- e1 :: t2 -> t1 ==> a |- e2 :: t2
      ==> a |- App e1 e2 :: t1";


text {* Type assigment is closed wrt.\ substitution. *};

lemma has_type_subst_closed: "a |- e :: t ==> $s a |- e :: $s t";
proof -;
  assume "a |- e :: t";
  thus ?thesis (is "?P a e t");
  proof (induct (open) ?P a e t);
    case Var;
    hence "n < length (map ($ s) a)"; by simp;
    hence "map ($ s) a |- Var n :: map ($ s) a ! n";
      by (rule has_type.Var);
    also; have "map ($ s) a ! n = $ s (a ! n)";
      by (rule nth_map);
    also; have "map ($ s) a = $ s a";
      by (simp only: app_subst_list);
    finally; show "?P a (Var n) (a ! n)"; .;
  next;
    case Abs;
    hence "$ s t1 # map ($ s) a |- e :: $ s t2";
      by (simp add: app_subst_list);
    hence "map ($ s) a |- Abs e :: $ s t1 -> $ s t2";
      by (rule has_type.Abs);
    thus "?P a (Abs e) (t1 -> t2)";
      by (simp add: app_subst_list);
  next;
    case App;
    thus "?P a (App e1 e2) t1"; by simp;
  qed;
qed;


subsection {* Type inference algorithm W *};

consts
  W :: "[expr, typ list, nat] => (subst * typ * nat) maybe";

primrec
  "W (Var i) a n =
    (if i < length a then Ok (id_subst, a ! i, n) else Fail)"
  "W (Abs e) a n =
    ((s, t, m) := W e (TVar n # a) (Suc n);
     Ok (s, (s n) -> t, m))"
  "W (App e1 e2) a n =
    ((s1, t1, m1) := W e1 a n;
     (s2, t2, m2) := W e2 ($s1 a) m1;
     u := mgu ($ s2 t1) (t2 -> TVar m2);
     Ok ($u o $s2 o s1, $u (TVar m2), Suc m2))";


subsection {* Correctness theorem *};

theorem W_correct: "W e a n = Ok (s, t, m) ==> $ s a |- e :: t";
proof -;
  assume W_ok: "W e a n = Ok (s, t, m)";
  have "ALL a s t m n. Ok (s, t, m) = W e a n --> $ s a |- e :: t"
    (is "?P e");
  proof (induct (stripped) e);
    fix a s t m n;
    {
      fix i;
      assume "Ok (s, t, m) = W (Var i) a n";
      thus "$ s a |- Var i :: t"; by (simp split: if_splits);
    next;
      fix e; assume hyp: "?P e";
      assume "Ok (s, t, m) = W (Abs e) a n";
      then; obtain t' where "t = s n -> t'"
	  and "Ok (s, t', m) = W e (TVar n # a) (Suc n)";
	by (auto split: bind_splits);
      with hyp; show "$ s a |- Abs e :: t";
	by (force intro: has_type.Abs);
    next;
      fix e1 e2; assume hyp1: "?P e1" and hyp2: "?P e2";
      assume "Ok (s, t, m) = W (App e1 e2) a n";
      then; obtain s1 t1 n1 s2 t2 n2 u where
          s: "s = $ u o $ s2 o s1"
          and t: "t = u n2"
          and mgu_ok: "mgu ($ s2 t1) (t2 -> TVar n2) = Ok u"
          and W1_ok: "W e1 a n = Ok (s1, t1, n1)"
          and W2_ok: "W e2 ($ s1 a) n1 = Ok (s2, t2, n2)";
	by (auto split: bind_splits);
      show "$ s a |- App e1 e2 :: t";
      proof (rule has_type.App);
        from s; have s': "$ u ($ s2 ($ s1 a)) = $s a";
          by (simp add: subst_comp_tel o_def);
        show "$s a |- e1 :: $ u t2 -> t";
        proof -;
          from hyp1 W1_ok [symmetric]; have "$ s1 a |- e1 :: t1";
            by blast;
          hence "$ u ($ s2 ($ s1 a)) |- e1 :: $ u ($ s2 t1)";
            by (intro has_type_subst_closed);
          with s' t mgu_ok; show ?thesis; by simp;
        qed;
        show "$ s a |- e2 :: $ u t2";
        proof -;
          from hyp2 W2_ok [symmetric];
          have "$ s2 ($ s1 a) |- e2 :: t2"; by blast;
          hence "$ u ($ s2 ($ s1 a)) |- e2 :: $ u t2";
            by (rule has_type_subst_closed);
          with s'; show ?thesis; by simp;
        qed;
      qed;
    };
  qed;
  with W_ok [symmetric]; show ?thesis; by blast;
qed;

end;

(*  Title:      HOL/Library/Heap_Monad.thy
    Author:     John Matthews, Galois Connections; Alexander Krauss, Lukas Bulwahn & Florian Haftmann, TU Muenchen
*)

header {* A monad with a polymorphic heap and primitive reasoning infrastructure *}

theory Heap_Monad
imports Heap
begin

subsection {* The monad *}

subsubsection {* Monad construction *}

text {* Monadic heap actions either produce values
  and transform the heap, or fail *}
datatype 'a Heap = Heap "heap \<Rightarrow> ('a \<times> heap) option"

primrec execute :: "'a Heap \<Rightarrow> heap \<Rightarrow> ('a \<times> heap) option" where
  [code del]: "execute (Heap f) = f"

lemma Heap_cases [case_names succeed fail]:
  fixes f and h
  assumes succeed: "\<And>x h'. execute f h = Some (x, h') \<Longrightarrow> P"
  assumes fail: "execute f h = None \<Longrightarrow> P"
  shows P
  using assms by (cases "execute f h") auto

lemma Heap_execute [simp]:
  "Heap (execute f) = f" by (cases f) simp_all

lemma Heap_eqI:
  "(\<And>h. execute f h = execute g h) \<Longrightarrow> f = g"
    by (cases f, cases g) (auto simp: expand_fun_eq)

ML {* structure Execute_Simps = Named_Thms(
  val name = "execute_simps"
  val description = "simplification rules for execute"
) *}

setup Execute_Simps.setup

lemma execute_Let [simp, execute_simps]:
  "execute (let x = t in f x) = (let x = t in execute (f x))"
  by (simp add: Let_def)


subsubsection {* Specialised lifters *}

definition tap :: "(heap \<Rightarrow> 'a) \<Rightarrow> 'a Heap" where
  [code del]: "tap f = Heap (\<lambda>h. Some (f h, h))"

lemma execute_tap [simp, execute_simps]:
  "execute (tap f) h = Some (f h, h)"
  by (simp add: tap_def)

definition heap :: "(heap \<Rightarrow> 'a \<times> heap) \<Rightarrow> 'a Heap" where
  [code del]: "heap f = Heap (Some \<circ> f)"

lemma execute_heap [simp, execute_simps]:
  "execute (heap f) = Some \<circ> f"
  by (simp add: heap_def)

definition guard :: "(heap \<Rightarrow> bool) \<Rightarrow> (heap \<Rightarrow> 'a \<times> heap) \<Rightarrow> 'a Heap" where
  [code del]: "guard P f = Heap (\<lambda>h. if P h then Some (f h) else None)"

lemma execute_guard [execute_simps]:
  "\<not> P h \<Longrightarrow> execute (guard P f) h = None"
  "P h \<Longrightarrow> execute (guard P f) h = Some (f h)"
  by (simp_all add: guard_def)


subsubsection {* Predicate classifying successful computations *}

definition success :: "'a Heap \<Rightarrow> heap \<Rightarrow> bool" where
  "success f h \<longleftrightarrow> execute f h \<noteq> None"

lemma successI:
  "execute f h \<noteq> None \<Longrightarrow> success f h"
  by (simp add: success_def)

lemma successE:
  assumes "success f h"
  obtains r h' where "r = fst (the (execute c h))"
    and "h' = snd (the (execute c h))"
    and "execute f h \<noteq> None"
  using assms by (simp add: success_def)

ML {* structure Success_Intros = Named_Thms(
  val name = "success_intros"
  val description = "introduction rules for success"
) *}

setup Success_Intros.setup

lemma success_tapI [iff, success_intros]:
  "success (tap f) h"
  by (rule successI) simp

lemma success_heapI [iff, success_intros]:
  "success (heap f) h"
  by (rule successI) simp

lemma success_guardI [success_intros]:
  "P h \<Longrightarrow> success (guard P f) h"
  by (rule successI) (simp add: execute_guard)

lemma success_LetI [success_intros]:
  "x = t \<Longrightarrow> success (f x) h \<Longrightarrow> success (let x = t in f x) h"
  by (simp add: Let_def)

lemma success_ifI:
  "(c \<Longrightarrow> success t h) \<Longrightarrow> (\<not> c \<Longrightarrow> success e h) \<Longrightarrow>
    success (if c then t else e) h"
  by (simp add: success_def)


subsubsection {* Predicate for a simple relational calculus *}

text {*
  The @{text crel} predicate states that when a computation @{text c}
  runs with the heap @{text h} will result in return value @{text r}
  and a heap @{text "h'"}, i.e.~no exception occurs.
*}  

definition crel :: "'a Heap \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> 'a \<Rightarrow> bool" where
  crel_def: "crel c h h' r \<longleftrightarrow> Heap_Monad.execute c h = Some (r, h')"

lemma crelI:
  "Heap_Monad.execute c h = Some (r, h') \<Longrightarrow> crel c h h' r"
  by (simp add: crel_def)

lemma crelE:
  assumes "crel c h h' r"
  obtains "r = fst (the (execute c h))"
    and "h' = snd (the (execute c h))"
    and "success c h"
proof (rule that)
  from assms have *: "execute c h = Some (r, h')" by (simp add: crel_def)
  then show "success c h" by (simp add: success_def)
  from * have "fst (the (execute c h)) = r" and "snd (the (execute c h)) = h'"
    by simp_all
  then show "r = fst (the (execute c h))"
    and "h' = snd (the (execute c h))" by simp_all
qed

lemma crel_success:
  "crel c h h' r \<Longrightarrow> success c h"
  by (simp add: crel_def success_def)

lemma success_crelE:
  assumes "success c h"
  obtains r h' where "crel c h h' r"
  using assms by (auto simp add: crel_def success_def)

lemma crel_deterministic:
  assumes "crel f h h' a"
    and "crel f h h'' b"
  shows "a = b" and "h' = h''"
  using assms unfolding crel_def by auto

ML {* structure Crel_Intros = Named_Thms(
  val name = "crel_intros"
  val description = "introduction rules for crel"
) *}

ML {* structure Crel_Elims = Named_Thms(
  val name = "crel_elims"
  val description = "elimination rules for crel"
) *}

setup "Crel_Intros.setup #> Crel_Elims.setup"

lemma crel_LetI [crel_intros]:
  assumes "x = t" "crel (f x) h h' r"
  shows "crel (let x = t in f x) h h' r"
  using assms by simp

lemma crel_LetE [crel_elims]:
  assumes "crel (let x = t in f x) h h' r"
  obtains "crel (f t) h h' r"
  using assms by simp

lemma crel_ifI:
  assumes "c \<Longrightarrow> crel t h h' r"
    and "\<not> c \<Longrightarrow> crel e h h' r"
  shows "crel (if c then t else e) h h' r"
  by (cases c) (simp_all add: assms)

lemma crel_ifE:
  assumes "crel (if c then t else e) h h' r"
  obtains "c" "crel t h h' r"
    | "\<not> c" "crel e h h' r"
  using assms by (cases c) simp_all

lemma crel_tapI [crel_intros]:
  assumes "h' = h" "r = f h"
  shows "crel (tap f) h h' r"
  by (rule crelI) (simp add: assms)

lemma crel_tapE [crel_elims]:
  assumes "crel (tap f) h h' r"
  obtains "h' = h" and "r = f h"
  using assms by (rule crelE) auto

lemma crel_heapI [crel_intros]:
  assumes "h' = snd (f h)" "r = fst (f h)"
  shows "crel (heap f) h h' r"
  by (rule crelI) (simp add: assms)

lemma crel_heapE [crel_elims]:
  assumes "crel (heap f) h h' r"
  obtains "h' = snd (f h)" and "r = fst (f h)"
  using assms by (rule crelE) simp

lemma crel_guardI [crel_intros]:
  assumes "P h" "h' = snd (f h)" "r = fst (f h)"
  shows "crel (guard P f) h h' r"
  by (rule crelI) (simp add: assms execute_simps)

lemma crel_guardE [crel_elims]:
  assumes "crel (guard P f) h h' r"
  obtains "h' = snd (f h)" "r = fst (f h)" "P h"
  using assms by (rule crelE)
    (auto simp add: execute_simps elim!: successE, cases "P h", auto simp add: execute_simps)


subsubsection {* Monad combinators *}

definition return :: "'a \<Rightarrow> 'a Heap" where
  [code del]: "return x = heap (Pair x)"

lemma execute_return [simp, execute_simps]:
  "execute (return x) = Some \<circ> Pair x"
  by (simp add: return_def)

lemma success_returnI [iff, success_intros]:
  "success (return x) h"
  by (rule successI) simp

lemma crel_returnI [crel_intros]:
  "h = h' \<Longrightarrow> crel (return x) h h' x"
  by (rule crelI) simp

lemma crel_returnE [crel_elims]:
  assumes "crel (return x) h h' r"
  obtains "r = x" "h' = h"
  using assms by (rule crelE) simp

definition raise :: "string \<Rightarrow> 'a Heap" where -- {* the string is just decoration *}
  [code del]: "raise s = Heap (\<lambda>_. None)"

lemma execute_raise [simp, execute_simps]:
  "execute (raise s) = (\<lambda>_. None)"
  by (simp add: raise_def)

lemma crel_raiseE [crel_elims]:
  assumes "crel (raise x) h h' r"
  obtains "False"
  using assms by (rule crelE) (simp add: success_def)

definition bind :: "'a Heap \<Rightarrow> ('a \<Rightarrow> 'b Heap) \<Rightarrow> 'b Heap" (infixl ">>=" 54) where
  [code del]: "f >>= g = Heap (\<lambda>h. case execute f h of
                  Some (x, h') \<Rightarrow> execute (g x) h'
                | None \<Rightarrow> None)"

notation bind (infixl "\<guillemotright>=" 54)

lemma execute_bind [execute_simps]:
  "execute f h = Some (x, h') \<Longrightarrow> execute (f \<guillemotright>= g) h = execute (g x) h'"
  "execute f h = None \<Longrightarrow> execute (f \<guillemotright>= g) h = None"
  by (simp_all add: bind_def)

lemma execute_bind_success:
  "success f h \<Longrightarrow> execute (f \<guillemotright>= g) h = execute (g (fst (the (execute f h)))) (snd (the (execute f h)))"
  by (cases f h rule: Heap_cases) (auto elim!: successE simp add: bind_def)

lemma success_bind_executeI:
  "execute f h = Some (x, h') \<Longrightarrow> success (g x) h' \<Longrightarrow> success (f \<guillemotright>= g) h"
  by (auto intro!: successI elim!: successE simp add: bind_def)

lemma success_bind_crelI [success_intros]:
  "crel f h h' x \<Longrightarrow> success (g x) h' \<Longrightarrow> success (f \<guillemotright>= g) h"
  by (auto simp add: crel_def success_def bind_def)

lemma crel_bindI [crel_intros]:
  assumes "crel f h h' r" "crel (g r) h' h'' r'"
  shows "crel (f \<guillemotright>= g) h h'' r'"
  using assms
  apply (auto intro!: crelI elim!: crelE successE)
  apply (subst execute_bind, simp_all)
  done

lemma crel_bindE [crel_elims]:
  assumes "crel (f \<guillemotright>= g) h h'' r'"
  obtains h' r where "crel f h h' r" "crel (g r) h' h'' r'"
  using assms by (auto simp add: crel_def bind_def split: option.split_asm)

lemma execute_bind_eq_SomeI:
  assumes "Heap_Monad.execute f h = Some (x, h')"
    and "Heap_Monad.execute (g x) h' = Some (y, h'')"
  shows "Heap_Monad.execute (f \<guillemotright>= g) h = Some (y, h'')"
  using assms by (simp add: bind_def)

lemma return_bind [simp]: "return x \<guillemotright>= f = f x"
  by (rule Heap_eqI) (simp add: execute_bind)

lemma bind_return [simp]: "f \<guillemotright>= return = f"
  by (rule Heap_eqI) (simp add: bind_def split: option.splits)

lemma bind_bind [simp]: "(f \<guillemotright>= g) \<guillemotright>= k = f \<guillemotright>= (\<lambda>x. g x \<guillemotright>= k)"
  by (rule Heap_eqI) (simp add: bind_def split: option.splits)

lemma raise_bind [simp]: "raise e \<guillemotright>= f = raise e"
  by (rule Heap_eqI) (simp add: execute_bind)

abbreviation chain :: "'a Heap \<Rightarrow> 'b Heap \<Rightarrow> 'b Heap"  (infixl ">>" 54) where
  "f >> g \<equiv> f >>= (\<lambda>_. g)"

notation chain (infixl "\<guillemotright>" 54)


subsubsection {* do-syntax *}

text {*
  We provide a convenient do-notation for monadic expressions
  well-known from Haskell.  @{const Let} is printed
  specially in do-expressions.
*}

nonterminals do_expr

syntax
  "_do" :: "do_expr \<Rightarrow> 'a"
    ("(do (_)//done)" [12] 100)
  "_bind" :: "pttrn \<Rightarrow> 'a \<Rightarrow> do_expr \<Rightarrow> do_expr"
    ("_ <- _;//_" [1000, 13, 12] 12)
  "_chain" :: "'a \<Rightarrow> do_expr \<Rightarrow> do_expr"
    ("_;//_" [13, 12] 12)
  "_let" :: "pttrn \<Rightarrow> 'a \<Rightarrow> do_expr \<Rightarrow> do_expr"
    ("let _ = _;//_" [1000, 13, 12] 12)
  "_nil" :: "'a \<Rightarrow> do_expr"
    ("_" [12] 12)

syntax (xsymbols)
  "_bind" :: "pttrn \<Rightarrow> 'a \<Rightarrow> do_expr \<Rightarrow> do_expr"
    ("_ \<leftarrow> _;//_" [1000, 13, 12] 12)

translations
  "_do f" => "f"
  "_bind x f g" => "f \<guillemotright>= (\<lambda>x. g)"
  "_chain f g" => "f \<guillemotright> g"
  "_let x t f" => "CONST Let t (\<lambda>x. f)"
  "_nil f" => "f"

print_translation {*
let
  fun dest_abs_eta (Abs (abs as (_, ty, _))) =
        let
          val (v, t) = Syntax.variant_abs abs;
        in (Free (v, ty), t) end
    | dest_abs_eta t =
        let
          val (v, t) = Syntax.variant_abs ("", dummyT, t $ Bound 0);
        in (Free (v, dummyT), t) end;
  fun unfold_monad (Const (@{const_syntax bind}, _) $ f $ g) =
        let
          val (v, g') = dest_abs_eta g;
          val vs = fold_aterms (fn Free (v, _) => insert (op =) v | _ => I) v [];
          val v_used = fold_aterms
            (fn Free (w, _) => (fn s => s orelse member (op =) vs w) | _ => I) g' false;
        in if v_used then
          Const (@{syntax_const "_bind"}, dummyT) $ v $ f $ unfold_monad g'
        else
          Const (@{syntax_const "_chain"}, dummyT) $ f $ unfold_monad g'
        end
    | unfold_monad (Const (@{const_syntax chain}, _) $ f $ g) =
        Const (@{syntax_const "_chain"}, dummyT) $ f $ unfold_monad g
    | unfold_monad (Const (@{const_syntax Let}, _) $ f $ g) =
        let
          val (v, g') = dest_abs_eta g;
        in Const (@{syntax_const "_let"}, dummyT) $ v $ f $ unfold_monad g' end
    | unfold_monad (Const (@{const_syntax Pair}, _) $ f) =
        Const (@{const_syntax return}, dummyT) $ f
    | unfold_monad f = f;
  fun contains_bind (Const (@{const_syntax bind}, _) $ _ $ _) = true
    | contains_bind (Const (@{const_syntax Let}, _) $ _ $ Abs (_, _, t)) =
        contains_bind t;
  fun bind_monad_tr' (f::g::ts) = list_comb
    (Const (@{syntax_const "_do"}, dummyT) $
      unfold_monad (Const (@{const_syntax bind}, dummyT) $ f $ g), ts);
  fun Let_monad_tr' (f :: (g as Abs (_, _, g')) :: ts) =
    if contains_bind g' then list_comb
      (Const (@{syntax_const "_do"}, dummyT) $
        unfold_monad (Const (@{const_syntax Let}, dummyT) $ f $ g), ts)
    else raise Match;
in
 [(@{const_syntax bind}, bind_monad_tr'),
  (@{const_syntax Let}, Let_monad_tr')]
end;
*}


subsection {* Generic combinators *}

subsubsection {* Assertions *}

definition assert :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a Heap" where
  "assert P x = (if P x then return x else raise ''assert'')"

lemma execute_assert [execute_simps]:
  "P x \<Longrightarrow> execute (assert P x) h = Some (x, h)"
  "\<not> P x \<Longrightarrow> execute (assert P x) h = None"
  by (simp_all add: assert_def)

lemma success_assertI [success_intros]:
  "P x \<Longrightarrow> success (assert P x) h"
  by (rule successI) (simp add: execute_assert)

lemma crel_assertI [crel_intros]:
  "P x \<Longrightarrow> h' = h \<Longrightarrow> r = x \<Longrightarrow> crel (assert P x) h h' r"
  by (rule crelI) (simp add: execute_assert)
 
lemma crel_assertE [crel_elims]:
  assumes "crel (assert P x) h h' r"
  obtains "P x" "r = x" "h' = h"
  using assms by (rule crelE) (cases "P x", simp_all add: execute_assert success_def)

lemma assert_cong [fundef_cong]:
  assumes "P = P'"
  assumes "\<And>x. P' x \<Longrightarrow> f x = f' x"
  shows "(assert P x >>= f) = (assert P' x >>= f')"
  by (rule Heap_eqI) (insert assms, simp add: assert_def)


subsubsection {* Plain lifting *}

definition lift :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b Heap" where
  "lift f = return o f"

lemma lift_collapse [simp]:
  "lift f x = return (f x)"
  by (simp add: lift_def)

lemma bind_lift:
  "(f \<guillemotright>= lift g) = (f \<guillemotright>= (\<lambda>x. return (g x)))"
  by (simp add: lift_def comp_def)


subsubsection {* Iteration -- warning: this is rarely useful! *}

primrec fold_map :: "('a \<Rightarrow> 'b Heap) \<Rightarrow> 'a list \<Rightarrow> 'b list Heap" where
  "fold_map f [] = return []"
| "fold_map f (x # xs) = do
     y \<leftarrow> f x;
     ys \<leftarrow> fold_map f xs;
     return (y # ys)
   done"

lemma fold_map_append:
  "fold_map f (xs @ ys) = fold_map f xs \<guillemotright>= (\<lambda>xs. fold_map f ys \<guillemotright>= (\<lambda>ys. return (xs @ ys)))"
  by (induct xs) simp_all

lemma execute_fold_map_unchanged_heap [execute_simps]:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> \<exists>y. execute (f x) h = Some (y, h)"
  shows "execute (fold_map f xs) h =
    Some (List.map (\<lambda>x. fst (the (execute (f x) h))) xs, h)"
using assms proof (induct xs)
  case Nil show ?case by simp
next
  case (Cons x xs)
  from Cons.prems obtain y
    where y: "execute (f x) h = Some (y, h)" by auto
  moreover from Cons.prems Cons.hyps have "execute (fold_map f xs) h =
    Some (map (\<lambda>x. fst (the (execute (f x) h))) xs, h)" by auto
  ultimately show ?case by (simp, simp only: execute_bind(1), simp)
qed

subsection {* Code generator setup *}

subsubsection {* Logical intermediate layer *}

primrec raise' :: "String.literal \<Rightarrow> 'a Heap" where
  [code del, code_post]: "raise' (STR s) = raise s"

lemma raise_raise' [code_inline]:
  "raise s = raise' (STR s)"
  by simp

code_datatype raise' -- {* avoid @{const "Heap"} formally *}


subsubsection {* SML and OCaml *}

code_type Heap (SML "unit/ ->/ _")
code_const "op \<guillemotright>=" (SML "!(fn/ f'_/ =>/ fn/ ()/ =>/ f'_/ (_/ ())/ ())")
code_const return (SML "!(fn/ ()/ =>/ _)")
code_const Heap_Monad.raise' (SML "!(raise/ Fail/ _)")

code_type Heap (OCaml "unit/ ->/ _")
code_const "op \<guillemotright>=" (OCaml "!(fun/ f'_/ ()/ ->/ f'_/ (_/ ())/ ())")
code_const return (OCaml "!(fun/ ()/ ->/ _)")
code_const Heap_Monad.raise' (OCaml "failwith/ _")

setup {*

let

open Code_Thingol;

fun imp_program naming =

  let
    fun is_const c = case lookup_const naming c
     of SOME c' => (fn c'' => c' = c'')
      | NONE => K false;
    val is_bind = is_const @{const_name bind};
    val is_return = is_const @{const_name return};
    val dummy_name = "";
    val dummy_type = ITyVar dummy_name;
    val dummy_case_term = IVar NONE;
    (*assumption: dummy values are not relevant for serialization*)
    val unitt = case lookup_const naming @{const_name Unity}
     of SOME unit' => IConst (unit', (([], []), []))
      | NONE => error ("Must include " ^ @{const_name Unity} ^ " in generated constants.");
    fun dest_abs ((v, ty) `|=> t, _) = ((v, ty), t)
      | dest_abs (t, ty) =
          let
            val vs = fold_varnames cons t [];
            val v = Name.variant vs "x";
            val ty' = (hd o fst o unfold_fun) ty;
          in ((SOME v, ty'), t `$ IVar (SOME v)) end;
    fun force (t as IConst (c, _) `$ t') = if is_return c
          then t' else t `$ unitt
      | force t = t `$ unitt;
    fun tr_bind' [(t1, _), (t2, ty2)] =
      let
        val ((v, ty), t) = dest_abs (t2, ty2);
      in ICase (((force t1, ty), [(IVar v, tr_bind'' t)]), dummy_case_term) end
    and tr_bind'' t = case unfold_app t
         of (IConst (c, (_, ty1 :: ty2 :: _)), [x1, x2]) => if is_bind c
              then tr_bind' [(x1, ty1), (x2, ty2)]
              else force t
          | _ => force t;
    fun imp_monad_bind'' ts = (SOME dummy_name, dummy_type) `|=> ICase (((IVar (SOME dummy_name), dummy_type),
      [(unitt, tr_bind' ts)]), dummy_case_term)
    and imp_monad_bind' (const as (c, (_, tys))) ts = if is_bind c then case (ts, tys)
       of ([t1, t2], ty1 :: ty2 :: _) => imp_monad_bind'' [(t1, ty1), (t2, ty2)]
        | ([t1, t2, t3], ty1 :: ty2 :: _) => imp_monad_bind'' [(t1, ty1), (t2, ty2)] `$ t3
        | (ts, _) => imp_monad_bind (eta_expand 2 (const, ts))
      else IConst const `$$ map imp_monad_bind ts
    and imp_monad_bind (IConst const) = imp_monad_bind' const []
      | imp_monad_bind (t as IVar _) = t
      | imp_monad_bind (t as _ `$ _) = (case unfold_app t
         of (IConst const, ts) => imp_monad_bind' const ts
          | (t, ts) => imp_monad_bind t `$$ map imp_monad_bind ts)
      | imp_monad_bind (v_ty `|=> t) = v_ty `|=> imp_monad_bind t
      | imp_monad_bind (ICase (((t, ty), pats), t0)) = ICase
          (((imp_monad_bind t, ty),
            (map o pairself) imp_monad_bind pats),
              imp_monad_bind t0);

  in (Graph.map_nodes o map_terms_stmt) imp_monad_bind end;

in

Code_Target.extend_target ("SML_imp", ("SML", imp_program))
#> Code_Target.extend_target ("OCaml_imp", ("OCaml", imp_program))

end

*}


subsubsection {* Haskell *}

text {* Adaption layer *}

code_include Haskell "Heap"
{*import qualified Control.Monad;
import qualified Control.Monad.ST;
import qualified Data.STRef;
import qualified Data.Array.ST;

type RealWorld = Control.Monad.ST.RealWorld;
type ST s a = Control.Monad.ST.ST s a;
type STRef s a = Data.STRef.STRef s a;
type STArray s a = Data.Array.ST.STArray s Int a;

newSTRef = Data.STRef.newSTRef;
readSTRef = Data.STRef.readSTRef;
writeSTRef = Data.STRef.writeSTRef;

newArray :: (Int, Int) -> a -> ST s (STArray s a);
newArray = Data.Array.ST.newArray;

newListArray :: (Int, Int) -> [a] -> ST s (STArray s a);
newListArray = Data.Array.ST.newListArray;

lengthArray :: STArray s a -> ST s Int;
lengthArray a = Control.Monad.liftM snd (Data.Array.ST.getBounds a);

readArray :: STArray s a -> Int -> ST s a;
readArray = Data.Array.ST.readArray;

writeArray :: STArray s a -> Int -> a -> ST s ();
writeArray = Data.Array.ST.writeArray;*}

code_reserved Haskell Heap

text {* Monad *}

code_type Heap (Haskell "Heap.ST/ Heap.RealWorld/ _")
code_monad "op \<guillemotright>=" Haskell
code_const return (Haskell "return")
code_const Heap_Monad.raise' (Haskell "error/ _")

hide_const (open) Heap heap guard raise' fold_map

end

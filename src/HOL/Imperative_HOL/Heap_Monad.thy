(*  Title:      HOL/Library/Heap_Monad.thy
    Author:     John Matthews, Galois Connections; Alexander Krauss, Lukas Bulwahn & Florian Haftmann, TU Muenchen
*)

header {* A monad with a polymorphic heap *}

theory Heap_Monad
imports Heap
begin

subsection {* The monad *}

subsubsection {* Monad combinators *}

text {* Monadic heap actions either produce values
  and transform the heap, or fail *}
datatype 'a Heap = Heap "heap \<Rightarrow> ('a \<times> heap) option"

primrec execute :: "'a Heap \<Rightarrow> heap \<Rightarrow> ('a \<times> heap) option" where
  [code del]: "execute (Heap f) = f"

lemma Heap_execute [simp]:
  "Heap (execute f) = f" by (cases f) simp_all

lemma Heap_eqI:
  "(\<And>h. execute f h = execute g h) \<Longrightarrow> f = g"
    by (cases f, cases g) (auto simp: expand_fun_eq)

lemma Heap_eqI':
  "(\<And>h. (\<lambda>x. execute (f x) h) = (\<lambda>y. execute (g y) h)) \<Longrightarrow> f = g"
    by (auto simp: expand_fun_eq intro: Heap_eqI)

definition heap :: "(heap \<Rightarrow> 'a \<times> heap) \<Rightarrow> 'a Heap" where
  [code del]: "heap f = Heap (Some \<circ> f)"

lemma execute_heap [simp]:
  "execute (heap f) = Some \<circ> f"
  by (simp add: heap_def)

lemma heap_cases [case_names succeed fail]:
  fixes f and h
  assumes succeed: "\<And>x h'. execute f h = Some (x, h') \<Longrightarrow> P"
  assumes fail: "execute f h = None \<Longrightarrow> P"
  shows P
  using assms by (cases "execute f h") auto

definition return :: "'a \<Rightarrow> 'a Heap" where
  [code del]: "return x = heap (Pair x)"

lemma execute_return [simp]:
  "execute (return x) = Some \<circ> Pair x"
  by (simp add: return_def)

definition raise :: "string \<Rightarrow> 'a Heap" where -- {* the string is just decoration *}
  [code del]: "raise s = Heap (\<lambda>_. None)"

lemma execute_raise [simp]:
  "execute (raise s) = (\<lambda>_. None)"
  by (simp add: raise_def)

definition bindM :: "'a Heap \<Rightarrow> ('a \<Rightarrow> 'b Heap) \<Rightarrow> 'b Heap" (infixl ">>=" 54) where
  [code del]: "f >>= g = Heap (\<lambda>h. case execute f h of
                  Some (x, h') \<Rightarrow> execute (g x) h'
                | None \<Rightarrow> None)"

notation bindM (infixl "\<guillemotright>=" 54)

lemma execute_bind [simp]:
  "execute f h = Some (x, h') \<Longrightarrow> execute (f \<guillemotright>= g) h = execute (g x) h'"
  "execute f h = None \<Longrightarrow> execute (f \<guillemotright>= g) h = None"
  by (simp_all add: bindM_def)

lemma execute_bind_heap [simp]:
  "execute (heap f \<guillemotright>= g) h = execute (g (fst (f h))) (snd (f h))"
  by (simp add: bindM_def split_def)
  
lemma return_bind [simp]: "return x \<guillemotright>= f = f x"
  by (rule Heap_eqI) simp

lemma bind_return [simp]: "f \<guillemotright>= return = f"
  by (rule Heap_eqI) (simp add: bindM_def split: option.splits)

lemma bind_bind [simp]: "(f \<guillemotright>= g) \<guillemotright>= k = f \<guillemotright>= (\<lambda>x. g x \<guillemotright>= k)"
  by (rule Heap_eqI) (simp add: bindM_def split: option.splits)

lemma raise_bind [simp]: "raise e \<guillemotright>= f = raise e"
  by (rule Heap_eqI) simp

abbreviation chainM :: "'a Heap \<Rightarrow> 'b Heap \<Rightarrow> 'b Heap"  (infixl ">>" 54) where
  "f >> g \<equiv> f >>= (\<lambda>_. g)"

notation chainM (infixl "\<guillemotright>" 54)


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
  "_bindM" :: "pttrn \<Rightarrow> 'a \<Rightarrow> do_expr \<Rightarrow> do_expr"
    ("_ <- _;//_" [1000, 13, 12] 12)
  "_chainM" :: "'a \<Rightarrow> do_expr \<Rightarrow> do_expr"
    ("_;//_" [13, 12] 12)
  "_let" :: "pttrn \<Rightarrow> 'a \<Rightarrow> do_expr \<Rightarrow> do_expr"
    ("let _ = _;//_" [1000, 13, 12] 12)
  "_nil" :: "'a \<Rightarrow> do_expr"
    ("_" [12] 12)

syntax (xsymbols)
  "_bindM" :: "pttrn \<Rightarrow> 'a \<Rightarrow> do_expr \<Rightarrow> do_expr"
    ("_ \<leftarrow> _;//_" [1000, 13, 12] 12)

translations
  "_do f" => "f"
  "_bindM x f g" => "f \<guillemotright>= (\<lambda>x. g)"
  "_chainM f g" => "f \<guillemotright> g"
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
  fun unfold_monad (Const (@{const_syntax bindM}, _) $ f $ g) =
        let
          val (v, g') = dest_abs_eta g;
          val vs = fold_aterms (fn Free (v, _) => insert (op =) v | _ => I) v [];
          val v_used = fold_aterms
            (fn Free (w, _) => (fn s => s orelse member (op =) vs w) | _ => I) g' false;
        in if v_used then
          Const (@{syntax_const "_bindM"}, dummyT) $ v $ f $ unfold_monad g'
        else
          Const (@{syntax_const "_chainM"}, dummyT) $ f $ unfold_monad g'
        end
    | unfold_monad (Const (@{const_syntax chainM}, _) $ f $ g) =
        Const (@{syntax_const "_chainM"}, dummyT) $ f $ unfold_monad g
    | unfold_monad (Const (@{const_syntax Let}, _) $ f $ g) =
        let
          val (v, g') = dest_abs_eta g;
        in Const (@{syntax_const "_let"}, dummyT) $ v $ f $ unfold_monad g' end
    | unfold_monad (Const (@{const_syntax Pair}, _) $ f) =
        Const (@{const_syntax return}, dummyT) $ f
    | unfold_monad f = f;
  fun contains_bindM (Const (@{const_syntax bindM}, _) $ _ $ _) = true
    | contains_bindM (Const (@{const_syntax Let}, _) $ _ $ Abs (_, _, t)) =
        contains_bindM t;
  fun bindM_monad_tr' (f::g::ts) = list_comb
    (Const (@{syntax_const "_do"}, dummyT) $
      unfold_monad (Const (@{const_syntax bindM}, dummyT) $ f $ g), ts);
  fun Let_monad_tr' (f :: (g as Abs (_, _, g')) :: ts) =
    if contains_bindM g' then list_comb
      (Const (@{syntax_const "_do"}, dummyT) $
        unfold_monad (Const (@{const_syntax Let}, dummyT) $ f $ g), ts)
    else raise Match;
in
 [(@{const_syntax bindM}, bindM_monad_tr'),
  (@{const_syntax Let}, Let_monad_tr')]
end;
*}


subsection {* Monad properties *}

subsection {* Generic combinators *}

definition assert :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a Heap" where
  "assert P x = (if P x then return x else raise ''assert'')"

lemma assert_cong [fundef_cong]:
  assumes "P = P'"
  assumes "\<And>x. P' x \<Longrightarrow> f x = f' x"
  shows "(assert P x >>= f) = (assert P' x >>= f')"
  using assms by (auto simp add: assert_def return_bind raise_bind)

definition liftM :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b Heap" where
  "liftM f = return o f"

lemma liftM_collapse [simp]:
  "liftM f x = return (f x)"
  by (simp add: liftM_def)

lemma bind_liftM:
  "(f \<guillemotright>= liftM g) = (f \<guillemotright>= (\<lambda>x. return (g x)))"
  by (simp add: liftM_def comp_def)

primrec mapM :: "('a \<Rightarrow> 'b Heap) \<Rightarrow> 'a list \<Rightarrow> 'b list Heap" where
  "mapM f [] = return []"
| "mapM f (x#xs) = do
     y \<leftarrow> f x;
     ys \<leftarrow> mapM f xs;
     return (y # ys)
   done"


subsubsection {* A monadic combinator for simple recursive functions *}

text {* Using a locale to fix arguments f and g of MREC *}

locale mrec =
  fixes f :: "'a \<Rightarrow> ('b + 'a) Heap"
  and g :: "'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b Heap"
begin

function (default "\<lambda>(x, h). None") mrec :: "'a \<Rightarrow> heap \<Rightarrow> ('b \<times> heap) option" where
  "mrec x h = (case execute (f x) h of
     Some (Inl r, h') \<Rightarrow> Some (r, h')
   | Some (Inr s, h') \<Rightarrow> (case mrec s h' of
             Some (z, h'') \<Rightarrow> execute (g x s z) h''
           | None \<Rightarrow> None)
   | None \<Rightarrow> None)"
by auto

lemma graph_implies_dom:
  "mrec_graph x y \<Longrightarrow> mrec_dom x"
apply (induct rule:mrec_graph.induct) 
apply (rule accpI)
apply (erule mrec_rel.cases)
by simp

lemma mrec_default: "\<not> mrec_dom (x, h) \<Longrightarrow> mrec x h = None"
  unfolding mrec_def 
  by (rule fundef_default_value[OF mrec_sumC_def graph_implies_dom, of _ _ "(x, h)", simplified])

lemma mrec_di_reverse: 
  assumes "\<not> mrec_dom (x, h)"
  shows "
   (case execute (f x) h of
     Some (Inl r, h') \<Rightarrow> False
   | Some (Inr s, h') \<Rightarrow> \<not> mrec_dom (s, h')
   | None \<Rightarrow> False
   )" 
using assms apply (auto split: option.split sum.split)
apply (rule ccontr)
apply (erule notE, rule accpI, elim mrec_rel.cases, auto)+
done

lemma mrec_rule:
  "mrec x h = 
   (case execute (f x) h of
     Some (Inl r, h') \<Rightarrow> Some (r, h')
   | Some (Inr s, h') \<Rightarrow> 
          (case mrec s h' of
             Some (z, h'') \<Rightarrow> execute (g x s z) h''
           | None \<Rightarrow> None)
   | None \<Rightarrow> None
   )"
apply (cases "mrec_dom (x,h)", simp)
apply (frule mrec_default)
apply (frule mrec_di_reverse, simp)
by (auto split: sum.split option.split simp: mrec_default)

definition
  "MREC x = Heap (mrec x)"

lemma MREC_rule:
  "MREC x = 
  (do y \<leftarrow> f x;
                (case y of 
                Inl r \<Rightarrow> return r
              | Inr s \<Rightarrow> 
                do z \<leftarrow> MREC s ;
                   g x s z
                done) done)"
  unfolding MREC_def
  unfolding bindM_def return_def
  apply simp
  apply (rule ext)
  apply (unfold mrec_rule[of x])
  by (auto split: option.splits prod.splits sum.splits)

lemma MREC_pinduct:
  assumes "execute (MREC x) h = Some (r, h')"
  assumes non_rec_case: "\<And> x h h' r. execute (f x) h = Some (Inl r, h') \<Longrightarrow> P x h h' r"
  assumes rec_case: "\<And> x h h1 h2 h' s z r. execute (f x) h = Some (Inr s, h1) \<Longrightarrow> execute (MREC s) h1 = Some (z, h2) \<Longrightarrow> P s h1 h2 z
    \<Longrightarrow> execute (g x s z) h2 = Some (r, h') \<Longrightarrow> P x h h' r"
  shows "P x h h' r"
proof -
  from assms(1) have mrec: "mrec x h = Some (r, h')"
    unfolding MREC_def execute.simps .
  from mrec have dom: "mrec_dom (x, h)"
    apply -
    apply (rule ccontr)
    apply (drule mrec_default) by auto
  from mrec have h'_r: "h' = snd (the (mrec x h))" "r = fst (the (mrec x h))"
    by auto
  from mrec have "P x h (snd (the (mrec x h))) (fst (the (mrec x h)))"
  proof (induct arbitrary: r h' rule: mrec.pinduct[OF dom])
    case (1 x h)
    obtain rr h' where "the (mrec x h) = (rr, h')" by fastsimp
    show ?case
    proof (cases "execute (f x) h")
      case (Some result)
      then obtain a h1 where exec_f: "execute (f x) h = Some (a, h1)" by fastsimp
      note Inl' = this
      show ?thesis
      proof (cases a)
        case (Inl aa)
        from this Inl' 1(1) exec_f mrec non_rec_case show ?thesis
          by auto
      next
        case (Inr b)
        note Inr' = this
        show ?thesis
        proof (cases "mrec b h1")
          case (Some result)
          then obtain aaa h2 where mrec_rec: "mrec b h1 = Some (aaa, h2)" by fastsimp
          moreover from this have "P b h1 (snd (the (mrec b h1))) (fst (the (mrec b h1)))"
            apply (intro 1(2))
            apply (auto simp add: Inr Inl')
            done
          moreover note mrec mrec_rec exec_f Inl' Inr' 1(1) 1(3)
          ultimately show ?thesis
            apply auto
            apply (rule rec_case)
            apply auto
            unfolding MREC_def by auto
        next
          case None
          from this 1(1) exec_f mrec Inr' 1(3) show ?thesis by auto
        qed
      qed
    next
      case None
      from this 1(1) mrec 1(3) show ?thesis by simp
    qed
  qed
  from this h'_r show ?thesis by simp
qed

end

text {* Providing global versions of the constant and the theorems *}

abbreviation "MREC == mrec.MREC"
lemmas MREC_rule = mrec.MREC_rule
lemmas MREC_pinduct = mrec.MREC_pinduct


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

code_type Heap (OCaml "_")
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
    val is_bindM = is_const @{const_name bindM};
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
         of (IConst (c, (_, ty1 :: ty2 :: _)), [x1, x2]) => if is_bindM c
              then tr_bind' [(x1, ty1), (x2, ty2)]
              else force t
          | _ => force t;
    fun imp_monad_bind'' ts = (SOME dummy_name, dummy_type) `|=> ICase (((IVar (SOME dummy_name), dummy_type),
      [(unitt, tr_bind' ts)]), dummy_case_term)
    and imp_monad_bind' (const as (c, (_, tys))) ts = if is_bindM c then case (ts, tys)
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

hide_const (open) Heap heap execute raise'

end

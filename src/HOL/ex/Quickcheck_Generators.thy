(* Author: Florian Haftmann, TU Muenchen *)

header {* Experimental counterexample generators *}

theory Quickcheck_Generators
imports Quickcheck State_Monad
begin

subsection {* Datatypes *}

definition collapse :: "('a \<Rightarrow> ('a \<Rightarrow> 'b \<times> 'a) \<times> 'a) \<Rightarrow> 'a \<Rightarrow> 'b \<times> 'a" where
  "collapse f = (do g \<leftarrow> f; g done)"

lemma random'_if:
  fixes random' :: "code_numeral \<Rightarrow> code_numeral \<Rightarrow> Random.seed \<Rightarrow> ('a \<times> (unit \<Rightarrow> term)) \<times> Random.seed"
  assumes "random' 0 j = (\<lambda>s. undefined)"
    and "\<And>i. random' (Suc_code_numeral i) j = rhs2 i"
  shows "random' i j s = (if i = 0 then undefined else rhs2 (i - 1) s)"
  by (cases i rule: code_numeral.exhaust) (insert assms, simp_all)

setup {*
let
  fun liftT T sT = sT --> HOLogic.mk_prodT (T, sT);
  fun scomp T1 T2 sT f g = Const (@{const_name scomp},
    liftT T1 sT --> (T1 --> liftT T2 sT) --> liftT T2 sT) $ f $ g;
  exception REC of string;
  exception TYP of string;
  fun mk_collapse thy ty = Sign.mk_const thy
    (@{const_name collapse}, [@{typ Random.seed}, ty]);
  fun term_ty ty = HOLogic.mk_prodT (ty, @{typ "unit \<Rightarrow> term"});
  fun mk_split thy ty ty' = Sign.mk_const thy
    (@{const_name split}, [ty, @{typ "unit \<Rightarrow> term"}, liftT (term_ty ty') @{typ Random.seed}]);
  fun mk_scomp_split thy ty ty' t t' =
    scomp (term_ty ty) (term_ty ty') @{typ Random.seed} t
      (mk_split thy ty ty' $ Abs ("", ty, Abs ("", @{typ "unit \<Rightarrow> term"}, t')))
  fun mk_cons thy this_ty (c, args) =
    let
      val tys = map (fst o fst) args;
      val c_ty = tys ---> this_ty;
      val c = Const (c, tys ---> this_ty);
      val t_indices = map (curry ( op * ) 2) (length tys - 1 downto 0);
      val c_indices = map (curry ( op + ) 1) t_indices;
      val c_t = list_comb (c, map Bound c_indices);
      val t_t = Abs ("", @{typ unit}, HOLogic.reflect_term
        (list_comb (c, map (fn k => Bound (k + 1)) t_indices))
        |> map_aterms (fn t as Bound _ => t $ @{term "()"} | t => t));
      val return = HOLogic.mk_return (term_ty this_ty) @{typ Random.seed}
        (HOLogic.mk_prod (c_t, t_t));
      val t = fold_rev (fn ((ty, _), random) =>
        mk_scomp_split thy ty this_ty random)
          args return;
      val is_rec = exists (snd o fst) args;
    in (is_rec, t) end;
  fun mk_conss thy ty [] = NONE
    | mk_conss thy ty [(_, t)] = SOME t
    | mk_conss thy ty ts = SOME (mk_collapse thy (term_ty ty) $
          (Sign.mk_const thy (@{const_name Random.select}, [liftT (term_ty ty) @{typ Random.seed}]) $
            HOLogic.mk_list (liftT (term_ty ty) @{typ Random.seed}) (map snd ts)));
  fun mk_clauses thy ty (tyco, (ts_rec, ts_atom)) = 
    let
      val SOME t_atom = mk_conss thy ty ts_atom;
    in case mk_conss thy ty ts_rec
     of SOME t_rec => mk_collapse thy (term_ty ty) $
          (Sign.mk_const thy (@{const_name Random.select_default}, [liftT (term_ty ty) @{typ Random.seed}]) $
             @{term "i\<Colon>code_numeral"} $ t_rec $ t_atom)
      | NONE => t_atom
    end;
  fun mk_random_eqs thy vs tycos =
    let
      val this_ty = Type (hd tycos, map TFree vs);
      val this_ty' = liftT (term_ty this_ty) @{typ Random.seed};
      val random_name = Long_Name.base_name @{const_name random};
      val random'_name = random_name ^ "_" ^ Class.type_name (hd tycos) ^ "'";
      fun random ty = Sign.mk_const thy (@{const_name random}, [ty]);
      val random' = Free (random'_name,
        @{typ code_numeral} --> @{typ code_numeral} --> this_ty');
      fun atom ty = if Sign.of_sort thy (ty, @{sort random})
        then ((ty, false), random ty $ @{term "j\<Colon>code_numeral"})
        else raise TYP
          ("Will not generate random elements for type(s) " ^ quote (hd tycos));
      fun dtyp tyco = ((this_ty, true), random' $ @{term "i\<Colon>code_numeral"} $ @{term "j\<Colon>code_numeral"});
      fun rtyp (tyco, Ts) _ = raise REC
        ("Will not generate random elements for mutual recursive type " ^ quote (hd tycos));
      val rhss = DatatypePackage.construction_interpretation thy
            { atom = atom, dtyp = dtyp, rtyp = rtyp } vs tycos
        |> fst
        |> (map o apsnd o map) (mk_cons thy this_ty) 
        |> (map o apsnd) (List.partition fst)
        |> map (mk_clauses thy this_ty)
      val eqss = map ((apsnd o map) (HOLogic.mk_Trueprop o HOLogic.mk_eq) o (fn rhs => ((this_ty, random'), [
          (random' $ @{term "0\<Colon>code_numeral"} $ @{term "j\<Colon>code_numeral"}, Abs ("s", @{typ Random.seed},
            Const (@{const_name undefined}, HOLogic.mk_prodT (term_ty this_ty, @{typ Random.seed})))),
          (random' $ @{term "Suc_code_numeral i"} $ @{term "j\<Colon>code_numeral"}, rhs)
        ]))) rhss;
    in eqss end;
  fun random_inst [tyco] thy =
        let
          val (raw_vs, _) = DatatypePackage.the_datatype_spec thy tyco;
          val vs = (map o apsnd)
            (curry (Sorts.inter_sort (Sign.classes_of thy)) @{sort random}) raw_vs;
          val ((this_ty, random'), eqs') = singleton (mk_random_eqs thy vs) tyco;
          val eq = (HOLogic.mk_Trueprop o HOLogic.mk_eq)
            (Sign.mk_const thy (@{const_name random}, [this_ty]) $ @{term "i\<Colon>code_numeral"},
               random' $ @{term "max (i\<Colon>code_numeral) 1"} $ @{term "i\<Colon>code_numeral"})
          val del_func = Attrib.internal (fn _ => Thm.declaration_attribute
            (fn thm => Context.mapping (Code.del_eqn thm) I));
          fun add_code simps lthy =
            let
              val thy = ProofContext.theory_of lthy;
              val thm = @{thm random'_if}
                |> Drule.instantiate' [SOME (Thm.ctyp_of thy this_ty)] [SOME (Thm.cterm_of thy random')]
                |> (fn thm => thm OF simps)
                |> singleton (ProofContext.export lthy (ProofContext.init thy));
              val c = (fst o dest_Const o fst o strip_comb o fst
                o HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of) thm;
            in
              lthy
              |> LocalTheory.theory (Code.del_eqns c
                   #> PureThy.add_thm ((Binding.name (fst (dest_Free random') ^ "_code"), thm), [Thm.kind_internal])
                   #-> Code.add_eqn)
            end;
        in
          thy
          |> TheoryTarget.instantiation ([tyco], vs, @{sort random})
          |> PrimrecPackage.add_primrec
               [(Binding.name (fst (dest_Free random')), SOME (snd (dest_Free random')), NoSyn)]
                 (map (fn eq => ((Binding.empty, [del_func]), eq)) eqs')
          |-> add_code
          |> `(fn lthy => Syntax.check_term lthy eq)
          |-> (fn eq => Specification.definition (NONE, (Attrib.empty_binding, eq)))
          |> snd
          |> Class.prove_instantiation_instance (K (Class.intro_classes_tac []))
          |> LocalTheory.exit_global
        end
    | random_inst tycos thy = raise REC
        ("Will not generate random elements for mutual recursive type(s) " ^ commas (map quote tycos));
  fun add_random_inst [@{type_name bool}] thy = thy
    | add_random_inst [@{type_name nat}] thy = thy
    | add_random_inst tycos thy = random_inst tycos thy
        handle REC msg => (warning msg; thy)
             | TYP msg => (warning msg; thy)
in DatatypePackage.interpretation add_random_inst end
*}


subsection {* Examples *}

theorem "map g (map f xs) = map (g o f) xs"
  quickcheck [generator = code]
  by (induct xs) simp_all

theorem "map g (map f xs) = map (f o g) xs"
  quickcheck [generator = code]
  oops

theorem "rev (xs @ ys) = rev ys @ rev xs"
  quickcheck [generator = code]
  by simp

theorem "rev (xs @ ys) = rev xs @ rev ys"
  quickcheck [generator = code]
  oops

theorem "rev (rev xs) = xs"
  quickcheck [generator = code]
  by simp

theorem "rev xs = xs"
  quickcheck [generator = code]
  oops

primrec app :: "('a \<Rightarrow> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "app [] x = x"
  | "app (f # fs) x = app fs (f x)"

lemma "app (fs @ gs) x = app gs (app fs x)"
  quickcheck [generator = code]
  by (induct fs arbitrary: x) simp_all

lemma "app (fs @ gs) x = app fs (app gs x)"
  quickcheck [generator = code]
  oops

primrec occurs :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "occurs a [] = 0"
  | "occurs a (x#xs) = (if (x=a) then Suc(occurs a xs) else occurs a xs)"

primrec del1 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "del1 a [] = []"
  | "del1 a (x#xs) = (if (x=a) then xs else (x#del1 a xs))"

lemma "Suc (occurs a (del1 a xs)) = occurs a xs"
  -- {* Wrong. Precondition needed.*}
  quickcheck [generator = code]
  oops

lemma "xs ~= [] \<longrightarrow> Suc (occurs a (del1 a xs)) = occurs a xs"
  quickcheck [generator = code]
    -- {* Also wrong.*}
  oops

lemma "0 < occurs a xs \<longrightarrow> Suc (occurs a (del1 a xs)) = occurs a xs"
  quickcheck [generator = code]
  by (induct xs) auto

primrec replace :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "replace a b [] = []"
  | "replace a b (x#xs) = (if (x=a) then (b#(replace a b xs)) 
                            else (x#(replace a b xs)))"

lemma "occurs a xs = occurs b (replace a b xs)"
  quickcheck [generator = code]
  -- {* Wrong. Precondition needed.*}
  oops

lemma "occurs b xs = 0 \<or> a=b \<longrightarrow> occurs a xs = occurs b (replace a b xs)"
  quickcheck [generator = code]
  by (induct xs) simp_all


subsection {* Trees *}

datatype 'a tree = Twig |  Leaf 'a | Branch "'a tree" "'a tree"

primrec leaves :: "'a tree \<Rightarrow> 'a list" where
  "leaves Twig = []"
  | "leaves (Leaf a) = [a]"
  | "leaves (Branch l r) = (leaves l) @ (leaves r)"

primrec plant :: "'a list \<Rightarrow> 'a tree" where
  "plant [] = Twig "
  | "plant (x#xs) = Branch (Leaf x) (plant xs)"

primrec mirror :: "'a tree \<Rightarrow> 'a tree" where
  "mirror (Twig) = Twig "
  | "mirror (Leaf a) = Leaf a "
  | "mirror (Branch l r) = Branch (mirror r) (mirror l)"

theorem "plant (rev (leaves xt)) = mirror xt"
  quickcheck [generator = code]
    --{* Wrong! *} 
  oops

theorem "plant (leaves xt @ leaves yt) = Branch xt yt"
  quickcheck [generator = code]
    --{* Wrong! *} 
  oops

datatype 'a ntree = Tip "'a" | Node "'a" "'a ntree" "'a ntree"

primrec inOrder :: "'a ntree \<Rightarrow> 'a list" where
  "inOrder (Tip a)= [a]"
  | "inOrder (Node f x y) = (inOrder x)@[f]@(inOrder y)"

primrec root :: "'a ntree \<Rightarrow> 'a" where
  "root (Tip a) = a"
  | "root (Node f x y) = f"

theorem "hd (inOrder xt) = root xt"
  quickcheck [generator = code]
    --{* Wrong! *} 
  oops

lemma "int (f k) = k"
  quickcheck [generator = code]
  oops

lemma "int (nat k) = k"
  quickcheck [generator = code]
  oops

end

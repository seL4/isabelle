(*  Title:      HOL/prod
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

For prod.thy.  Ordered Pairs, the Cartesian product type, the unit type
*)

open Prod;

(*This counts as a non-emptiness result for admitting 'a * 'b as a type*)
Goalw [Prod_def] "Pair_Rep a b : Prod";
by (EVERY1 [rtac CollectI, rtac exI, rtac exI, rtac refl]);
qed "ProdI";

val [major] = goalw Prod.thy [Pair_Rep_def]
    "Pair_Rep a b = Pair_Rep a' b' ==> a=a' & b=b'";
by (EVERY1 [rtac (major RS fun_cong RS fun_cong RS subst), 
            rtac conjI, rtac refl, rtac refl]);
qed "Pair_Rep_inject";

Goal "inj_on Abs_Prod Prod";
by (rtac inj_on_inverseI 1);
by (etac Abs_Prod_inverse 1);
qed "inj_on_Abs_Prod";

val prems = goalw Prod.thy [Pair_def]
    "[| (a, b) = (a',b');  [| a=a';  b=b' |] ==> R |] ==> R";
by (rtac (inj_on_Abs_Prod RS inj_onD RS Pair_Rep_inject RS conjE) 1);
by (REPEAT (ares_tac (prems@[ProdI]) 1));
qed "Pair_inject";

Goal "((a,b) = (a',b')) = (a=a' & b=b')";
by (blast_tac (claset() addSEs [Pair_inject]) 1);
qed "Pair_eq";
AddIffs [Pair_eq];

Goalw [fst_def] "fst((a,b)) = a";
by (Blast_tac 1);
qed "fst_conv";
Goalw [snd_def] "snd((a,b)) = b";
by (Blast_tac 1);
qed "snd_conv";
Addsimps [fst_conv, snd_conv];

Goalw [Pair_def] "? x y. p = (x,y)";
by (rtac (rewrite_rule [Prod_def] Rep_Prod RS CollectE) 1);
by (EVERY1[etac exE, etac exE, rtac exI, rtac exI,
           rtac (Rep_Prod_inverse RS sym RS trans),  etac arg_cong]);
qed "PairE_lemma";

val [prem] = goal Prod.thy "[| !!x y. p = (x,y) ==> Q |] ==> Q";
by (rtac (PairE_lemma RS exE) 1);
by (REPEAT (eresolve_tac [prem,exE] 1));
qed "PairE";

fun pair_tac s = EVERY' [res_inst_tac [("p",s)] PairE, hyp_subst_tac,
			 K prune_params_tac];

(* Do not add as rewrite rule: invalidates some proofs in IMP *)
Goal "p = (fst(p),snd(p))";
by (pair_tac "p" 1);
by (Asm_simp_tac 1);
qed "surjective_pairing";

val surj_pair = prove_goal Prod.thy "? x y. z = (x, y)" (K [
	rtac exI 1, rtac exI 1, rtac surjective_pairing 1]);
Addsimps [surj_pair];

(* lemmas for splitting paired `!!' *)
local 
    val lemma1 = prove_goal Prod.thy "(!!x. PROP P x) ==> (!!a b. PROP P(a,b))" 
		 (fn prems => [resolve_tac prems 1]);

    val psig = sign_of Prod.thy;
    val pT = Sign.read_typ (psig, K None) "?'a*?'b=>prop";
    val PeqP = reflexive(read_cterm psig ("P", pT));
    val psplit = zero_var_indexes(read_instantiate [("p","x")]
                                  surjective_pairing RS eq_reflection);
    val adhoc = combination PeqP psplit;
    val lemma = prove_goal Prod.thy "(!!a b. PROP P(a,b)) ==> PROP P x" 
		(fn prems => [rewtac adhoc, resolve_tac prems 1]);
    val lemma2 = prove_goal Prod.thy "(!!a b. PROP P(a,b)) ==> (!!x. PROP P x)"
		(fn prems => [rtac lemma 1, resolve_tac prems 1]);
in
  val split_paired_all = equal_intr lemma1 lemma2
end;
bind_thm("split_paired_all", split_paired_all);
(*
Addsimps [split_paired_all] does not work with simplifier 
because it also affects premises in congrence rules, 
where is can lead to premises of the form !!a b. ... = ?P(a,b)
which cannot be solved by reflexivity.
*)

(* replace parameters of product type by individual component parameters *)
local
  fun is_pair (_,Type("*",_)) = true
    | is_pair  _              = false;
  fun exists_paired_all prem  = exists is_pair (Logic.strip_params prem);
  val split_tac = full_simp_tac (HOL_basic_ss addsimps [split_paired_all]);
in
val split_all_tac = SUBGOAL (fn (prem,i) => 
    if exists_paired_all prem then split_tac i else no_tac);  
end;

claset_ref() := claset() addSWrapper ("split_all_tac", 
				      fn tac2 => split_all_tac ORELSE' tac2);

Goal "(!x. P x) = (!a b. P(a,b))";
by (Fast_tac 1);
qed "split_paired_All";
Addsimps [split_paired_All];
(* AddIffs is not a good idea because it makes Blast_tac loop *)

Goal "(? x. P x) = (? a b. P(a,b))";
by (Fast_tac 1);
qed "split_paired_Ex";
Addsimps [split_paired_Ex];

Goalw [split_def] "split c (a,b) = c a b";
by (Simp_tac 1);
qed "split";
Addsimps [split];

Goal "split Pair p = p";
by (pair_tac "p" 1);
by (Simp_tac 1);
qed "split_Pair";
(*unused: val surjective_pairing2 = split_Pair RS sym;*)

Goal "!!s t. (s=t) = (fst(s)=fst(t) & snd(s)=snd(t))";
by (split_all_tac 1);
by (Asm_simp_tac 1);
qed "Pair_fst_snd_eq";

(*Prevents simplification of c: much faster*)
qed_goal "split_weak_cong" Prod.thy
  "p=q ==> split c p = split c q"
  (fn [prem] => [rtac (prem RS arg_cong) 1]);

qed_goal "split_eta" Prod.thy "(%(x,y). f(x,y)) = f"
  (K [rtac ext 1, split_all_tac 1, rtac split 1]);

qed_goal "cond_split_eta" Prod.thy 
	"!!f. (!!x y. f x y = g(x,y)) ==> (%(x,y). f x y) = g"
  (K [asm_simp_tac (simpset() addsimps [split_eta]) 1]);
(*Addsimps [cond_split_eta];  with this version of split_eta, the simplifier 
			      can eta-contract arbitrarily tupled functions.
  Unfortunately, this renders some existing proofs very inefficient.
                 stac split_eta does not work in general either. *)
val split_etas = split_eta::map (fn s => prove_goal Prod.thy s 
  (K [simp_tac (simpset() addsimps [cond_split_eta]) 1]))
["(%(a,b,c    ). f(a,b,c    )) = f","(%(a,b,c,d    ). f(a,b,c,d    )) = f",
 "(%(a,b,c,d,e). f(a,b,c,d,e)) = f","(%(a,b,c,d,e,g). f(a,b,c,d,e,g)) = f"];
Addsimps split_etas; (* pragmatic solution *)

Goal "(%(x,y,z).f(x,y,z)) = t";
by(simp_tac (simpset() addsimps [cond_split_eta]) 1);

qed_goal "split_beta" Prod.thy "(%(x,y). P x y) z = P (fst z) (snd z)"
	(K [stac surjective_pairing 1, stac split 1, rtac refl 1]);

(*For use with split_tac and the simplifier*)
Goal "R (split c p) = (! x y. p = (x,y) --> R (c x y))";
by (stac surjective_pairing 1);
by (stac split 1);
by (Blast_tac 1);
qed "split_split";

(* could be done after split_tac has been speeded up significantly:
simpset_ref() := simpset() addsplits [split_split];
   precompute the constants involved and don't do anything unless
   the current goal contains one of those constants
*)

Goal "R (split c p) = (~(? x y. p = (x,y) & (~R (c x y))))";
by (stac split_split 1);
by (Simp_tac 1);
qed "expand_split_asm";

(** split used as a logical connective or set former **)

(*These rules are for use with blast_tac.
  Could instead call simp_tac/asm_full_simp_tac using split as rewrite.*)

Goal "!!p. [| !!a b. p=(a,b) ==> c a b |] ==> split c p";
by (split_all_tac 1);
by (Asm_simp_tac 1);
qed "splitI2";

Goal "!!a b c. c a b ==> split c (a,b)";
by (Asm_simp_tac 1);
qed "splitI";

val prems = goalw Prod.thy [split_def]
    "[| split c p;  !!x y. [| p = (x,y);  c x y |] ==> Q |] ==> Q";
by (REPEAT (resolve_tac (prems@[surjective_pairing]) 1));
qed "splitE";

val splitE2 = prove_goal Prod.thy 
"[|Q (split P z); !!x y. [|z = (x, y); Q (P x y)|] ==> R|] ==> R" (fn prems => [
	REPEAT (resolve_tac (prems@[surjective_pairing]) 1),
	rtac (split_beta RS subst) 1,
	rtac (hd prems) 1]);

Goal "!!R a b. split R (a,b) ==> R a b";
by (etac (split RS iffD1) 1);
qed "splitD";

Goal "!!a b c. z: c a b ==> z: split c (a,b)";
by (Asm_simp_tac 1);
qed "mem_splitI";

Goal "!!p. [| !!a b. p=(a,b) ==> z: c a b |] ==> z: split c p";
by (split_all_tac 1);
by (Asm_simp_tac 1);
qed "mem_splitI2";

val prems = goalw Prod.thy [split_def]
    "[| z: split c p;  !!x y. [| p = (x,y);  z: c x y |] ==> Q |] ==> Q";
by (REPEAT (resolve_tac (prems@[surjective_pairing]) 1));
qed "mem_splitE";

AddSIs [splitI, splitI2, mem_splitI, mem_splitI2];
AddSEs [splitE, mem_splitE];

(* allows simplifications of nested splits in case of independent predicates *)
Goal "(%(a,b). P & Q a b) = (%ab. P & split Q ab)";
by (rtac ext 1);
by (Blast_tac 1);
qed "split_part";
Addsimps [split_part];

Goal "(@(x',y'). x = x' & y = y') = (x,y)";
by (Blast_tac 1);
qed "Eps_split_eq";
Addsimps [Eps_split_eq];
(*
the following  would be slightly more general, 
but cannot be used as rewrite rule:
### Cannot add premise as rewrite rule because it contains (type) unknowns:
### ?y = .x
Goal "!!P. [| P y; !!x. P x ==> x = y |] ==> (@(x',y). x = x' & P y) = (x,y)";
by (rtac select_equality 1);
by ( Simp_tac 1);
by (split_all_tac 1);
by (Asm_full_simp_tac 1);
qed "Eps_split_eq";
*)

(*** prod_fun -- action of the product functor upon functions ***)

Goalw [prod_fun_def] "prod_fun f g (a,b) = (f(a),g(b))";
by (rtac split 1);
qed "prod_fun";
Addsimps [prod_fun];

Goal 
    "prod_fun (f1 o f2) (g1 o g2) = ((prod_fun f1 g1) o (prod_fun f2 g2))";
by (rtac ext 1);
by (pair_tac "x" 1);
by (Asm_simp_tac 1);
qed "prod_fun_compose";

Goal "prod_fun (%x. x) (%y. y) = (%z. z)";
by (rtac ext 1);
by (pair_tac "z" 1);
by (Asm_simp_tac 1);
qed "prod_fun_ident";
Addsimps [prod_fun_ident];

val prems = goal Prod.thy "(a,b):r ==> (f(a),g(b)) : (prod_fun f g)``r";
by (rtac image_eqI 1);
by (rtac (prod_fun RS sym) 1);
by (resolve_tac prems 1);
qed "prod_fun_imageI";

val major::prems = goal Prod.thy
    "[| c: (prod_fun f g)``r;  !!x y. [| c=(f(x),g(y));  (x,y):r |] ==> P  \
\    |] ==> P";
by (rtac (major RS imageE) 1);
by (res_inst_tac [("p","x")] PairE 1);
by (resolve_tac prems 1);
by (Blast_tac 2);
by (blast_tac (claset() addIs [prod_fun]) 1);
qed "prod_fun_imageE";


(*** Disjoint union of a family of sets - Sigma ***)

qed_goalw "SigmaI" Prod.thy [Sigma_def]
    "[| a:A;  b:B(a) |] ==> (a,b) : Sigma A B"
 (fn prems=> [ (REPEAT (resolve_tac (prems@[singletonI,UN_I]) 1)) ]);

AddSIs [SigmaI];

(*The general elimination rule*)
qed_goalw "SigmaE" Prod.thy [Sigma_def]
    "[| c: Sigma A B;  \
\       !!x y.[| x:A;  y:B(x);  c=(x,y) |] ==> P \
\    |] ==> P"
 (fn major::prems=>
  [ (cut_facts_tac [major] 1),
    (REPEAT (eresolve_tac [UN_E, singletonE] 1 ORELSE ares_tac prems 1)) ]);

(** Elimination of (a,b):A*B -- introduces no eigenvariables **)
qed_goal "SigmaD1" Prod.thy "(a,b) : Sigma A B ==> a : A"
 (fn [major]=>
  [ (rtac (major RS SigmaE) 1),
    (REPEAT (eresolve_tac [asm_rl,Pair_inject,ssubst] 1)) ]);

qed_goal "SigmaD2" Prod.thy "(a,b) : Sigma A B ==> b : B(a)"
 (fn [major]=>
  [ (rtac (major RS SigmaE) 1),
    (REPEAT (eresolve_tac [asm_rl,Pair_inject,ssubst] 1)) ]);

qed_goal "SigmaE2" Prod.thy
    "[| (a,b) : Sigma A B;    \
\       [| a:A;  b:B(a) |] ==> P   \
\    |] ==> P"
 (fn [major,minor]=>
  [ (rtac minor 1),
    (rtac (major RS SigmaD1) 1),
    (rtac (major RS SigmaD2) 1) ]);

AddSEs [SigmaE2, SigmaE];

val prems = goal Prod.thy
    "[| A<=C;  !!x. x:A ==> B x <= D x |] ==> Sigma A B <= Sigma C D";
by (cut_facts_tac prems 1);
by (blast_tac (claset() addIs (prems RL [subsetD])) 1);
qed "Sigma_mono";

qed_goal "Sigma_empty1" Prod.thy "Sigma {} B = {}"
 (fn _ => [ (Blast_tac 1) ]);

qed_goal "Sigma_empty2" Prod.thy "A Times {} = {}"
 (fn _ => [ (Blast_tac 1) ]);

Addsimps [Sigma_empty1,Sigma_empty2]; 

Goal "((a,b): Sigma A B) = (a:A & b:B(a))";
by (Blast_tac 1);
qed "mem_Sigma_iff";
AddIffs [mem_Sigma_iff]; 

val Collect_split = prove_goal Prod.thy 
	"{(a,b). P a & Q b} = Collect P Times Collect Q" (K [Blast_tac 1]);
Addsimps [Collect_split];

(*Suggested by Pierre Chartier*)
Goal
     "(UN (a,b):(A Times B). E a Times F b) = (UNION A E) Times (UNION B F)";
by (Blast_tac 1);
qed "UNION_Times_distrib";

(*** Domain of a relation ***)

val prems = goalw Prod.thy [image_def] "(a,b) : r ==> a : fst``r";
by (rtac CollectI 1);
by (rtac bexI 1);
by (rtac (fst_conv RS sym) 1);
by (resolve_tac prems 1);
qed "fst_imageI";

val major::prems = goal Prod.thy
    "[| a : fst``r;  !!y.[| (a,y) : r |] ==> P |] ==> P"; 
by (rtac (major RS imageE) 1);
by (resolve_tac prems 1);
by (etac ssubst 1);
by (rtac (surjective_pairing RS subst) 1);
by (assume_tac 1);
qed "fst_imageE";

(*** Range of a relation ***)

val prems = goalw Prod.thy [image_def] "(a,b) : r ==> b : snd``r";
by (rtac CollectI 1);
by (rtac bexI 1);
by (rtac (snd_conv RS sym) 1);
by (resolve_tac prems 1);
qed "snd_imageI";

val major::prems = goal Prod.thy
    "[| a : snd``r;  !!y.[| (y,a) : r |] ==> P |] ==> P"; 
by (rtac (major RS imageE) 1);
by (resolve_tac prems 1);
by (etac ssubst 1);
by (rtac (surjective_pairing RS subst) 1);
by (assume_tac 1);
qed "snd_imageE";


(** Exhaustion rule for unit -- a degenerate form of induction **)

Goalw [Unity_def]
    "u = ()";
by (stac (rewrite_rule [unit_def] Rep_unit RS singletonD RS sym) 1);
by (rtac (Rep_unit_inverse RS sym) 1);
qed "unit_eq";
 
AddIs  [fst_imageI, snd_imageI, prod_fun_imageI];
AddSEs [fst_imageE, snd_imageE, prod_fun_imageE];


(*simplification procedure for unit_eq.
  Cannot use this rule directly -- it loops!*)
local
  val unit_pat = Thm.cterm_of (sign_of thy) (Free ("x", HOLogic.unitT));
  val unit_meta_eq = standard (mk_meta_eq unit_eq);
  fun proc _ _ t =
    if HOLogic.is_unit t then None
    else Some unit_meta_eq;
in
  val unit_eq_proc = Simplifier.mk_simproc "unit_eq" [unit_pat] proc;
end;

Addsimprocs [unit_eq_proc];


(*This rewrite counters the effect of unit_eq_proc on (%u::unit. f u),
  replacing it by f rather than by %u.f(). *)
Goal "(%u::unit. f()) = f";
by (rtac ext 1);
by (Simp_tac 1);
qed "unit_abs_eta_conv";
Addsimps [unit_abs_eta_conv];


(*Attempts to remove occurrences of split, and pair-valued parameters*)
val remove_split = rewrite_rule [split RS eq_reflection] o  
                   rule_by_tactic (TRYALL split_all_tac);

local

(*In ap_split S T u, term u expects separate arguments for the factors of S,
  with result type T.  The call creates a new term expecting one argument
  of type S.*)
fun ap_split (Type ("*", [T1, T2])) T3 u = 
      HOLogic.split_const (T1, T2, T3) $ 
      Abs("v", T1, 
          ap_split T2 T3
             ((ap_split T1 (HOLogic.prodT_factors T2 ---> T3) (incr_boundvars 1 u)) $ 
              Bound 0))
  | ap_split T T3 u = u;

(*Curries any Var of function type in the rule*)
fun split_rule_var' (t as Var (v, Type ("fun", [T1, T2])), rl) =
      let val T' = HOLogic.prodT_factors T1 ---> T2
          val newt = ap_split T1 T2 (Var (v, T'))
          val cterm = Thm.cterm_of (#sign (rep_thm rl))
      in
          instantiate ([], [(cterm t, cterm newt)]) rl
      end
  | split_rule_var' (t, rl) = rl;

in

val split_rule_var = standard o remove_split o split_rule_var';

(*Curries ALL function variables occurring in a rule's conclusion*)
fun split_rule rl = remove_split (foldr split_rule_var' (term_vars (concl_of rl), rl))
                    |> standard;

end;

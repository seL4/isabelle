(*  Title:      HOL/prod
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

For prod.thy.  Ordered Pairs, the Cartesian product type, the unit type
*)

open Prod;

(*This counts as a non-emptiness result for admitting 'a * 'b as a type*)
goalw Prod.thy [Prod_def] "Pair_Rep a b : Prod";
by (EVERY1 [rtac CollectI, rtac exI, rtac exI, rtac refl]);
qed "ProdI";

val [major] = goalw Prod.thy [Pair_Rep_def]
    "Pair_Rep a b = Pair_Rep a' b' ==> a=a' & b=b'";
by (EVERY1 [rtac (major RS fun_cong RS fun_cong RS subst), 
            rtac conjI, rtac refl, rtac refl]);
qed "Pair_Rep_inject";

goal Prod.thy "inj_onto Abs_Prod Prod";
by (rtac inj_onto_inverseI 1);
by (etac Abs_Prod_inverse 1);
qed "inj_onto_Abs_Prod";

val prems = goalw Prod.thy [Pair_def]
    "[| (a, b) = (a',b');  [| a=a';  b=b' |] ==> R |] ==> R";
by (rtac (inj_onto_Abs_Prod RS inj_ontoD RS Pair_Rep_inject RS conjE) 1);
by (REPEAT (ares_tac (prems@[ProdI]) 1));
qed "Pair_inject";

goal Prod.thy "((a,b) = (a',b')) = (a=a' & b=b')";
by (blast_tac (claset() addSEs [Pair_inject]) 1);
qed "Pair_eq";
AddIffs [Pair_eq];

goalw Prod.thy [fst_def] "fst((a,b)) = a";
by (Blast_tac 1);
qed "fst_conv";
goalw Prod.thy [snd_def] "snd((a,b)) = b";
by (Blast_tac 1);
qed "snd_conv";
Addsimps [fst_conv, snd_conv];

goalw Prod.thy [Pair_def] "? x y. p = (x,y)";
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

(* replace parameters of product type by individual component parameters *)
local
  fun is_pair (_,Type("*",_)) = true
    | is_pair  _              = false;
  fun ptac x = res_inst_tac [("p",x)] PairE;
  fun find_pair_params prem =
    let val params = Logic.strip_params prem
    in if exists is_pair params
       then let val params = rev(rename_wrt_term prem params)
                             (*as they are printed*)
            in filter is_pair params end
       else []
   end;
in
val split_all_tac = REPEAT1 o SUBGOAL (fn (prem,i) => 
  let val params = find_pair_params prem in
  if params = [] then no_tac 
  	         else EVERY'[EVERY' (map (ptac o fst) params),
			     REPEAT o hyp_subst_tac,
			     K prune_params_tac] i end)
end;

(*claset_ref() := claset()  addbefore  ("split_all_tac", TRY o split_all_tac);*)
  claset_ref() := claset() addSWrapper ("split_all_tac", 
					fn tac2 => split_all_tac ORELSE' tac2);

(*** lemmas for splitting paired `!!'
Does not work with simplifier because it also affects premises in
congrence rules, where is can lead to premises of the form
!!a b. ... = ?P(a,b)
which cannot be solved by reflexivity.
   
val [prem] = goal Prod.thy "(!!x. PROP P x) ==> (!!a b. PROP P(a,b))";
by (rtac prem 1);
val lemma1 = result();

local
    val psig = sign_of Prod.thy;
    val pT = Sign.read_typ (psig, K None) "?'a*?'b=>prop";
    val PeqP = reflexive(read_cterm psig ("P", pT));
    val psplit = zero_var_indexes(read_instantiate [("p","x")]
                                  surjective_pairing RS eq_reflection)
in
val adhoc = combination PeqP psplit
end;


val [prem] = goal Prod.thy "(!!a b. PROP P(a,b)) ==> PROP P x";
by (rewtac adhoc);
by (rtac prem 1);
val lemma = result();

val [prem] = goal Prod.thy "(!!a b. PROP P(a,b)) ==> (!!x. PROP P x)";
by (rtac lemma 1);
by (rtac prem 1);
val lemma2 = result();

bind_thm("split_paired_all", equal_intr lemma1 lemma2);
Addsimps [split_paired_all];
***)

goal Prod.thy "(!x. P x) = (!a b. P(a,b))";
by (Fast_tac 1);
qed "split_paired_All";
Addsimps [split_paired_All];
(* AddIffs is not a good idea because it makes Blast_tac loop *)

goal Prod.thy "(? x. P x) = (? a b. P(a,b))";
by (Fast_tac 1);
qed "split_paired_Ex";
Addsimps [split_paired_Ex];

goalw Prod.thy [split_def] "split c (a,b) = c a b";
by (Simp_tac 1);
qed "split";
Addsimps [split];

goal Prod.thy "(s=t) = (fst(s)=fst(t) & snd(s)=snd(t))";
by (res_inst_tac[("p","s")] PairE 1);
by (res_inst_tac[("p","t")] PairE 1);
by (Asm_simp_tac 1);
qed "Pair_fst_snd_eq";

(*Prevents simplification of c: much faster*)
qed_goal "split_weak_cong" Prod.thy
  "p=q ==> split c p = split c q"
  (fn [prem] => [rtac (prem RS arg_cong) 1]);

(* Do not add as rewrite rule: invalidates some proofs in IMP *)
goal Prod.thy "p = (fst(p),snd(p))";
by (res_inst_tac [("p","p")] PairE 1);
by (Asm_simp_tac 1);
qed "surjective_pairing";

goal Prod.thy "p = split (%x y.(x,y)) p";
by (res_inst_tac [("p","p")] PairE 1);
by (Asm_simp_tac 1);
qed "surjective_pairing2";

val surj_pair = prove_goal Prod.thy "? x y. z = (x, y)" (K [
	rtac exI 1, rtac exI 1, rtac surjective_pairing 1]);
Addsimps [surj_pair];

qed_goal "split_eta" Prod.thy "(%(x,y). f(x,y)) = f"
  (K [rtac ext 1, split_all_tac 1, rtac split 1]);

qed_goal "split_beta" Prod.thy "(%(x,y). P x y) z = P (fst z) (snd z)"
	(K [stac surjective_pairing 1, stac split 1, rtac refl 1]);

(*For use with split_tac and the simplifier*)
goal Prod.thy "R (split c p) = (! x y. p = (x,y) --> R (c x y))";
by (stac surjective_pairing 1);
by (stac split 1);
by (Blast_tac 1);
qed "expand_split";

(* could be done after split_tac has been speeded up significantly:
simpset_ref() := simpset() addsplits [expand_split];
   precompute the constants involved and don't do anything unless
   the current goal contains one of those constants
*)

goal Prod.thy "R (split c p) = (~(? x y. p = (x,y) & (~R (c x y))))";
by (stac expand_split 1);
by (Simp_tac 1);
qed "expand_split_asm";

(** split used as a logical connective or set former **)

(*These rules are for use with blast_tac.
  Could instead call simp_tac/asm_full_simp_tac using split as rewrite.*)

goal Prod.thy "!!p. [| !!a b. p=(a,b) ==> c a b |] ==> split c p";
by (split_all_tac 1);
by (Asm_simp_tac 1);
qed "splitI2";

goal Prod.thy "!!a b c. c a b ==> split c (a,b)";
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

goal Prod.thy "!!R a b. split R (a,b) ==> R a b";
by (etac (split RS iffD1) 1);
qed "splitD";

goal Prod.thy "!!a b c. z: c a b ==> z: split c (a,b)";
by (Asm_simp_tac 1);
qed "mem_splitI";

goal Prod.thy "!!p. [| !!a b. p=(a,b) ==> z: c a b |] ==> z: split c p";
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
goal Prod.thy "(%(a,b). P & Q a b) = (%ab. P & split Q ab)";
by (rtac ext 1);
by (Blast_tac 1);
qed "split_part";
Addsimps [split_part];

goal Prod.thy "(@(x',y'). x = x' & y = y') = (x,y)";
by (Blast_tac 1);
qed "Eps_split_eq";
Addsimps [Eps_split_eq];
(*
the following  would be slightly more general, 
but cannot be used as rewrite rule:
### Cannot add premise as rewrite rule because it contains (type) unknowns:
### ?y = .x
goal Prod.thy "!!P. [| P y; !!x. P x ==> x = y |] ==> (@(x',y). x = x' & P y) = (x,y)";
by (rtac select_equality 1);
by ( Simp_tac 1);
by (split_all_tac 1);
by (Asm_full_simp_tac 1);
qed "Eps_split_eq";
*)

(*** prod_fun -- action of the product functor upon functions ***)

goalw Prod.thy [prod_fun_def] "prod_fun f g (a,b) = (f(a),g(b))";
by (rtac split 1);
qed "prod_fun";
Addsimps [prod_fun];

goal Prod.thy 
    "prod_fun (f1 o f2) (g1 o g2) = ((prod_fun f1 g1) o (prod_fun f2 g2))";
by (rtac ext 1);
by (res_inst_tac [("p","x")] PairE 1);
by (Asm_simp_tac 1);
qed "prod_fun_compose";

goal Prod.thy "prod_fun (%x. x) (%y. y) = (%z. z)";
by (rtac ext 1);
by (res_inst_tac [("p","z")] PairE 1);
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

goal Prod.thy "((a,b): Sigma A B) = (a:A & b:B(a))";
by (Blast_tac 1);
qed "mem_Sigma_iff";
AddIffs [mem_Sigma_iff]; 

val Collect_split = prove_goal Prod.thy 
	"{(a,b). P a & Q b} = Collect P Times Collect Q" (K [Blast_tac 1]);
Addsimps [Collect_split];

(*Suggested by Pierre Chartier*)
goal Prod.thy
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

goalw Prod.thy [Unity_def]
    "u = ()";
by (stac (rewrite_rule [unit_def] Rep_unit RS singletonD RS sym) 1);
by (rtac (Rep_unit_inverse RS sym) 1);
qed "unit_eq";
 
AddIs  [fst_imageI, snd_imageI, prod_fun_imageI];
AddSEs [fst_imageE, snd_imageE, prod_fun_imageE];

structure Prod_Syntax =
struct

val unitT = Type("unit",[]);

fun mk_prod (T1,T2) = Type("*", [T1,T2]);

(*Maps the type T1*...*Tn to [T1,...,Tn], however nested*)
fun factors (Type("*", [T1,T2])) = factors T1 @ factors T2
  | factors T                    = [T];

(*Make a correctly typed ordered pair*)
fun mk_Pair (t1,t2) = 
  let val T1 = fastype_of t1
      and T2 = fastype_of t2
  in  Const("Pair", [T1, T2] ---> mk_prod(T1,T2)) $ t1 $ t2  end;
   
fun split_const(Ta,Tb,Tc) = 
    Const("split", [[Ta,Tb]--->Tc, mk_prod(Ta,Tb)] ---> Tc);

(*In ap_split S T u, term u expects separate arguments for the factors of S,
  with result type T.  The call creates a new term expecting one argument
  of type S.*)
fun ap_split (Type("*", [T1,T2])) T3 u = 
      split_const(T1,T2,T3) $ 
      Abs("v", T1, 
          ap_split T2 T3
             ((ap_split T1 (factors T2 ---> T3) (incr_boundvars 1 u)) $ 
              Bound 0))
  | ap_split T T3 u = u;

(*Makes a nested tuple from a list, following the product type structure*)
fun mk_tuple (Type("*", [T1,T2])) tms = 
        mk_Pair (mk_tuple T1 tms, 
                 mk_tuple T2 (drop (length (factors T1), tms)))
  | mk_tuple T (t::_) = t;

(*Attempts to remove occurrences of split, and pair-valued parameters*)
val remove_split = rewrite_rule [split RS eq_reflection]  o  
                   rule_by_tactic (TRYALL split_all_tac);

(*Uncurries any Var of function type in the rule*)
fun split_rule_var (t as Var(v, Type("fun",[T1,T2])), rl) =
      let val T' = factors T1 ---> T2
          val newt = ap_split T1 T2 (Var(v,T'))
          val cterm = Thm.cterm_of (#sign(rep_thm rl))
      in
          remove_split (instantiate ([], [(cterm t, cterm newt)]) rl)
      end
  | split_rule_var (t,rl) = rl;

(*Uncurries ALL function variables occurring in a rule's conclusion*)
fun split_rule rl = foldr split_rule_var (term_vars (concl_of rl), rl)
                    |> standard;

end;

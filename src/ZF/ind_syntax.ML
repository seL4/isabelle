(*  Title:      ZF/ind-syntax.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Abstract Syntax functions for Inductive Definitions
*)

(*The structure protects these items from redeclaration (somewhat!).  The 
  datatype definitions in theory files refer to these items by name!
*)
structure Ind_Syntax =
struct

(** Abstract syntax definitions for FOL and ZF **)

val iT = Type("i",[])
and oT = Type("o",[]);


(** Logical constants **)

val conj = Const("op &", [oT,oT]--->oT)
and disj = Const("op |", [oT,oT]--->oT)
and imp = Const("op -->", [oT,oT]--->oT);

val eq_const = Const("op =", [iT,iT]--->oT);

val mem_const = Const("op :", [iT,iT]--->oT);

val exists_const = Const("Ex", [iT-->oT]--->oT);
fun mk_exists (Free(x,T),P) = exists_const $ (absfree (x,T,P));

val all_const = Const("All", [iT-->oT]--->oT);
fun mk_all (Free(x,T),P) = all_const $ (absfree (x,T,P));

(*Creates All(%v.v:A --> P(v)) rather than Ball(A,P) *)
fun mk_all_imp (A,P) = 
    all_const $ Abs("v", iT, imp $ (mem_const $ Bound 0 $ A) $ (P $ Bound 0));

val Part_const = Const("Part", [iT,iT-->iT]--->iT);

val Collect_const = Const("Collect", [iT,iT-->oT]--->iT);
fun mk_Collect (a,D,t) = Collect_const $ D $ absfree(a, iT, t);

val Trueprop = Const("Trueprop",oT-->propT);
fun mk_tprop P = Trueprop $ P;

(*simple error-checking in the premises of an inductive definition*)
fun chk_prem rec_hd (Const("op &",_) $ _ $ _) =
        error"Premises may not be conjuctive"
  | chk_prem rec_hd (Const("op :",_) $ t $ X) = 
        deny (Logic.occs(rec_hd,t)) "Recursion term on left of member symbol"
  | chk_prem rec_hd t = 
        deny (Logic.occs(rec_hd,t)) "Recursion term in side formula";

(*Return the conclusion of a rule, of the form t:X*)
fun rule_concl rl = 
    let val Const("Trueprop",_) $ (Const("op :",_) $ t $ X) = 
                Logic.strip_imp_concl rl
    in  (t,X)  end;

(*As above, but return error message if bad*)
fun rule_concl_msg sign rl = rule_concl rl
    handle Bind => error ("Ill-formed conclusion of introduction rule: " ^ 
                          Sign.string_of_term sign rl);

(*For deriving cases rules.  CollectD2 discards the domain, which is redundant;
  read_instantiate replaces a propositional variable by a formula variable*)
val equals_CollectD = 
    read_instantiate [("W","?Q")]
        (make_elim (equalityD1 RS subsetD RS CollectD2));


(** For datatype definitions **)

fun dest_mem (Const("op :",_) $ x $ A) = (x,A)
  | dest_mem _ = error "Constructor specifications must have the form x:A";

(*read a constructor specification*)
fun read_construct sign (id, sprems, syn) =
    let val prems = map (readtm sign oT) sprems
        val args = map (#1 o dest_mem) prems
        val T = (map (#2 o dest_Free) args) ---> iT
                handle TERM _ => error 
                    "Bad variable in constructor specification"
        val name = Syntax.const_name id syn  (*handle infix constructors*)
    in ((id,T,syn), name, args, prems) end;

val read_constructs = map o map o read_construct;

(*convert constructor specifications into introduction rules*)
fun mk_intr_tms sg (rec_tm, constructs) =
  let
    fun mk_intr ((id,T,syn), name, args, prems) =
      Logic.list_implies
        (map mk_tprop prems,
          mk_tprop (mem_const $ list_comb (Const (Sign.full_name sg name, T), args) $ rec_tm))
  in  map mk_intr constructs  end;

fun mk_all_intr_tms sg arg = List.concat (ListPair.map (mk_intr_tms sg) arg);

val Un          = Const("op Un", [iT,iT]--->iT)
and empty       = Const("0", iT)
and univ        = Const("univ", iT-->iT)
and quniv       = Const("quniv", iT-->iT);

(*Make a datatype's domain: form the union of its set parameters*)
fun union_params rec_tm =
  let val (_,args) = strip_comb rec_tm
  in  case (filter (fn arg => type_of arg = iT) args) of
         []    => empty
       | iargs => fold_bal (app Un) iargs
  end;

(*Previously these both did    replicate (length rec_tms);  however now
  [q]univ itself constitutes the sum domain for mutual recursion!*)
fun data_domain rec_tms = univ $ union_params (hd rec_tms);
fun Codata_domain rec_tms = quniv $ union_params (hd rec_tms);

(*Could go to FOL, but it's hardly general*)
val def_swap_iff = prove_goal IFOL.thy "a==b ==> a=c <-> c=b"
 (fn [def] => [(rewtac def), (rtac iffI 1), (REPEAT (etac sym 1))]);

val def_trans = prove_goal IFOL.thy "[| f==g;  g(a)=b |] ==> f(a)=b"
  (fn [rew,prem] => [ rewtac rew, rtac prem 1 ]);

(*Delete needless equality assumptions*)
val refl_thin = prove_goal IFOL.thy "!!P. [| a=a;  P |] ==> P"
     (fn _ => [assume_tac 1]);

(*Includes rules for succ and Pair since they are common constructions*)
val elim_rls = [asm_rl, FalseE, succ_neq_0, sym RS succ_neq_0, 
                Pair_neq_0, sym RS Pair_neq_0, Pair_inject,
                make_elim succ_inject, 
                refl_thin, conjE, exE, disjE];

(*Turns iff rules into safe elimination rules*)
fun mk_free_SEs iffs = map (gen_make_elim [conjE,FalseE]) (iffs RL [iffD1]);

end;


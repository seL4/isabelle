(*  Title:      HOL/add_ind_def.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Fixedpoint definition module -- for Inductive/Coinductive Definitions

Features:
* least or greatest fixedpoints
* user-specified product and sum constructions
* mutually recursive definitions
* definitions involving arbitrary monotone operators
* automatically proves introduction and elimination rules

The recursive sets must *already* be declared as constants in parent theory!

  Introduction rules have the form
  [| ti:M(Sj), ..., P(x), ... |] ==> t: Sk |]
  where M is some monotone operator (usually the identity)
  P(x) is any (non-conjunctive) side condition on the free variables
  ti, t are any terms
  Sj, Sk are two of the sets being defined in mutual recursion

Sums are used only for mutual recursion;
Products are used only to derive "streamlined" induction rules for relations

Nestings of disjoint sum types:
   (a+(b+c)) for 3,  ((a+b)+(c+d)) for 4,  ((a+b)+(c+(d+e))) for 5,
   ((a+(b+c))+(d+(e+f))) for 6
*)

signature FP =          (** Description of a fixed point operator **)
  sig
  val checkThy  : theory -> unit   (*signals error if Lfp/Gfp is missing*)
  val oper      : string * typ * term -> term   (*fixed point operator*)
  val Tarski    : thm              (*Tarski's fixed point theorem*)
  val induct    : thm              (*induction/coinduction rule*)
  end;


signature ADD_INDUCTIVE_DEF =
  sig 
  val add_fp_def_i : term list * term list -> theory -> theory
  end;



(*Declares functions to add fixedpoint/constructor defs to a theory*)
functor Add_inductive_def_Fun (Fp: FP) : ADD_INDUCTIVE_DEF =
struct
open Ind_Syntax;

(*internal version*)
fun add_fp_def_i (rec_tms, intr_tms) thy = 
  let
    val dummy = Fp.checkThy thy		(*has essential ancestors?*)
    
    val sign = sign_of thy;

    (*rec_params should agree for all mutually recursive components*)
    val rec_hds = map head_of rec_tms;

    val _ = assert_all is_Const rec_hds
            (fn t => "Recursive set not previously declared as constant: " ^ 
                     Sign.string_of_term sign t);

    (*Now we know they are all Consts, so get their names, type and params*)
    val rec_names = map (#1 o dest_Const) rec_hds
    and (Const(_,recT),rec_params) = strip_comb (hd rec_tms);

    val rec_base_names = map Sign.base_name rec_names;
    val _ = assert_all Syntax.is_identifier rec_base_names
       (fn a => "Base name of recursive set not an identifier: " ^ a);

    local (*Checking the introduction rules*)
      val intr_sets = map (#2 o rule_concl_msg sign) intr_tms;
      fun intr_ok set =
          case head_of set of Const(a,_) => a mem rec_names | _ => false;
    in
      val _ =  assert_all intr_ok intr_sets
         (fn t => "Conclusion of rule does not name a recursive set: " ^ 
                  Sign.string_of_term sign t);
    end;

    val _ = assert_all is_Free rec_params
        (fn t => "Param in recursion term not a free variable: " ^
                 Sign.string_of_term sign t);

    (*** Construct the lfp definition ***)
    val mk_variant = variant (foldr add_term_names (intr_tms,[]));

    val z = mk_variant"z" and X = mk_variant"X" and w = mk_variant"w";

    (*Mutual recursion ?? *)
    val dom_set  = body_type recT
    val dom_sumT = dest_setT dom_set

    val freez   = Free(z, dom_sumT)
    and freeX   = Free(X, dom_set);

    fun dest_tprop (Const("Trueprop",_) $ P) = P
      | dest_tprop Q = error ("Ill-formed premise of introduction rule: " ^ 
                              Sign.string_of_term sign Q);

    (*Makes a disjunct from an introduction rule*)
    fun lfp_part intr = (*quantify over rule's free vars except parameters*)
      let val prems = map dest_tprop (Logic.strip_imp_prems intr)
          val _ = seq (fn rec_hd => seq (chk_prem rec_hd) prems) rec_hds
          val exfrees = term_frees intr \\ rec_params
          val zeq = eq_const dom_sumT $ freez $ (#1 (rule_concl intr))
      in foldr mk_exists (exfrees, fold_bal (app conj) (zeq::prems)) end;

    (*The Part(A,h) terms -- compose injections to make h*)
    fun mk_Part (Bound 0, _) = freeX    (*no mutual rec, no Part needed*)
      | mk_Part (h, domT)    = 
          let val goodh = mend_sum_types (h, dom_sumT)
              and Part_const = 
                  Const("Part", [dom_set, domT-->dom_sumT]---> dom_set)
          in  Part_const $ freeX $ Abs(w,domT,goodh)  end;

    (*Access to balanced disjoint sums via injections??
      Mutual recursion is NOT supported*)
    val parts = ListPair.map mk_Part
                (accesses_bal (ap Inl, ap Inr, Bound 0) 1,
                 [dom_set]);

    (*replace each set by the corresponding Part(A,h)*)
    val part_intrs = map (subst_free (rec_tms ~~ parts) o lfp_part) intr_tms;

    val lfp_rhs = Fp.oper(X, dom_sumT, 
                          mk_Collect(z, dom_sumT, 
                                     fold_bal (app disj) part_intrs))


    (*** Make the new theory ***)

    (*A key definition:
      If no mutual recursion then it equals the one recursive set.
      If mutual recursion then it differs from all the recursive sets. *)
    val big_rec_base_name = space_implode "_" rec_base_names;
    val big_rec_name = Sign.full_name sign big_rec_base_name;

    (*Big_rec... is the union of the mutually recursive sets*)
    val big_rec_tm = list_comb(Const(big_rec_name,recT), rec_params);

    (*The individual sets must already be declared*)
    val axpairs = map mk_defpair 
          ((big_rec_tm, lfp_rhs) ::
           (case parts of 
               [_] => []                        (*no mutual recursion*)
             | _ => rec_tms ~~          (*define the sets as Parts*)
                    map (subst_atomic [(freeX, big_rec_tm)]) parts));

    val _ = seq (writeln o Sign.string_of_term sign o #2) axpairs
  
    (*Detect occurrences of operator, even with other types!*)
    val _ = (case rec_names inter (add_term_names (lfp_rhs,[])) of
               [] => ()
             | x::_ => error ("Illegal occurrence of recursion op: " ^ x ^
                               "\n\t*Consider adding type constraints*"))

  in  thy |> PureThy.add_store_defs_i axpairs  end


end;

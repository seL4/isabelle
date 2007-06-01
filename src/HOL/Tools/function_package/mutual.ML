(*  Title:      HOL/Tools/function_package/mutual.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions.
Tools for mutual recursive definitions.
*)

signature FUNDEF_MUTUAL =
sig

  val prepare_fundef_mutual : FundefCommon.fundef_config
                              -> string (* defname *)
                              -> ((string * typ) * mixfix) list
                              -> term list
                              -> local_theory
                              -> ((thm (* goalstate *)
                                   * (thm -> FundefCommon.fundef_result) (* proof continuation *)
                                   * (thm list -> thm list list)         (* sorting continuation *)
                                  ) * local_theory)

end


structure FundefMutual: FUNDEF_MUTUAL =
struct

open FundefLib
open FundefCommon

(* Theory dependencies *)
val sum_case_rules = thms "Sum_Type.sum_cases"
val split_apply = thm "Product_Type.split"

type qgar = string * (string * typ) list * term list * term list * term

fun name_of_fqgar (f, _, _, _, _) = f

datatype mutual_part =
  MutualPart of 
   {
    fvar : string * typ,
    cargTs: typ list,
    pthA: SumTools.sum_path,
    pthR: SumTools.sum_path,
    f_def: term,

    f: term option,
    f_defthm : thm option
   }
   

datatype mutual_info =
  Mutual of 
   { 
    fsum_var : string * typ,

    ST: typ,
    RST: typ,
    streeA: SumTools.sum_tree,
    streeR: SumTools.sum_tree,

    parts: mutual_part list,
    fqgars: qgar list,
    qglrs: ((string * typ) list * term list * term * term) list,

    fsum : term option
   }

fun mutual_induct_Pnames n =
    if n < 5 then fst (chop n ["P","Q","R","S"])
    else map (fn i => "P" ^ string_of_int i) (1 upto n)

fun get_part fname =
    the o find_first (fn (MutualPart {fvar=(n,_), ...}) => n = fname)
                     
(* FIXME *)
fun mk_prod_abs e (t1, t2) =
    let
      val bTs = rev (map snd e)
      val T1 = fastype_of1 (bTs, t1)
      val T2 = fastype_of1 (bTs, t2)
    in
      HOLogic.pair_const T1 T2 $ t1 $ t2
    end;


fun analyze_eqs ctxt defname fs eqs =
    let
        val fnames = map fst fs
        val fqgars = map split_def eqs
        val arities = mk_arities fqgars

        fun curried_types (fname, fT) =
            let
              val k = the_default 1 (Symtab.lookup arities fname)
              val (caTs, uaTs) = chop k (binder_types fT)
            in
                (caTs, uaTs ---> body_type fT)
            end

        val (caTss, resultTs) = split_list (map curried_types fs)
        val argTs = map (foldr1 HOLogic.mk_prodT) caTss

        val (RST,streeR, pthsR) = SumTools.mk_tree_distinct resultTs
        val (ST, streeA, pthsA) = SumTools.mk_tree argTs

        val fsum_type = ST --> RST

        val ([fsum_var_name], _) = Variable.add_fixes [ defname ^ "_sum" ] ctxt
        val fsum_var = (fsum_var_name, fsum_type)

        fun define (fvar as (n, T)) caTs pthA pthR =
            let
                val vars = map_index (fn (i,T) => Free ("x" ^ string_of_int i, T)) caTs (* FIXME: Bind xs properly *)

                val f_exp = SumTools.mk_proj streeR pthR (Free fsum_var $ SumTools.mk_inj streeA pthA (foldr1 HOLogic.mk_prod vars))
                val def = Term.abstract_over (Free fsum_var, fold_rev lambda vars f_exp)

                val rew = (n, fold_rev lambda vars f_exp)
            in
                (MutualPart {fvar=fvar,cargTs=caTs,pthA=pthA,pthR=pthR,f_def=def,f=NONE,f_defthm=NONE}, rew)
            end
            
        val (parts, rews) = split_list (map4 define fs caTss pthsA pthsR)

        fun convert_eqs (f, qs, gs, args, rhs) =
            let
              val MutualPart {pthA, pthR, ...} = get_part f parts
            in
              (qs, gs, SumTools.mk_inj streeA pthA (foldr1 (mk_prod_abs qs) args),
               SumTools.mk_inj streeR pthR (replace_frees rews rhs)
                               |> Envir.norm_term (Envir.empty 0))
            end

        val qglrs = map convert_eqs fqgars
    in
        Mutual {fsum_var=fsum_var, ST=ST, RST=RST, streeA=streeA, streeR=streeR,
                parts=parts, fqgars=fqgars, qglrs=qglrs, fsum=NONE}
    end




fun define_projections fixes mutual fsum lthy =
    let
      fun def ((MutualPart {fvar=(fname, fT), cargTs, pthA, pthR, f_def, ...}), (_, mixfix)) lthy =
          let
            val ((f, (_, f_defthm)), lthy') =
              LocalTheory.def Thm.internalK ((fname, mixfix),
                                            ((fname ^ "_def", []), Term.subst_bound (fsum, f_def)))
                              lthy
          in
            (MutualPart {fvar=(fname, fT), cargTs=cargTs, pthA=pthA, pthR=pthR, f_def=f_def,
                         f=SOME f, f_defthm=SOME f_defthm },
             lthy')
          end
          
      val Mutual { fsum_var, ST, RST, streeA, streeR, parts, fqgars, qglrs, ... } = mutual
      val (parts', lthy') = fold_map def (parts ~~ fixes) lthy
    in
      (Mutual { fsum_var=fsum_var, ST=ST, RST=RST, streeA=streeA, streeR=streeR, parts=parts',
                fqgars=fqgars, qglrs=qglrs, fsum=SOME fsum },
       lthy')
    end


fun beta_reduce thm = Thm.equal_elim (Thm.beta_conversion true (cprop_of thm)) thm
                      
fun in_context ctxt (f, pre_qs, pre_gs, pre_args, pre_rhs) F =
    let
      val thy = ProofContext.theory_of ctxt
                
      val oqnames = map fst pre_qs
      val (qs, ctxt') = Variable.variant_fixes oqnames ctxt
                        |>> map2 (fn (_, T) => fn n => Free (n, T)) pre_qs
                        
      fun inst t = subst_bounds (rev qs, t)
      val gs = map inst pre_gs
      val args = map inst pre_args
      val rhs = inst pre_rhs

      val cqs = map (cterm_of thy) qs
      val ags = map (assume o cterm_of thy) gs

      val import = fold forall_elim cqs
                   #> fold implies_elim_swp ags

      val export = fold_rev (implies_intr o cprop_of) ags
                   #> fold_rev forall_intr_rename (oqnames ~~ cqs)
    in
      F ctxt (f, qs, gs, args, rhs) import export
    end

fun recover_mutual_psimp all_orig_fdefs parts ctxt (fname, _, _, args, rhs) import (export : thm -> thm) sum_psimp_eq =
    let
      val (MutualPart {f=SOME f, f_defthm=SOME f_def, pthR, ...}) = get_part fname parts

      val psimp = import sum_psimp_eq
      val (simp, restore_cond) = case cprems_of psimp of
                                   [] => (psimp, I)
                                 | [cond] => (implies_elim psimp (assume cond), implies_intr cond)
                                 | _ => sys_error "Too many conditions"
    in
      Goal.prove ctxt [] [] 
                 (HOLogic.Trueprop $ HOLogic.mk_eq (list_comb (f, args), rhs))
                 (fn _ => SIMPSET (unfold_tac all_orig_fdefs)
                          THEN EqSubst.eqsubst_tac ctxt [0] [simp] 1
                          THEN SIMPSET' (fn ss => simp_tac (ss addsimps [SumTools.projl_inl, SumTools.projr_inr])) 1)
        |> restore_cond 
        |> export
    end


(* FIXME HACK *)
fun mk_applied_form ctxt caTs thm =
    let
      val thy = ProofContext.theory_of ctxt
      val xs = map_index (fn (i,T) => cterm_of thy (Free ("x" ^ string_of_int i, T))) caTs (* FIXME: Bind xs properly *)
    in
      fold (fn x => fn thm => combination thm (reflexive x)) xs thm
           |> beta_reduce
           |> fold_rev forall_intr xs
           |> forall_elim_vars 0
    end
    

fun mutual_induct_rules lthy induct all_f_defs (Mutual {RST, parts, streeA, ...}) =
    let
      val cert = cterm_of (ProofContext.theory_of lthy)
      val newPs = map2 (fn Pname => fn MutualPart {cargTs, ...} => 
                                       Free (Pname, cargTs ---> HOLogic.boolT))
                       (mutual_induct_Pnames (length parts))
                       parts
                       
      fun mk_P (MutualPart {cargTs, ...}) P =
          let
            val avars = map_index (fn (i,T) => Var (("a", i), T)) cargTs
            val atup = foldr1 HOLogic.mk_prod avars
          in
            tupled_lambda atup (list_comb (P, avars))
          end
          
      val Ps = map2 mk_P parts newPs
      val case_exp = SumTools.mk_sumcases streeA HOLogic.boolT Ps
                     
      val induct_inst =
          forall_elim (cert case_exp) induct
                      |> full_simplify (HOL_basic_ss addsimps (split_apply :: sum_case_rules))
                      |> full_simplify (HOL_basic_ss addsimps all_f_defs)
          
      fun mk_proj rule (MutualPart {cargTs, pthA, ...}) =
          let
            val afs = map_index (fn (i,T) => Free ("a" ^ string_of_int i, T)) cargTs
            val inj = SumTools.mk_inj streeA pthA (foldr1 HOLogic.mk_prod afs)
          in
            rule
              |> forall_elim (cert inj)
              |> full_simplify (HOL_basic_ss addsimps (split_apply :: sum_case_rules))
              |> fold_rev (forall_intr o cert) (afs @ newPs)
          end
          
    in
      map (mk_proj induct_inst) parts
    end
    

fun mk_partial_rules_mutual lthy inner_cont (m as Mutual {parts, fqgars, ...}) proof =
    let
      val result = inner_cont proof
      val FundefResult {fs=[f], G, R, cases, psimps, trsimps, subset_pinducts=[subset_pinduct],simple_pinducts=[simple_pinduct],
                        termination,domintros} = result
                                                                                                               
      val (all_f_defs, fs) = map (fn MutualPart {f_defthm = SOME f_def, f = SOME f, cargTs, ...} =>
                                     (mk_applied_form lthy cargTs (symmetric f_def), f))
                                 parts
                             |> split_list

      val all_orig_fdefs = map (fn MutualPart {f_defthm = SOME f_def, ...} => f_def) parts
                           
      fun mk_mpsimp fqgar sum_psimp =
          in_context lthy fqgar (recover_mutual_psimp all_orig_fdefs parts) sum_psimp
          
      val rew_ss = HOL_basic_ss addsimps all_f_defs
      val mpsimps = map2 mk_mpsimp fqgars psimps
      val mtrsimps = map_option (map2 mk_mpsimp fqgars) trsimps
      val minducts = mutual_induct_rules lthy simple_pinduct all_f_defs m
      val mtermination = full_simplify rew_ss termination
      val mdomintros = map_option (map (full_simplify rew_ss)) domintros
    in
      FundefResult { fs=fs, G=G, R=R,
                     psimps=mpsimps, subset_pinducts=[subset_pinduct], simple_pinducts=minducts,
                     cases=cases, termination=mtermination,
                     domintros=mdomintros,
                     trsimps=mtrsimps}
    end
      

(* puts an object in the "right bucket" *)
fun store_grouped P x [] = []
  | store_grouped P x ((l, xs)::bs) =
    if P (x, l) then ((l, x::xs)::bs) else ((l, xs)::store_grouped P x bs)
                                           
fun sort_by_function (Mutual {fqgars, ...}) names xs =
    fold_rev (store_grouped (eq_str o apfst fst))  (* fill *)
             (map name_of_fqgar fqgars ~~ xs)      (* the name-thm pairs *)
             (map (rpair []) names)                (* in the empty buckets labeled with names *)
             
             |> map (snd #> map snd)                     (* and remove the labels afterwards *)


fun prepare_fundef_mutual config defname fixes eqss lthy =
    let
      val mutual = analyze_eqs lthy defname (map fst fixes) (map Envir.beta_eta_contract eqss)
      val Mutual {fsum_var=(n, T), qglrs, ...} = mutual
          
      val ((fsum, goalstate, cont), lthy') =
          FundefCore.prepare_fundef config defname [((n, T), NoSyn)] qglrs lthy
          
      val (mutual', lthy'') = define_projections fixes mutual fsum lthy'

      val mutual_cont = mk_partial_rules_mutual lthy'' cont mutual'
      val sort_cont = sort_by_function mutual' (map (fst o fst) fixes)
    in
      ((goalstate, mutual_cont, sort_cont), lthy'')
    end

    
end

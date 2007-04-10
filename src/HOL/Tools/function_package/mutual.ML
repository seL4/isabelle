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
                              -> string (* default, unparsed term *)
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


fun open_all_all (Const ("all", _) $ Abs (n, T, b)) = apfst (cons (n, T)) (open_all_all b)
  | open_all_all t = ([], t)

(* Builds a curried clause description in abstracted form *)
fun split_def ctxt fnames geq arities =
    let
      fun input_error msg = cat_lines [msg, ProofContext.string_of_term ctxt geq]
                            
      val (qs, imp) = open_all_all geq

      val gs = Logic.strip_imp_prems imp
      val eq = Logic.strip_imp_concl imp

      val (f_args, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop eq)
      val (head, args) = strip_comb f_args

      val invalid_head_msg = "Head symbol of left hand side must be " ^ plural "" "one out of " fnames ^ commas_quote fnames
      val fname = fst (dest_Free head)
          handle TERM _ => error (input_error invalid_head_msg)

      val _ = fname mem fnames orelse error (input_error invalid_head_msg)

      fun add_bvs t is = add_loose_bnos (t, 0, is)
      val rvs = (add_bvs rhs [] \\ fold add_bvs args [])
                  |> map (fst o nth (rev qs))
                
      val _ = null rvs orelse error (input_error ("Variable" ^ plural " " "s " rvs ^ commas_quote rvs
                                              ^ " occur" ^ plural "s" "" rvs ^ " on right hand side only:"))

      val _ = forall (forall_aterms (fn Free (n, _) => not (n mem fnames) | _ => true)) gs orelse
                     error (input_error "Recursive Calls not allowed in premises")

      val k = length args

      val arities' = case Symtab.lookup arities fname of
                       NONE => Symtab.update (fname, k) arities
                     | SOME i => (i = k orelse
                                  error (input_error ("Function " ^ quote fname ^ " has different numbers of arguments in different equations"));
                                  arities)
    in
      ((fname, qs, gs, args, rhs), arities')
    end
    
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
        val (fqgars, arities) = fold_map (split_def ctxt fnames) eqs Symtab.empty

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
    

fun mutual_induct_rules thy induct all_f_defs (Mutual {RST, parts, streeA, ...}) =
    let
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
          forall_elim (cterm_of thy case_exp) induct
                      |> full_simplify (HOL_basic_ss addsimps (split_apply :: sum_case_rules))
                      |> full_simplify (HOL_basic_ss addsimps all_f_defs)
          
      fun mk_proj rule (MutualPart {cargTs, pthA, ...}) =
          let
            val afs = map_index (fn (i,T) => Free ("a" ^ string_of_int i, T)) cargTs
            val inj = SumTools.mk_inj streeA pthA (foldr1 HOLogic.mk_prod afs)
          in
            rule
              |> forall_elim (cterm_of thy inj)
              |> full_simplify (HOL_basic_ss addsimps (split_apply :: sum_case_rules))
              |> fold_rev (forall_intr o cterm_of thy) (afs @ newPs)
          end
          
    in
      map (mk_proj induct_inst) parts
    end
    




fun mk_partial_rules_mutual lthy inner_cont (m as Mutual {RST, parts, streeR, fqgars, ...}) proof =
    let
      val thy = ProofContext.theory_of lthy
                                       
      (* FIXME !? *)
      val expand = Assumption.export false lthy (LocalTheory.target_of lthy)
      val expand_term = Drule.term_rule thy expand
                        
      val result = inner_cont proof
      val FundefResult {f, G, R, cases, psimps, trsimps, subset_pinducts=[subset_pinduct],simple_pinducts=[simple_pinduct],
                        termination,domintros} = result
                                                                                                               
      val all_f_defs = map (fn MutualPart {f_defthm = SOME f_def, cargTs, ...} =>
                               mk_applied_form lthy cargTs (symmetric f_def))
                           parts

      val all_orig_fdefs = map (fn MutualPart {f_defthm = SOME f_def, ...} => f_def) parts
                           
      fun mk_mpsimp fqgar sum_psimp =
          in_context lthy fqgar (recover_mutual_psimp all_orig_fdefs parts) sum_psimp
          
      val mpsimps = map2 mk_mpsimp fqgars psimps
      val mtrsimps = map_option (map2 mk_mpsimp fqgars) trsimps
      val minducts = mutual_induct_rules thy simple_pinduct all_f_defs m
      val mtermination = full_simplify (HOL_basic_ss addsimps all_f_defs) termination
    in
      FundefResult { f=expand_term f, G=expand_term G, R=expand_term R,
                     psimps=map expand mpsimps, subset_pinducts=[expand subset_pinduct], simple_pinducts=map expand minducts,
                     cases=expand cases, termination=expand mtermination,
                     domintros=map_option (map expand) domintros,
                     trsimps=map_option (map expand) mtrsimps}
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


fun prepare_fundef_mutual config defname fixes eqss default lthy =
    let
      val mutual = analyze_eqs lthy defname (map fst fixes) (map Envir.beta_eta_contract eqss)
      val Mutual {fsum_var=(n, T), qglrs, ...} = mutual
          
      val ((fsum, goalstate, cont), lthy') =
          FundefCore.prepare_fundef config defname (n, T, NoSyn) qglrs default lthy
          
      val (mutual', lthy'') = define_projections fixes mutual fsum lthy'

      val mutual_cont = mk_partial_rules_mutual lthy'' cont mutual'
      val sort_cont = sort_by_function mutual' (map (fst o fst) fixes)
    in
      ((goalstate, mutual_cont, sort_cont), lthy'')
    end

    
end

(*  Title:      HOL/Tools/function_package/fundef_common.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions. 
Common type definitions and other infrastructure.
*)

structure FundefCommon =
struct

(* Theory Dependencies *)
val acc_const_name = "FunDef.accP"

val domintros = ref true;
val profile = ref false;

fun PROFILE msg = if !profile then timeap_msg msg else I

fun mk_acc domT R =
    Const (acc_const_name, (fastype_of R) --> domT --> HOLogic.boolT) $ R 

val function_name = suffix "C"
val graph_name = suffix "_graph"
val rel_name = suffix "_rel"
val dom_name = suffix "_dom"

val dest_rel_name = unsuffix "_rel"

type depgraph = int IntGraph.T


datatype ctx_tree 
  = Leaf of term
  | Cong of (term * thm * depgraph * ((string * typ) list * thm list * ctx_tree) list)
  | RCall of (term * ctx_tree)

type glrs = (term list * term list * term * term) list


datatype globals =
   Globals of { 
         fvar: term, 
         domT: typ, 
         ranT: typ,
         h: term, 
         y: term, 
         x: term, 
         z: term, 
         a:term, 
         P: term, 
         D: term, 
         Pbool:term
}


datatype rec_call_info = 
  RCInfo of
  {
   RIvs: (string * typ) list,  (* Call context: fixes and assumes *)
   CCas: thm list,
   rcarg: term,                 (* The recursive argument *)

   llRI: thm,
   h_assum: term
  } 


datatype clause_context =
  ClauseContext of
  {
    ctxt : Proof.context,

    qs : term list,
    gs : term list,
    lhs: term,
    rhs: term,

    cqs: cterm list,
    ags: thm list,     
    case_hyp : thm
  }


fun transfer_clause_ctx thy (ClauseContext { ctxt, qs, gs, lhs, rhs, cqs, ags, case_hyp }) =
    ClauseContext { ctxt = ProofContext.transfer thy ctxt,
                    qs = qs, gs = gs, lhs = lhs, rhs = rhs, cqs = cqs, ags = ags, case_hyp = case_hyp }


datatype clause_info =
  ClauseInfo of 
     {
      no: int,
      qglr : ((string * typ) list * term list * term * term),
      cdata : clause_context,

      tree: ctx_tree,
      lGI: thm,
      RCs: rec_call_info list
     }




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
    defname: string,
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


datatype prep_result =
  Prep of
     {
      globals: globals,
      f: term,
      G: term,
      R: term,
 
      goal: term,
      goalI: thm,
      values: thm list,
      clauses: clause_info list,

      R_cases: thm,
      ex1_iff: thm
     }

datatype fundef_result =
  FundefResult of
     {
      f: term,
      G : term,
      R : term,
      completeness : thm,

      psimps : thm list, 
      subset_pinduct : thm, 
      simple_pinduct : thm, 
      total_intro : thm,
      dom_intros : thm list
     }

datatype fundef_mresult =
  FundefMResult of
     {
      f: term,
      G: term,
      R: term,

      psimps : thm list, 
      subset_pinducts : thm list, 
      simple_pinducts : thm list, 
      cases : thm,
      termination : thm,
      domintros : thm list
     }

datatype fundef_context_data =
  FundefCtxData of
     {
      fixes : ((string * typ) * mixfix) list,
      spec : ((string * Attrib.src list) * term list) list list,
      mutual: mutual_info,

      f : term,
      R : term,
      
      psimps: thm list,
      pinducts: thm list,
      termination: thm
     }


structure FundefData = GenericDataFun
(struct
  val name = "HOL/function_def/data";
  type T = string * fundef_context_data Symtab.table

  val empty = ("", Symtab.empty);
  val copy = I;
  val extend = I;
  fun merge _ ((l1,tab1),(l2,tab2)) = (l1, Symtab.merge (K true) (tab1, tab2))

  fun print _ _ = ();
end);


structure FundefCongs = GenericDataFun
(struct
    val name = "HOL/function_def/congs"
    type T = thm list
    val empty = []
    val extend = I
    fun merge _ = Drule.merge_rules
    fun print  _ _ = ()
end);


fun add_fundef_data name fundef_data =
    FundefData.map (fn (last,tab) => (name, Symtab.update_new (name, fundef_data) tab))

fun get_fundef_data name thy = Symtab.lookup (snd (FundefData.get thy)) name

fun set_last_fundef name = FundefData.map (apfst (K name))
fun get_last_fundef thy = fst (FundefData.get thy)


val map_fundef_congs = FundefCongs.map 
val get_fundef_congs = FundefCongs.get



structure TerminationRule = ProofDataFun
(struct
    val name = "HOL/function_def/termination"
    type T = thm option
    fun init _ = NONE
    fun print  _ _ = ()
end);

val get_termination_rule = TerminationRule.get
val set_termination_rule = TerminationRule.map o K o SOME



(* Configuration management *)
datatype fundef_opt 
  = Sequential
  | Default of string
  | Preprocessor of string
  | Target of xstring
  | DomIntros

datatype fundef_config
  = FundefConfig of
   {
    sequential: bool,
    default: string,
    preprocessor: string option,
    target: xstring option,
    domintros: bool
   }


val default_config = FundefConfig { sequential=false, default="%x. arbitrary", preprocessor=NONE, target=NONE, domintros=false }
val fun_config = FundefConfig { sequential=true, default="%x. arbitrary", preprocessor=NONE, target=NONE, domintros=false }

fun apply_opt Sequential (FundefConfig {sequential, default, preprocessor, target, domintros}) = 
    FundefConfig {sequential=true, default=default, preprocessor=preprocessor, target=target, domintros=domintros }
  | apply_opt (Default d) (FundefConfig {sequential, default, preprocessor, target, domintros}) = 
    FundefConfig {sequential=sequential, default=d, preprocessor=preprocessor, target=target, domintros=domintros }
  | apply_opt (Preprocessor p) (FundefConfig {sequential, default, preprocessor, target, domintros}) = 
    FundefConfig {sequential=sequential, default=default, preprocessor=SOME p, target=target, domintros=domintros }
  | apply_opt (Target t) (FundefConfig {sequential, default, preprocessor, target, domintros }) =
    FundefConfig {sequential=sequential, default=default, preprocessor=preprocessor, target=SOME t, domintros=domintros }
  | apply_opt Domintros (FundefConfig {sequential, default, preprocessor, target, domintros }) =
    FundefConfig {sequential=sequential, default=default, preprocessor=preprocessor, target=target, domintros=true }


local structure P = OuterParse and K = OuterKeyword in

val opt_sequential = Scan.optional ((P.$$$ "(" |-- P.$$$ "sequential" --| P.$$$ ")") >> K true) false

val option_parser = (P.$$$ "sequential" >> K Sequential)
               || ((P.reserved "default" |-- P.term) >> Default)
               || (P.reserved "domintros" >> K DomIntros)
               || ((P.$$$ "in" |-- P.xname) >> Target)

fun config_parser def = (Scan.optional (P.$$$ "(" |-- P.list1 option_parser --| P.$$$ ")") [])
                          >> (fn opts => fold apply_opt opts def)
end


















end



(* Common Abbreviations *)

structure FundefAbbrev =
struct

fun implies_elim_swp x y = implies_elim y x

(* Some HOL things frequently used *)
val boolT = HOLogic.boolT
val mk_prod = HOLogic.mk_prod
val mk_mem = HOLogic.mk_mem
val mk_eq = HOLogic.mk_eq
val eq_const = HOLogic.eq_const
val Trueprop = HOLogic.mk_Trueprop

val mk_relT = HOLogic.mk_setT o HOLogic.mk_prodT
fun mk_relmem (x,y) R = Trueprop (mk_mem (mk_prod (x, y), R))

fun mk_subset T A B = 
    let val sT = HOLogic.mk_setT T
    in Const ("Orderings.less_eq", sT --> sT --> boolT) $ A $ B end


(* with explicit types: Needed with loose bounds *)
fun mk_relmemT xT yT (x,y) R = 
    let 
  val pT = HOLogic.mk_prodT (xT, yT)
  val RT = HOLogic.mk_setT pT
    in
  Const ("op :", [pT, RT] ---> boolT)
        $ (HOLogic.pair_const xT yT $ x $ y)
        $ R
    end

fun free_to_var (Free (v,T)) = Var ((v,0),T)
  | free_to_var _ = raise Match

fun var_to_free (Var ((v,_),T)) = Free (v,T)
  | var_to_free _ = raise Match


end

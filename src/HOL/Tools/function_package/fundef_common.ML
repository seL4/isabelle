(*  Title:      HOL/Tools/function_package/fundef_common.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions. 
Common type definitions and other infrastructure.
*)

structure FundefCommon =
struct

(* Theory Dependencies *)
val acc_const_name = "Accessible_Part.acc"



type depgraph = int IntGraph.T


datatype ctx_tree 
  = Leaf of term
  | Cong of (term * thm * depgraph * ((string * typ) list * thm list * ctx_tree) list)
  | RCall of (term * ctx_tree)

type glrs = (term list * term list * term * term) list


(* A record containing all the relevant symbols and types needed during the proof.
   This is set up at the beginning and does not change. *)
datatype naming_context =
   Names of { f: term, fvarname: string, fvar: term, domT: typ, ranT: typ,
       G: term, R: term, acc_R: term, h: term, y: term, x: term, z: term, a:term, P: term, 
       D: term, Pbool:term,
       glrs: (term list * term list * term * term) list,
       glrs': (term list * term list * term * term) list,
       f_def: thm,
       used: string list,
       trees: ctx_tree list
     }


datatype rec_call_info = 
  RCInfo of
  {
   RI: thm, 
   RIvs: (string * typ) list,
   lRI: thm, 
   lRIq: thm, 
   Gh: thm, 
   Gh': thm,
   GmAs: term list,
   rcarg: term
  } 
     
datatype clause_info =
  ClauseInfo of 
     {
      no: int,

      qs: term list, 
      gs: term list,
      lhs: term,
      rhs: term,

      cqs: cterm list,
      cvqs: cterm list,
      ags: thm list,
      
      cqs': cterm list, 
      ags': thm list,
      lhs': term,
      rhs': term,
      ordcqs': cterm list, 

      GI: thm,
      lGI: thm,
      RCs: rec_call_info list,

      tree: ctx_tree,
      case_hyp: thm
     }

type inj_proj = ((term -> term) * (term -> term))

type qgar = (string * typ) list * term list * term list * term

datatype mutual_part =
  MutualPart of 
	 {
          f_name: string,
	  const: string * typ,
	  cargTs: typ list,
	  pthA: SumTools.sum_path,
	  pthR: SumTools.sum_path,
	  qgars: qgar list,
	  f_def: thm
	 }
	 

datatype mutual_info =
  Mutual of 
	 { 
	  name: string, 
	  sum_const: string * typ,
	  ST: typ,
	  RST: typ,
	  streeA: SumTools.sum_tree,
	  streeR: SumTools.sum_tree,
	  parts: mutual_part list,
	  qglrss: (term list * term list * term * term) list list
	 }


datatype prep_result =
  Prep of
     {
      names: naming_context, 
      complete : term,
      compat : term list,
      clauses: clause_info list
     }

datatype fundef_result =
  FundefResult of
     {
      f: term,
      G : term,
      R : term,
      completeness : thm,
      compatibility : thm list,

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
      G : term,
      R : term,

      psimps : thm list list, 
      subset_pinducts : thm list, 
      simple_pinducts : thm list, 
      cases : thm,
      termination : thm,
      domintros : thm list
     }


type result_with_names = fundef_mresult * mutual_info * string list list * attribute list list list

structure FundefData = TheoryDataFun
(struct
  val name = "HOL/function_def/data";
  type T = string * result_with_names Symtab.table

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
    fun merge _ (l1, l2) = l1 @ l2
    fun print  _ _ = ()
end);


fun add_fundef_data name fundef_data =
    FundefData.map (fn (_,tab) => (name, Symtab.update_new (name, fundef_data) tab))

fun get_fundef_data name thy = Symtab.lookup (snd (FundefData.get thy)) name

fun get_last_fundef thy = fst (FundefData.get thy)

val map_fundef_congs = FundefCongs.map 
val get_fundef_congs = FundefCongs.get

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

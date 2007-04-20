(*  Title:      HOL/Tools/function_package/fundef_common.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions. 
Common type definitions and other infrastructure.
*)

structure FundefCommon =
struct

(* Profiling *)
val profile = ref false;

fun PROFILE msg = if !profile then timeap_msg msg else I


val acc_const_name = "Accessible_Part.acc"
fun mk_acc domT R =
    Const (acc_const_name, (domT --> domT --> HOLogic.boolT) --> domT --> HOLogic.boolT) $ R 

val function_name = suffix "C"
val graph_name = suffix "_graph"
val rel_name = suffix "_rel"
val dom_name = suffix "_dom"

type depgraph = int IntGraph.T

datatype ctx_tree 
  = Leaf of term
  | Cong of (term * thm * depgraph * ((string * typ) list * thm list * ctx_tree) list)
  | RCall of (term * ctx_tree)



datatype fundef_result =
  FundefResult of
     {
      fs: term list,
      G: term,
      R: term,

      psimps : thm list, 
      trsimps : thm list option, 

      subset_pinducts : thm list, 
      simple_pinducts : thm list, 
      cases : thm,
      termination : thm,
      domintros : thm list option
     }


datatype fundef_context_data =
  FundefCtxData of
     {
      defname : string,

      add_simps : string -> Attrib.src list -> thm list -> local_theory -> thm list * local_theory,

      fs : term list,
      R : term,
      
      psimps: thm list,
      pinducts: thm list,
      termination: thm
     }

fun morph_fundef_data phi (FundefCtxData {add_simps, fs, R, psimps, pinducts, termination, defname}) =
    let
      val term = Morphism.term phi val thm = Morphism.thm phi val fact = Morphism.fact phi
      val name = Morphism.name phi
    in
      FundefCtxData { add_simps = add_simps (* contains no logical entities *), 
                      fs = map term fs, R = term R, psimps = fact psimps, 
                      pinducts = fact pinducts, termination = thm termination,
                      defname = name defname }
    end

structure FundefData = GenericDataFun
(struct
  val name = "HOL/function_def/data";
  type T = (term * fundef_context_data) NetRules.T

  val empty = NetRules.init
    (op aconv o pairself fst : (term * fundef_context_data) * (term * fundef_context_data) -> bool)
    fst;
  val copy = I;
  val extend = I;
  fun merge _ (tab1, tab2) = NetRules.merge (tab1, tab2)

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


(* Generally useful?? *)
fun lift_morphism thy f = 
    let 
      val term = Drule.term_rule thy f
    in
      Morphism.thm_morphism f $> Morphism.term_morphism term $> Morphism.typ_morphism (Logic.type_map term)
    end

fun import_fundef_data t ctxt =
    let
      val thy = Context.theory_of ctxt
      val ct = cterm_of thy t
      val inst_morph = lift_morphism thy o Thm.instantiate 

      fun match data = 
          SOME (morph_fundef_data (inst_morph (Thm.cterm_match (cterm_of thy (fst data), ct))) (snd data))
          handle Pattern.MATCH => NONE
    in 
      get_first match (NetRules.retrieve (FundefData.get ctxt) t)
    end

fun import_last_fundef ctxt =
    case NetRules.rules (FundefData.get ctxt) of
      [] => NONE
    | (t, data) :: _ =>
      let 
        val ([t'], ctxt') = Variable.import_terms true [t] (Context.proof_of ctxt)
      in
        import_fundef_data t' (Context.Proof ctxt')
      end

val all_fundef_data = NetRules.rules o FundefData.get

val map_fundef_congs = FundefCongs.map 
val get_fundef_congs = FundefCongs.get



structure TerminationRule = GenericDataFun
(struct
    val name = "HOL/function_def/termination"
    type T = thm list
    val empty = []
    val extend = I
    fun merge _ = Drule.merge_rules
    fun print  _ _ = ()
end);

val get_termination_rules = TerminationRule.get
val store_termination_rule = TerminationRule.map o cons
val apply_termination_rule = resolve_tac o get_termination_rules o Context.Proof

fun add_fundef_data (data as FundefCtxData {fs, termination, ...}) =
    FundefData.map (fold (fn f => NetRules.insert (f, data)) fs)
    #> store_termination_rule termination



(* Configuration management *)
datatype fundef_opt 
  = Sequential
  | Default of string
  | Preprocessor of string
  | Target of xstring
  | DomIntros
  | Tailrec

datatype fundef_config
  = FundefConfig of
   {
    sequential: bool,
    default: string,
    preprocessor: string option,
    target: xstring option,
    domintros: bool,
    tailrec: bool
   }


val default_config = FundefConfig { sequential=false, default="%x. arbitrary", preprocessor=NONE,
                                    target=NONE, domintros=false, tailrec=false }

val fun_config = FundefConfig { sequential=true, default="%x. arbitrary", preprocessor=NONE, 
                                target=NONE, domintros=false, tailrec=false }

fun apply_opt Sequential (FundefConfig {sequential, default, preprocessor, target, domintros,tailrec}) = 
    FundefConfig {sequential=true, default=default, preprocessor=preprocessor, target=target, domintros=domintros, tailrec=tailrec }
  | apply_opt (Default d) (FundefConfig {sequential, default, preprocessor, target, domintros,tailrec}) = 
    FundefConfig {sequential=sequential, default=d, preprocessor=preprocessor, target=target, domintros=domintros, tailrec=tailrec }
  | apply_opt (Preprocessor p) (FundefConfig {sequential, default, preprocessor, target, domintros,tailrec}) = 
    FundefConfig {sequential=sequential, default=default, preprocessor=SOME p, target=target, domintros=domintros, tailrec=tailrec }
  | apply_opt (Target t) (FundefConfig {sequential, default, preprocessor, target, domintros,tailrec }) =
    FundefConfig {sequential=sequential, default=default, preprocessor=preprocessor, target=SOME t, domintros=domintros, tailrec=tailrec }
  | apply_opt DomIntros (FundefConfig {sequential, default, preprocessor, target, domintros,tailrec }) =
    FundefConfig {sequential=sequential, default=default, preprocessor=preprocessor, target=target, domintros=true,tailrec=tailrec }
  | apply_opt Tailrec (FundefConfig {sequential, default, preprocessor, target, domintros,tailrec }) =
    FundefConfig {sequential=sequential, default=default, preprocessor=preprocessor, target=target, domintros=domintros,tailrec=true } 

fun target_of (FundefConfig {target, ...}) = target

local 
  structure P = OuterParse and K = OuterKeyword 

  val opt_sequential = Scan.optional ((P.$$$ "(" |-- P.$$$ "sequential" --| P.$$$ ")") >> K true) false
                       
  val option_parser = (P.$$$ "sequential" >> K Sequential)
                   || ((P.reserved "default" |-- P.term) >> Default)
                   || (P.reserved "domintros" >> K DomIntros)
                   || (P.reserved "tailrec" >> K Tailrec)
                   || ((P.$$$ "in" |-- P.xname) >> Target)

  fun config_parser def = (Scan.optional (P.$$$ "(" |-- P.!!! (P.list1 (P.group "option" option_parser)) --| P.$$$ ")") [])
                          >> (fn opts => fold apply_opt opts def)

  fun pipe_list1 s = P.enum1 "|" s

  val otherwise = P.$$$ "(" |-- P.$$$ "otherwise" --| P.$$$ ")"

  fun pipe_error t = P.!!! (Scan.fail_with (K (cat_lines ["Equations must be separated by " ^ quote "|", quote t])))

  val statement_ow = SpecParse.opt_thm_name ":" -- (P.prop -- Scan.optional (otherwise >> K true) false)
                     --| Scan.ahead ((P.term :-- pipe_error) || Scan.succeed ("",""))

  val statements_ow = pipe_list1 statement_ow
in
  fun fundef_parser default_cfg = config_parser default_cfg -- P.fixes --| P.$$$ "where" -- statements_ow
end

end

(* Common Abbreviations *)

structure FundefAbbrev =
struct

fun implies_elim_swp x y = implies_elim y x

(* HOL abbreviations *)
val boolT = HOLogic.boolT
val mk_prod = HOLogic.mk_prod
val mk_eq = HOLogic.mk_eq
val eq_const = HOLogic.eq_const
val Trueprop = HOLogic.mk_Trueprop
val mk_relT = HOLogic.mk_setT o HOLogic.mk_prodT

fun free_to_var (Free (v,T)) = Var ((v,0),T)
  | free_to_var _ = raise Match

fun var_to_free (Var ((v,_),T)) = Free (v,T)
  | var_to_free _ = raise Match


end

(*  Title:      HOL/Tools/function_package/fundef_common.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions. 
Common definitions and other infrastructure.
*)

structure FundefCommon =
struct

local open FundefLib in

(* Profiling *)
val profile = ref false;

fun PROFILE msg = if !profile then timeap_msg msg else I


val acc_const_name = "Accessible_Part.accp"
fun mk_acc domT R =
    Const (acc_const_name, (domT --> domT --> HOLogic.boolT) --> domT --> HOLogic.boolT) $ R 

val function_name = suffix "C"
val graph_name = suffix "_graph"
val rel_name = suffix "_rel"
val dom_name = suffix "_dom"


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

      (* contains no logical entities: invariant under morphisms *)
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
      FundefCtxData { add_simps = add_simps,
                      fs = map term fs, R = term R, psimps = fact psimps, 
                      pinducts = fact pinducts, termination = thm termination,
                      defname = name defname }
    end

structure FundefData = GenericDataFun
(
  type T = (term * fundef_context_data) NetRules.T;
  val empty = NetRules.init
    (op aconv o pairself fst : (term * fundef_context_data) * (term * fundef_context_data) -> bool)
    fst;
  val copy = I;
  val extend = I;
  fun merge _ (tab1, tab2) = NetRules.merge (tab1, tab2)
);


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
          SOME (morph_fundef_data (inst_morph (Thm.match (cterm_of thy (fst data), ct))) (snd data))
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

structure TerminationRule = GenericDataFun
(
  type T = thm list
  val empty = []
  val extend = I
  fun merge _ = Thm.merge_thms
);

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
  | Target of xstring
  | DomIntros
  | Tailrec

datatype fundef_config
  = FundefConfig of
   {
    sequential: bool,
    default: string,
    target: xstring option,
    domintros: bool,
    tailrec: bool
   }

fun apply_opt Sequential (FundefConfig {sequential, default, target, domintros,tailrec}) = 
    FundefConfig {sequential=true, default=default, target=target, domintros=domintros, tailrec=tailrec}
  | apply_opt (Default d) (FundefConfig {sequential, default, target, domintros,tailrec}) = 
    FundefConfig {sequential=sequential, default=d, target=target, domintros=domintros, tailrec=tailrec}
  | apply_opt (Target t) (FundefConfig {sequential, default, target, domintros,tailrec}) =
    FundefConfig {sequential=sequential, default=default, target=SOME t, domintros=domintros, tailrec=tailrec}
  | apply_opt DomIntros (FundefConfig {sequential, default, target, domintros,tailrec}) =
    FundefConfig {sequential=sequential, default=default, target=target, domintros=true,tailrec=tailrec}
  | apply_opt Tailrec (FundefConfig {sequential, default, target, domintros,tailrec}) =
    FundefConfig {sequential=sequential, default=default, target=target, domintros=domintros,tailrec=true}

fun target_of (FundefConfig {target, ...}) = target

val default_config = FundefConfig { sequential=false, default="%x. arbitrary", 
                                    target=NONE, domintros=false, tailrec=false }


(* Common operations on equations *)

fun open_all_all (Const ("all", _) $ Abs (n, T, b)) = apfst (cons (n, T)) (open_all_all b)
  | open_all_all t = ([], t)

fun split_def ctxt geq =
    let
      fun input_error msg = cat_lines [msg, ProofContext.string_of_term ctxt geq]
      val (qs, imp) = open_all_all geq

      val gs = Logic.strip_imp_prems imp
      val eq = Logic.strip_imp_concl imp

      val (f_args, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop eq)
          handle TERM _ => error (input_error "Not an equation")

      val (head, args) = strip_comb f_args

      val fname = fst (dest_Free head)
          handle TERM _ => error (input_error "Head symbol must not be a bound variable")
    in
      (fname, qs, gs, args, rhs)
    end

exception ArgumentCount of string

fun mk_arities fqgars =
    let fun f (fname, _, _, args, _) arities =
            let val k = length args
            in
              case Symtab.lookup arities fname of
                NONE => Symtab.update (fname, k) arities
              | SOME i => (if i = k then arities else raise ArgumentCount fname)
            end
    in
      fold f fqgars Symtab.empty
    end


(* Check for all sorts of errors in the input *)
fun check_defs ctxt fixes eqs =
    let
      val fnames = map (fst o fst) fixes
                                
      fun check geq = 
          let
            fun input_error msg = cat_lines [msg, ProofContext.string_of_term ctxt geq]
                                  
            val fqgar as (fname, qs, gs, args, rhs) = split_def ctxt geq
                                 
            val _ = fname mem fnames 
                    orelse error (input_error ("Head symbol of left hand side must be " ^ plural "" "one out of " fnames 
                                               ^ commas_quote fnames))
                                            
            fun add_bvs t is = add_loose_bnos (t, 0, is)
            val rvs = (add_bvs rhs [] \\ fold add_bvs args [])
                        |> map (fst o nth (rev qs))
                      
            val _ = null rvs orelse error (input_error ("Variable" ^ plural " " "s " rvs ^ commas_quote rvs
                                                        ^ " occur" ^ plural "s" "" rvs ^ " on right hand side only:"))
                                    
            val _ = forall (not o Term.exists_subterm (fn Free (n, _) => n mem fnames | _ => false)) gs 
                    orelse error (input_error "Recursive Calls not allowed in premises")

            val freeargs = map (fn t => subst_bounds (rev (map Free qs), t)) args
            val funvars = filter (fn q => exists (exists_subterm (fn (Free q') $ _ => q = q' | _ => false)) freeargs) qs
            val _ = null funvars
                    orelse (warning (cat_lines ["Bound variable" ^ plural " " "s " funvars ^ commas_quote (map fst funvars) ^  
                                                " occur" ^ plural "s" "" funvars ^ " in function position.",  
                                                "Misspelled constructor???"]); true)
          in
            fqgar
          end
          
      fun check_sorts ((fname, fT), _) =
          Sorts.of_sort (Sign.classes_of (ProofContext.theory_of ctxt)) (fT, HOLogic.typeS)
          orelse error ("Type of " ^ quote fname ^ " is not of sort " ^ quote "type" ^ ".")

      val _ = map check_sorts fixes

      val _ = mk_arities (map check eqs)
          handle ArgumentCount fname => 
                 error ("Function " ^ quote fname ^ " has different numbers of arguments in different equations")
    in
      ()
    end

(* Preprocessors *)

type fixes = ((string * typ) * mixfix) list
type 'a spec = ((bstring * Attrib.src list) * 'a list) list
type preproc = fundef_config -> bool list -> Proof.context -> fixes -> term spec 
               -> (term list * (thm list -> thm spec) * (thm list -> thm list list))

val fname_of = fst o dest_Free o fst o strip_comb o fst o HOLogic.dest_eq o HOLogic.dest_Trueprop o Logic.strip_imp_concl o snd o dest_all_all

fun empty_preproc check _ _ ctxt fixes spec =
    let 
      val (nas,tss) = split_list spec
      val _ = check ctxt fixes (flat tss)
      val ts = flat tss
      val fnames = map (fst o fst) fixes
      val indices = map (fn eq => find_index (curry op = (fname_of eq)) fnames) ts

      fun sort xs = partition_list (fn i => fn (j,_) => i = j) 0 (length fnames - 1) (indices ~~ xs)
                        |> map (map snd)
    in
      (ts, curry op ~~ nas o Library.unflat tss, sort)
    end

structure Preprocessor = GenericDataFun
(
  type T = preproc
  val empty : T = empty_preproc check_defs
  val extend = I
  fun merge _ (a, _) = a
);

val get_preproc = Preprocessor.get o Context.Proof
val set_preproc = Preprocessor.map o K



local 
  structure P = OuterParse and K = OuterKeyword 

  val opt_sequential = Scan.optional ((P.$$$ "(" |-- P.$$$ "sequential" --| P.$$$ ")") >> K true) false
                       
  val option_parser = (P.$$$ "sequential" >> K Sequential)
                   || ((P.reserved "default" |-- P.term) >> Default)
                   || (P.reserved "domintros" >> K DomIntros)
                   || (P.reserved "tailrec" >> K Tailrec)
                   || ((P.$$$ "in" |-- P.xname) >> Target)

  fun config_parser default = (Scan.optional (P.$$$ "(" |-- P.!!! (P.list1 (P.group "option" option_parser)) --| P.$$$ ")") [])
                              >> (fn opts => fold apply_opt opts default)

  val otherwise = P.$$$ "(" |-- P.$$$ "otherwise" --| P.$$$ ")"

  fun pipe_error t = P.!!! (Scan.fail_with (K (cat_lines ["Equations must be separated by " ^ quote "|", quote t])))

  val statement_ow = SpecParse.opt_thm_name ":" -- (P.prop -- Scan.optional (otherwise >> K true) false)
                     --| Scan.ahead ((P.term :-- pipe_error) || Scan.succeed ("",""))

  val statements_ow = P.enum1 "|" statement_ow

  val flags_statements = statements_ow
                         >> (fn sow => (map (snd o snd) sow, map (apsnd fst) sow))
in
  fun fundef_parser default_cfg = (config_parser default_cfg -- P.fixes --| P.$$$ "where" -- flags_statements)
end


end
end


(*  Title:      HOL/Tools/Function/fundef_common.ML
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions. 
Common definitions and other infrastructure.
*)

structure Function_Common =
struct

local open Function_Lib in

(* Profiling *)
val profile = Unsynchronized.ref false;

fun PROFILE msg = if !profile then timeap_msg msg else I


val acc_const_name = @{const_name accp}
fun mk_acc domT R =
    Const (acc_const_name, (domT --> domT --> HOLogic.boolT) --> domT --> HOLogic.boolT) $ R 

val function_name = suffix "C"
val graph_name = suffix "_graph"
val rel_name = suffix "_rel"
val dom_name = suffix "_dom"

(* Termination rules *)

structure TerminationRule = Generic_Data
(
  type T = thm list
  val empty = []
  val extend = I
  val merge = Thm.merge_thms
);

val get_termination_rules = TerminationRule.get
val store_termination_rule = TerminationRule.map o cons
val apply_termination_rule = resolve_tac o get_termination_rules o Context.Proof


(* Function definition result data *)

datatype function_result =
  FunctionResult of
     {
      fs: term list,
      G: term,
      R: term,

      psimps : thm list, 
      trsimps : thm list option, 

      simple_pinducts : thm list, 
      cases : thm,
      termination : thm,
      domintros : thm list option
     }


datatype function_context_data =
  FunctionCtxData of
     {
      defname : string,

      (* contains no logical entities: invariant under morphisms *)
      add_simps : (binding -> binding) -> string -> (binding -> binding) ->
        Attrib.src list -> thm list -> local_theory -> thm list * local_theory,

      case_names : string list,

      fs : term list,
      R : term,
      
      psimps: thm list,
      pinducts: thm list,
      termination: thm
     }

fun morph_function_data (FunctionCtxData {add_simps, case_names, fs, R, 
                                      psimps, pinducts, termination, defname}) phi =
    let
      val term = Morphism.term phi val thm = Morphism.thm phi val fact = Morphism.fact phi
      val name = Binding.name_of o Morphism.binding phi o Binding.name
    in
      FunctionCtxData { add_simps = add_simps, case_names = case_names,
                      fs = map term fs, R = term R, psimps = fact psimps, 
                      pinducts = fact pinducts, termination = thm termination,
                      defname = name defname }
    end

structure FunctionData = Generic_Data
(
  type T = (term * function_context_data) Item_Net.T;
  val empty : T = Item_Net.init (op aconv o pairself fst) (single o fst);
  val extend = I;
  fun merge tabs : T = Item_Net.merge tabs;
);

val get_function = FunctionData.get o Context.Proof;


(* Generally useful?? *)
fun lift_morphism thy f = 
    let 
      val term = Drule.term_rule thy f
    in
      Morphism.thm_morphism f $> Morphism.term_morphism term 
       $> Morphism.typ_morphism (Logic.type_map term)
    end

fun import_function_data t ctxt =
    let
      val thy = ProofContext.theory_of ctxt
      val ct = cterm_of thy t
      val inst_morph = lift_morphism thy o Thm.instantiate 

      fun match (trm, data) = 
          SOME (morph_function_data data (inst_morph (Thm.match (cterm_of thy trm, ct))))
          handle Pattern.MATCH => NONE
    in 
      get_first match (Item_Net.retrieve (get_function ctxt) t)
    end

fun import_last_function ctxt =
    case Item_Net.content (get_function ctxt) of
      [] => NONE
    | (t, data) :: _ =>
      let 
        val ([t'], ctxt') = Variable.import_terms true [t] ctxt
      in
        import_function_data t' ctxt'
      end

val all_function_data = Item_Net.content o get_function

fun add_function_data (data as FunctionCtxData {fs, termination, ...}) =
    FunctionData.map (fold (fn f => Item_Net.update (f, data)) fs)
    #> store_termination_rule termination


(* Simp rules for termination proofs *)

structure Termination_Simps = Named_Thms
(
  val name = "termination_simp" 
  val description = "Simplification rule for termination proofs"
);


(* Default Termination Prover *)

structure TerminationProver = Generic_Data
(
  type T = Proof.context -> Proof.method
  val empty = (fn _ => error "Termination prover not configured")
  val extend = I
  fun merge (a, b) = b  (* FIXME ? *)
);

val set_termination_prover = TerminationProver.put
val get_termination_prover = TerminationProver.get o Context.Proof


(* Configuration management *)
datatype function_opt 
  = Sequential
  | Default of string
  | DomIntros
  | No_Partials
  | Tailrec

datatype function_config
  = FunctionConfig of
   {
    sequential: bool,
    default: string,
    domintros: bool,
    partials: bool,
    tailrec: bool
   }

fun apply_opt Sequential (FunctionConfig {sequential, default, domintros, partials, tailrec}) =
    FunctionConfig {sequential=true, default=default, domintros=domintros, partials=partials, tailrec=tailrec}
  | apply_opt (Default d) (FunctionConfig {sequential, default, domintros, partials, tailrec}) =
    FunctionConfig {sequential=sequential, default=d, domintros=domintros, partials=partials, tailrec=tailrec}
  | apply_opt DomIntros (FunctionConfig {sequential, default, domintros, partials, tailrec}) =
    FunctionConfig {sequential=sequential, default=default, domintros=true, partials=partials, tailrec=tailrec}
  | apply_opt Tailrec (FunctionConfig {sequential, default, domintros, partials, tailrec}) =
    FunctionConfig {sequential=sequential, default=default, domintros=domintros, partials=partials, tailrec=true}
  | apply_opt No_Partials (FunctionConfig {sequential, default, domintros, partials, tailrec}) =
    FunctionConfig {sequential=sequential, default=default, domintros=domintros, partials=false, tailrec=true}

val default_config =
  FunctionConfig { sequential=false, default="%x. undefined" (*FIXME dynamic scoping*), 
    domintros=false, partials=true, tailrec=false }


(* Analyzing function equations *)

fun split_def ctxt geq =
    let
      fun input_error msg = cat_lines [msg, Syntax.string_of_term ctxt geq]
      val qs = Term.strip_qnt_vars "all" geq
      val imp = Term.strip_qnt_body "all" geq
      val (gs, eq) = Logic.strip_horn imp

      val (f_args, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop eq)
          handle TERM _ => error (input_error "Not an equation")

      val (head, args) = strip_comb f_args

      val fname = fst (dest_Free head)
          handle TERM _ => error (input_error "Head symbol must not be a bound variable")
    in
      (fname, qs, gs, args, rhs)
    end

(* Check for all sorts of errors in the input *)
fun check_defs ctxt fixes eqs =
    let
      val fnames = map (fst o fst) fixes
                                
      fun check geq = 
          let
            fun input_error msg = error (cat_lines [msg, Syntax.string_of_term ctxt geq])
                                  
            val fqgar as (fname, qs, gs, args, rhs) = split_def ctxt geq
                                 
            val _ = fname mem fnames 
                    orelse input_error 
                             ("Head symbol of left hand side must be " 
                              ^ plural "" "one out of " fnames ^ commas_quote fnames)
                                            
            val _ = length args > 0 orelse input_error "Function has no arguments:"

            fun add_bvs t is = add_loose_bnos (t, 0, is)
            val rvs = (subtract (op =) (fold add_bvs args []) (add_bvs rhs []))
                        |> map (fst o nth (rev qs))
                      
            val _ = null rvs orelse input_error 
                        ("Variable" ^ plural " " "s " rvs ^ commas_quote rvs
                         ^ " occur" ^ plural "s" "" rvs ^ " on right hand side only:")
                                    
            val _ = forall (not o Term.exists_subterm 
                             (fn Free (n, _) => n mem fnames | _ => false)) (gs @ args)
                    orelse input_error "Defined function may not occur in premises or arguments"

            val freeargs = map (fn t => subst_bounds (rev (map Free qs), t)) args
            val funvars = filter (fn q => exists (exists_subterm (fn (Free q') $ _ => q = q' | _ => false)) freeargs) qs
            val _ = null funvars
                    orelse (warning (cat_lines 
                    ["Bound variable" ^ plural " " "s " funvars 
                     ^ commas_quote (map fst funvars) ^  
                     " occur" ^ plural "s" "" funvars ^ " in function position.",  
                     "Misspelled constructor???"]); true)
          in
            (fname, length args)
          end

      val _ = AList.group (op =) (map check eqs)
        |> map (fn (fname, ars) =>
             length (distinct (op =) ars) = 1
             orelse error ("Function " ^ quote fname ^
                           " has different numbers of arguments in different equations"))

      fun check_sorts ((fname, fT), _) =
          Sorts.of_sort (Sign.classes_of (ProofContext.theory_of ctxt)) (fT, HOLogic.typeS)
          orelse error (cat_lines 
          ["Type of " ^ quote fname ^ " is not of sort " ^ quote "type" ^ ":",
           setmp_CRITICAL show_sorts true (Syntax.string_of_typ ctxt) fT])

      val _ = map check_sorts fixes
    in
      ()
    end

(* Preprocessors *)

type fixes = ((string * typ) * mixfix) list
type 'a spec = (Attrib.binding * 'a list) list
type preproc = function_config -> Proof.context -> fixes -> term spec 
               -> (term list * (thm list -> thm spec) * (thm list -> thm list list) * string list)

val fname_of = fst o dest_Free o fst o strip_comb o fst 
 o HOLogic.dest_eq o HOLogic.dest_Trueprop o Logic.strip_imp_concl o snd o dest_all_all

fun mk_case_names i "" k = mk_case_names i (string_of_int (i + 1)) k
  | mk_case_names _ n 0 = []
  | mk_case_names _ n 1 = [n]
  | mk_case_names _ n k = map (fn i => n ^ "_" ^ string_of_int i) (1 upto k)

fun empty_preproc check _ ctxt fixes spec =
    let 
      val (bnds, tss) = split_list spec
      val ts = flat tss
      val _ = check ctxt fixes ts
      val fnames = map (fst o fst) fixes
      val indices = map (fn eq => find_index (curry op = (fname_of eq)) fnames) ts

      fun sort xs = partition_list (fn i => fn (j,_) => i = j) 0 (length fnames - 1) 
                                   (indices ~~ xs)
                        |> map (map snd)

      (* using theorem names for case name currently disabled *)
      val cnames = map_index (fn (i, _) => mk_case_names i "" 1) bnds |> flat
    in
      (ts, curry op ~~ bnds o Library.unflat tss, sort, cnames)
    end

structure Preprocessor = Generic_Data
(
  type T = preproc
  val empty : T = empty_preproc check_defs
  val extend = I
  fun merge (a, _) = a
);

val get_preproc = Preprocessor.get o Context.Proof
val set_preproc = Preprocessor.map o K



local 
  structure P = OuterParse and K = OuterKeyword

  val option_parser = 
      P.group "option" ((P.reserved "sequential" >> K Sequential)
                    || ((P.reserved "default" |-- P.term) >> Default)
                    || (P.reserved "domintros" >> K DomIntros)
                    || (P.reserved "no_partials" >> K No_Partials)
                    || (P.reserved "tailrec" >> K Tailrec))

  fun config_parser default = 
      (Scan.optional (P.$$$ "(" |-- P.!!! (P.list1 option_parser) --| P.$$$ ")") [])
        >> (fn opts => fold apply_opt opts default)
in
  fun function_parser default_cfg = 
      config_parser default_cfg -- P.fixes -- SpecParse.where_alt_specs
end


end
end


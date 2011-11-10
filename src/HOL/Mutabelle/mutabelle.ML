(*  Title:      HOL/Mutabelle/mutabelle.ML
    Author:     Veronika Ortner, TU Muenchen

Mutation of theorems.
*)

signature MUTABELLE =
sig
  exception WrongPath of string;
  exception WrongArg of string;
  val freeze : term -> term
  val mutate_exc : term -> string list -> int -> term list 
  val mutate_sign : term -> theory -> (string * string) list -> int -> term list 
  val mutate_mix : term -> theory -> string list -> 
   (string * string) list -> int -> term list
(*  val qc_test : term list -> (typ * typ) list -> theory ->
  int -> int -> int * Thm.cterm list * int * (Thm.cterm * (string * Thm.cterm) list) list
  val qc_test_file : bool -> term list -> (typ * typ) list 
   -> theory -> int -> int -> string -> unit
  val mutqc_file_exc : theory -> string list ->
  int -> Thm.thm -> (typ * typ) list -> int -> int -> string -> unit
  val mutqc_file_sign : theory -> (string * string) list ->
  int -> Thm.thm -> (typ * typ) list -> int -> int -> string -> unit
  val mutqc_file_mix : theory -> string list -> (string * string) list ->
  int -> Thm.thm -> (typ * typ) list -> int -> int -> string -> unit
  val mutqc_file_rec_exc : theory -> string list -> int ->
  Thm.thm list -> (typ * typ) list -> int -> int -> string list -> unit
  val mutqc_file_rec_sign : theory -> (string * string) list -> int ->
  Thm.thm list -> (typ * typ) list -> int -> int -> string list -> unit
  val mutqc_file_rec_mix : theory -> string list -> (string * string) list ->
  int -> Thm.thm list -> (typ * typ) list -> int -> int -> string list -> unit
  val mutqc_thy_exc : theory -> theory ->
  string list -> int -> (typ * typ) list -> int -> int -> string -> unit
  val mutqc_thy_sign : theory -> theory -> (string * string) list ->
  int -> (typ * typ) list -> int -> int -> string -> unit
  val mutqc_thy_mix : theory -> theory -> string list -> (string * string) list ->
  int -> (typ * typ) list -> int -> int -> string -> unit
  val mutqc_file_stat_sign : theory -> (string * string) list ->
  int -> Thm.thm list -> (typ * typ) list -> int -> int -> string -> unit
  val mutqc_file_stat_exc : theory -> string list ->
  int -> Thm.thm list -> (typ * typ) list -> int -> int -> string -> unit
  val mutqc_file_stat_mix : theory -> string list -> (string * string) list ->
  int -> Thm.thm list -> (typ * typ) list -> int -> int -> string -> unit
  val mutqc_thystat_exc : (string -> thm -> bool) -> theory -> theory ->
  string list -> int -> (typ * typ) list -> int -> int -> string -> unit
  val mutqc_thystat_sign : (string -> thm -> bool) -> theory -> theory -> (string * string) list ->
  int -> (typ * typ) list -> int -> int -> string -> unit
  val mutqc_thystat_mix : (string -> thm -> bool) -> theory -> theory -> string list -> 
  (string * string) list -> int -> (typ * typ) list -> int -> int -> string -> unit
  val canonize_term: term -> string list -> term
*)  
  val all_unconcealed_thms_of : theory -> (string * thm) list
end;

structure Mutabelle : MUTABELLE = 
struct

fun all_unconcealed_thms_of thy =
  let
    val facts = Global_Theory.facts_of thy
  in
    Facts.fold_static
      (fn (s, ths) =>
        if Facts.is_concealed facts s then I else append (map (`(Thm.get_name_hint)) ths))
      facts []
  end;

fun thms_of thy = filter (fn (_, th) =>
   Context.theory_name (theory_of_thm th) = Context.theory_name thy) (all_unconcealed_thms_of thy);

fun consts_of thy =
 let
   val (namespace, const_table) = #constants (Consts.dest (Sign.consts_of thy))
   val consts = Symtab.dest const_table
 in
   map_filter (fn (s, (T, NONE)) => SOME (s, T) | _ => NONE)
     (filter_out (fn (s, _) => Name_Space.is_concealed namespace s) consts)
 end;


(*possibility to print a given term for debugging purposes*)

fun prt x = Pretty.writeln (Syntax.pretty_term_global @{theory Main} x);

val debug = (Unsynchronized.ref false);
fun debug_msg mutterm = if (!debug) then (prt mutterm) else ();


(*thrown in case the specified path doesn't exist in the specified term*)

exception WrongPath of string;


(*thrown in case the arguments did not fit to the function*)

exception WrongArg of string; 

(*Rename the bound variables in a term with the minimal Index min of 
bound variables. Variable (Bound(min)) will be renamed to Bound(0) etc. 
This is needed in course auf evaluation of contexts.*)

fun rename_bnds curTerm 0 = curTerm
 | rename_bnds (Bound(i)) minInd = 
   let 
     val erg = if (i-minInd < 0) then 0 else (i - minInd)
   in 
     Bound(erg)
   end
 | rename_bnds (Abs(name,t,uTerm)) minInd = 
   Abs(name,t,(rename_bnds uTerm minInd))
 | rename_bnds (fstUTerm $ sndUTerm) minInd =
   (rename_bnds fstUTerm minInd) $ (rename_bnds sndUTerm minInd)
 | rename_bnds elseTerm minInd = elseTerm;





(*Partition a term in its subterms and create an entry 
(term * type * abscontext * mincontext * path) 
for each term in the return list 
e.g: getSubTermList Abs(y, int, Const(f,int->int) $ Const(x,int) $ Bound(0))
will give       [(Const(f,int->int),int->int,[int],[],[00]),
               (Const(x,int),int,[int],[],[010]),
               (Bound(0),int,[int],[int],[110]),
               (Const(x,int) $ Bound(0),type,[int],[int],[10]),
               (Const(f,int->int) $ Const(x,int) $ Bound(0),type,[int],[int],[0],
               (Abs (y,int,Const(f,int->int) $ const(x,int) $ Bound(0)),type,[],[],[])]
                *)

fun getSubTermList (Const(name,t)) abscontext path acc =
   (Const(name,t),t,abscontext,abscontext,path)::acc
 | getSubTermList (Free(name,t)) abscontext path acc =
   (Free(name,t),t,abscontext,abscontext,path)::acc
 | getSubTermList (Var(indname,t)) abscontext path acc =
   (Var(indname,t),t,abscontext,abscontext,path)::acc
 | getSubTermList (Bound(i)) abscontext path acc =
   (Bound(0),nth abscontext i,abscontext, Library.drop i abscontext,path)::acc
 | getSubTermList (Abs(name,t,uTerm)) abscontext path acc = 
   let 
     val curTerm = Abs(name,t,uTerm)
     val bnos = Term.add_loose_bnos (curTerm,0,[])
     val minInd = if (bnos = []) then 0 
       else Library.foldl (fn (n,m) => if (n<m) then n else m) (hd bnos,tl bnos)
     val newTerm = rename_bnds curTerm minInd
     val newContext = Library.drop minInd abscontext
   in 
     getSubTermList uTerm (t::abscontext) (0::path) 
               ((newTerm,(fastype_of1 (abscontext, curTerm)),abscontext,newContext,path)::acc)
   end
 | getSubTermList (fstUTerm $ sndUTerm) abscontext path acc = 
   let 
     val curTerm = (fstUTerm $ sndUTerm)
     val bnos = Term.add_loose_bnos (curTerm, 0, [])
     val minInd = if (bnos = []) then 0
       else Library.foldl (fn (n,m) => if (n<m) then n else m) (hd bnos,tl bnos)
     val newTerm = rename_bnds curTerm minInd
     val newContext = Library.drop minInd abscontext
   in 
     getSubTermList fstUTerm abscontext (0::path) 
       (getSubTermList sndUTerm abscontext (1::path) 
         ((newTerm,(fastype_of1 (abscontext, curTerm)),abscontext,newContext,path)::acc)) 
   end;  





(*tests if the given element ist in the given list*)

fun in_list elem [] = false
 | in_list elem (x::xs) = if (elem = x) then true else in_list elem xs;


(*Evaluate if the longContext is more special as the shortContext. 
If so, a term with shortContext can be substituted in the place of a 
term with longContext*)

fun is_morespecial longContext shortContext = 
 let 
   val revlC = rev longContext
   val revsC = rev shortContext
   fun is_prefix [] longList = true
     | is_prefix shList [] = false
     | is_prefix (x::xs) (y::ys) = if (x=y) then is_prefix xs ys else false
 in 
   is_prefix revsC revlC
 end;


(*takes a (term * type * context * context * path)-tupel and searches in the specified list for 
terms with the same type and appropriate context. Returns a (term * path) list of these terms.
Used in order to generate a list of type-equal subterms of the original term*)

fun searchForMutatableSubTerm (sterm,stype,sabsContext,sminContext,spath) [] resultList = 
   resultList
 | searchForMutatableSubTerm (sterm,stype,sabsContext,sminContext,spath) 
   ((hdterm,hdtype,hdabsContext,hdminContext,hdpath)::xs) resultList = 
   if ((stype = hdtype) andalso (is_morespecial sabsContext hdminContext) 
     andalso (is_morespecial hdabsContext sminContext)) 
   then searchForMutatableSubTerm (sterm,stype,sabsContext,sminContext,spath) xs 
     ((hdterm,hdabsContext,hdminContext,hdpath)::resultList) 
   else searchForMutatableSubTerm (sterm,stype,sabsContext,sminContext,spath) xs resultList;


(*evaluates if the given function is in the passed list of forbidden functions*)

fun in_list_forb consSig (consNameStr,consType) [] = false
 | in_list_forb consSig (consNameStr,consType) ((forbNameStr,forbTypeStr)::xs) = 
   let 
     val forbType = Syntax.read_typ_global consSig forbTypeStr
     val typeSignature = #tsig (Sign.rep_sg consSig)
   in
     if ((consNameStr = forbNameStr) 
       andalso (Type.typ_instance typeSignature (consType,(Logic.varifyT_global forbType))))
     then true
     else in_list_forb consSig (consNameStr,consType) xs
   end;



(*searches in the given signature Consts with the same type as sterm and 
returns a list of those terms*)

fun searchForSignatureMutations (sterm,stype) consSig forbidden_funs = 
 let 
   val sigConsTypeList = consts_of consSig;
   val typeSignature = #tsig (Sign.rep_sg consSig)
 in 
   let 
     fun recursiveSearch mutatableTermList [] = mutatableTermList
       | recursiveSearch mutatableTermList ((ConsName,ConsType)::xs) = 
         if (Type.typ_instance typeSignature (stype,ConsType) 
           andalso (not (sterm = Const(ConsName,stype))) 
           andalso (not (in_list_forb consSig (ConsName,ConsType) forbidden_funs))) 
         then recursiveSearch ((Term.Const(ConsName,stype), [], [], [5])::mutatableTermList) xs
         else recursiveSearch mutatableTermList xs
     in
       recursiveSearch [] sigConsTypeList
     end
   end;     


(*generates a list of terms that can be used instead of the passed subterm in the original term. These terms either have
the same type and appropriate context and are generated from the list of subterms either - in case of a Const-term they have been found
in the current signature.
This function has 3 versions:
0: no instertion of signature functions, 
  only terms in the subTermList with the same type and appropriate context as the passed term are returned
1: no exchange of subterms,
  only signature functions are inserted at the place of type-aequivalent Conses
2: mixture of the two other versions. insertion of signature functions and exchange of subterms*)

fun searchForMutatableTerm 0 (sterm,stype,sabscontext,smincontext,spath) 
   subTerms consSig resultList forbidden_funs =
   searchForMutatableSubTerm (sterm,stype,sabscontext,smincontext,spath) subTerms resultList
 | searchForMutatableTerm 1 (Const(constName,constType),stype,sabscontext,smincontext,spath) 
   subTerms consSig resultList forbidden_funs = 
   searchForSignatureMutations (Const(constName,constType),stype) consSig forbidden_funs
 | searchForMutatableTerm 1 _ _ _ _ _ = []
 | searchForMutatableTerm 2 (Const(constName,constType),stype,sabscontext,smincontext,spath) 
   subTerms consSig resultList forbidden_funs = 
     let 
       val subtermMutations = searchForMutatableSubTerm 
         (Const(constName,constType),stype,sabscontext,smincontext,spath) subTerms resultList
       val signatureMutations = searchForSignatureMutations 
         (Const(constName,constType),stype) consSig forbidden_funs
     in
       subtermMutations@signatureMutations
     end
 | searchForMutatableTerm 2 (sterm,stype,sabscontext,smincontext,spath) 
   subTerms consSig resultList forbidden_funs =
   searchForMutatableSubTerm (sterm,stype,sabscontext,smincontext,spath) subTerms resultList
 | searchForMutatableTerm i _ _ _ _ _ = 
   raise WrongArg("Version " ^ string_of_int i ^ 
     " doesn't exist for function searchForMutatableTerm!") ;




(*evaluates if the two terms with paths passed as arguments can be exchanged, i.e. evaluates if one of the terms is a subterm of the other one*)  

fun areReplacable [] [] = false
 | areReplacable fstPath [] = false
 | areReplacable [] sndPath = false
 | areReplacable (x::xs) (y::ys) = if (x=y) then areReplacable xs ys else true; 




(*substitutes the term at the position of the first list in fstTerm by sndTerm. 
The lists represent paths as generated by createSubTermList*)

fun substitute [] fstTerm sndTerm = sndTerm
 | substitute (_::xs) (Abs(s,T,subTerm)) sndTerm = Abs(s,T,(substitute xs subTerm sndTerm))
 | substitute (0::xs) (t $ u) sndTerm = substitute xs t sndTerm $ u 
 | substitute (1::xs) (t $ u) sndTerm = t $ substitute xs u sndTerm
 | substitute (_::xs) _ sndTerm = 
   raise WrongPath ("The Term could not be found at the specified position"); 


(*get the subterm with the specified path in myTerm*)

fun getSubTerm myTerm [] = myTerm
 | getSubTerm (Abs(s,T,subTerm)) (0::xs) = getSubTerm subTerm xs
 | getSubTerm (t $ u) (0::xs) = getSubTerm t xs
 | getSubTerm (t $ u) (1::xs) = getSubTerm u xs
 | getSubTerm _ (_::xs) = 
   raise WrongPath ("The subterm could not be found at the specified position");


(*exchanges two subterms with the given paths in the original Term*)

fun replace origTerm (fstTerm, fstPath) (sndTerm, sndPath) = 
 if (areReplacable (rev fstPath) (rev sndPath))
 then substitute (rev sndPath) (substitute (rev fstPath) origTerm sndTerm) fstTerm
 else origTerm; 




(*tests if the terms with the given pathes in the origTerm are commutative
respecting the list of commutative operators (commutatives)*)

fun areCommutative origTerm fstPath sndPath commutatives =
 if (sndPath = []) 
 then false
 else
   let 
     val base = (tl sndPath)
   in
     let 
       val fstcomm = 1::0::base
       val opcomm = 0::0::base
     in
       if ((fstPath = fstcomm) andalso (is_Const (getSubTerm origTerm (rev opcomm))))
       then
         let 
           val Const(name,_) = (getSubTerm origTerm (rev opcomm))
         in
           if (in_list name commutatives) 
           then true 
           else false
         end
       else false
     end
   end;


(*Canonizes term t with the commutative operators stored in list 
commutatives*)

fun canonize_term (Const (s, T) $ t $ u) comms =
 let
   val t' = canonize_term t comms;
   val u' = canonize_term u comms;
 in 
   if member (op =) comms s andalso Term_Ord.termless (u', t')
   then Const (s, T) $ u' $ t'
   else Const (s, T) $ t' $ u'
 end
 | canonize_term (t $ u) comms = canonize_term t comms $ canonize_term u comms
 | canonize_term (Abs (s, T, t)) comms = Abs (s, T, canonize_term t comms)
 | canonize_term t comms = t;


(*inspect the passed list and mutate origTerm following the elements of the list:
if the path of the current element is [5] (dummy path), the term has been found in the signature 
and the subterm will be substituted by it
else the term has been found in the original term and the two subterms have to be exchanged
The additional parameter commutatives indicates the commutative operators  
in the term whose operands won't be exchanged*)

fun createMutatedTerms origTerm _ [] commutatives mutatedTerms = mutatedTerms
 | createMutatedTerms origTerm (hdt as (hdTerm,hdabsContext,hdminContext,hdPath))
   ((sndTerm,sndabsContext,sndminContext,sndPath)::xs) commutatives mutatedTerms = 
   if (sndPath = [5])
   then
     let 
         val canonized = canonize_term (substitute (rev hdPath) origTerm sndTerm) commutatives
       in
         if (canonized = origTerm)  
         then createMutatedTerms origTerm hdt xs commutatives mutatedTerms
         else createMutatedTerms origTerm hdt xs commutatives 
           (insert op aconv canonized mutatedTerms)
       end
     else 
       if ((areCommutative origTerm hdPath sndPath commutatives)
         orelse (areCommutative origTerm sndPath hdPath commutatives)) 
       then createMutatedTerms origTerm hdt xs commutatives mutatedTerms
       else
         let 
           val canonized = canonize_term 
             (replace origTerm
                (incr_boundvars (length sndabsContext - length hdminContext) hdTerm,
                 hdPath)
                (incr_boundvars (length hdabsContext - length sndminContext) sndTerm,
                 sndPath)) commutatives
         in
           if (not(canonized = origTerm)) 
           then createMutatedTerms origTerm hdt xs commutatives 
             (insert op aconv canonized mutatedTerms)
           else createMutatedTerms origTerm hdt xs commutatives mutatedTerms
         end;



(*mutates origTerm by exchanging subterms. The mutated terms are returned in a term list
The parameter commutatives consists of a list of commutative operators. The permutation of their 
operands won't be considered as a new term
!!!Attention!!!: The given origTerm must be canonized. Use function canonize_term!*)

fun mutate_once option origTerm tsig commutatives forbidden_funs= 
 let 
   val subTermList = getSubTermList origTerm [] [] []
 in
   let 
     fun replaceRecursively [] mutatedTerms = mutatedTerms
       | replaceRecursively ((hdTerm,hdType,hdabsContext,hdminContext,hdPath)::tail) 
         mutatedTerms =
         replaceRecursively tail (union op aconv (createMutatedTerms origTerm 
           (hdTerm,hdabsContext,hdminContext,hdPath) 
           (searchForMutatableTerm option (hdTerm,hdType,hdabsContext,hdminContext,hdPath) 
             tail tsig [] forbidden_funs) 
           commutatives []) mutatedTerms)
   in
     replaceRecursively subTermList []
   end
 end;




(*helper function in order to apply recursively the mutate_once function on a whole list of terms
Needed for the mutate function*)

fun mutate_once_rec option [] tsig commutatives forbidden_funs acc = acc
 | mutate_once_rec option (x::xs) tsig commutatives forbidden_funs acc = 
   mutate_once_rec option xs tsig commutatives forbidden_funs 
     (union op aconv (mutate_once option x tsig commutatives forbidden_funs) acc);



(*apply function mutate_once iter times on the given origTerm. *)
(*call of mutiere with canonized form of origTerm. Prevents us of the computation of
canonization in the course of insertion of new terms!*)

fun mutate option origTerm tsig commutatives forbidden_funs 0 = []
 | mutate option origTerm tsig commutatives forbidden_funs 1 = 
   mutate_once option (canonize_term origTerm commutatives) tsig commutatives forbidden_funs
 | mutate option origTerm tsig commutatives forbidden_funs iter = 
   mutate_once_rec option (mutate option origTerm tsig commutatives forbidden_funs (iter-1)) 
     tsig commutatives forbidden_funs []; 

(*mutate origTerm iter times by only exchanging subterms*)

fun mutate_exc origTerm commutatives iter =
 mutate 0 origTerm @{theory Main} commutatives [] iter;


(*mutate origTerm iter times by only inserting signature functions*)

fun mutate_sign origTerm tsig forbidden_funs iter = 
 mutate 1 origTerm tsig [] forbidden_funs iter;


(*mutate origTerm iter times by exchange of subterms and insertion of subterms*)

fun mutate_mix origTerm tsig commutatives forbidden_funs iter =
 mutate 2 origTerm tsig commutatives forbidden_funs iter;  


(*helper function in order to prettily print a list of terms*)

fun pretty xs = map (fn (id, t) => (id, (HOLogic.mk_number HOLogic.natT
 (HOLogic.dest_nat t)) handle TERM _ => t)) xs;


(*helper function for the quickcheck invocation. Evaluates the quickcheck_term function on a whole list of terms
and tries to print the exceptions*)

fun freeze (t $ u) = freeze t $ freeze u
 | freeze (Abs (s, T, t)) = Abs (s, T, freeze t)
 | freeze (Var ((a, i), T)) =
     Free (if i = 0 then a else a ^ "_" ^ string_of_int i, T)
 | freeze t = t;

fun inst_type insts (Type (s, Ts)) = Type (s, map (inst_type insts) Ts)
 | inst_type insts T = the_default HOLogic.intT (AList.lookup op = insts T);

fun preprocess thy insts t = Object_Logic.atomize_term thy
 (map_types (inst_type insts) (freeze t));

fun is_executable thy insts th =
  let
    val ctxt' = Proof_Context.init_global thy
      |> Config.put Quickcheck.size 1
      |> Config.put Quickcheck.iterations 1
    val test = Quickcheck_Common.test_term
      ("exhaustive", Exhaustive_Generators.compile_generator_expr) ctxt' false
  in  
    case try test (preprocess thy insts (prop_of th), []) of
      SOME _ => (Output.urgent_message "executable"; true)
    | NONE => (Output.urgent_message ("not executable"); false)
  end;
(*
(*create a string of a list of terms*)

fun string_of_ctermlist thy [] acc = acc
 | string_of_ctermlist thy (x::xs) acc = 
   string_of_ctermlist thy xs ((Syntax.string_of_term_global thy (term_of x)) ^ "\n" ^ acc);

(*helper function in order to decompose the counter examples generated by quickcheck*)

fun decompose_ce thy [] acc = acc
 | decompose_ce thy ((varname,varce)::xs) acc = 
   decompose_ce thy xs ("\t" ^ varname ^ " instanciated to " ^ 
     (Syntax.string_of_term_global thy (term_of varce)) ^ "\n" ^ acc);

(*helper function in order to decompose a list of counter examples*)

fun decompose_celist thy [] acc = acc
 | decompose_celist thy ((mutTerm,varcelist)::xs) acc = decompose_celist thy xs 
   ("mutated term : " ^ 
   (Syntax.string_of_term_global thy (term_of mutTerm)) ^ "\n" ^ 
   "counterexample : \n" ^ 
   (decompose_ce thy (rev varcelist) "") ^ acc); 


(*quickcheck test the list of mutants mutated by applying the type instantiations 
insts and using the quickcheck-theory usedthy. The results of quickcheck are stored
in the file with name filename. If app is true, the output will be appended to the file. 
Else it will be overwritten. *)

fun qc_test_file app mutated insts usedthy sz qciter filename =
 let 
   val statisticList = qc_test mutated insts usedthy sz qciter
   val passed = (string_of_int (#1 statisticList)) ^ 
     " terms passed the quickchecktest: \n\n" ^ 
     (string_of_ctermlist usedthy (rev (#2 statisticList)) "") 
   val counterexps = (string_of_int (#3 statisticList)) ^ 
     " terms produced a counterexample: \n\n" ^
     decompose_celist usedthy (rev (#4 statisticList)) "" 
 in
   if (app = false) 
   then File.write (Path.explode filename) (passed ^ "\n\n" ^ counterexps)
   else File.append (Path.explode filename) (passed ^ "\n\n" ^ counterexps)
 end;


(*mutate sourceThm with the mutate-version given in option and check the resulting mutants. 
The output will be written to the file with name filename*)

fun mutqc_file option usedthy commutatives forbidden_funs iter sourceThm insts sz qciter filename =
 let 
   val mutated = mutate option (prop_of sourceThm) 
     usedthy commutatives forbidden_funs iter 
 in
   qc_test_file false mutated insts usedthy sz qciter filename 
 end;

(*exchange version of function mutqc_file*)

fun mutqc_file_exc usedthy commutatives iter sourceThm insts sz qciter filename =
 mutqc_file 0 usedthy commutatives [] iter sourceThm insts sz qciter filename;


(*sinature version of function mutqc_file*)
fun mutqc_file_sign usedthy forbidden_funs iter sourceThm insts sz qciter filename= 
 mutqc_file 1 usedthy [] forbidden_funs iter sourceThm insts sz qciter filename;

(*mixed version of function mutqc_file*)

fun mutqc_file_mix usedthy commutatives forbidden_funs iter sourceThm insts sz qciter filename =
 mutqc_file 2 usedthy commutatives forbidden_funs iter sourceThm insts sz qciter filename;



(*apply function mutqc_file on a list of theorems. The output for each theorem 
will be stored in a seperated file whose filename must be indicated in a list*)

fun mutqc_file_rec option usedthy commutatives forbFuns iter [] insts sz qciter _ = ()
 | mutqc_file_rec option usedthy commutatives forbFuns iter  sourceThms insts sz qciter [] = 
   raise WrongArg ("Not enough files for the output of qc_test_file_rec!")
 | mutqc_file_rec option usedthy commutatives forbFuns iter (x::xs) insts sz qciter (y::ys) = 
   (mutqc_file option usedthy commutatives forbFuns iter x insts sz qciter y ; 
   mutqc_file_rec option usedthy commutatives forbFuns iter xs insts sz qciter ys);


(*exchange version of function mutqc_file_rec*)

fun mutqc_file_rec_exc usedthy commutatives iter sourceThms insts sz qciter files =
 mutqc_file_rec 0 usedthy commutatives [] iter sourceThms insts sz qciter files;

(*signature version of function mutqc_file_rec*)

fun mutqc_file_rec_sign usedthy forbidden_funs iter sourceThms insts sz qciter files =
 mutqc_file_rec 1 usedthy [] forbidden_funs iter sourceThms insts sz qciter files;

(*mixed version of function mutqc_file_rec*)

fun mutqc_file_rec_mix usedthy commutatives forbidden_funs iter sourceThms insts sz qciter files =
 mutqc_file_rec 2 usedthy commutatives forbidden_funs iter sourceThms insts sz qciter files;

(*create the appropriate number of spaces in order to properly print a table*)

fun create_spaces entry spacenum =
 let 
   val diff = spacenum - (size entry)
 in
   if (diff > 0)
   then implode (replicate diff " ")
   else ""
 end;


(*create a statistic of the output of a quickcheck test on the passed thmlist*)

fun mutqc_file_stat option usedthy commutatives forbidden_funs iter thmlist insts sz qciter filename = 
 let 
   fun mutthmrec [] = ()
   |   mutthmrec (x::xs) =
     let 
       val mutated = mutate option (prop_of x) usedthy
         commutatives forbidden_funs iter
       val (passednum,_,cenum,_) = qc_test mutated insts usedthy sz qciter
       val thmname =  "\ntheorem " ^ Thm.get_name_hint x ^ ":"
       val pnumstring = string_of_int passednum
       val cenumstring = string_of_int cenum
     in
       (File.append (Path.explode filename) 
         (thmname ^ (create_spaces thmname 50) ^ 
         pnumstring ^ (create_spaces pnumstring 20) ^ 
         cenumstring ^ (create_spaces cenumstring 20) ^ "\n");
       mutthmrec xs)
     end;
 in 
   (File.write (Path.explode filename) 
     ("\n\ntheorem name" ^ (create_spaces "theorem name" 50) ^ 
     "passed mutants"  ^ (create_spaces "passed mutants" 20) ^ 
     "counter examples\n\n" );
   mutthmrec thmlist)
 end;

(*signature version of function mutqc_file_stat*)

fun mutqc_file_stat_sign usedthy forbidden_funs iter thmlist insts sz qciter filename =
 mutqc_file_stat 1 usedthy [] forbidden_funs iter thmlist insts sz qciter filename;

(*exchange version of function mutqc_file_stat*)

fun mutqc_file_stat_exc usedthy commutatives iter thmlist insts sz qciter filename =
 mutqc_file_stat 0 usedthy commutatives [] iter thmlist insts sz qciter filename;

(*mixed version of function mutqc_file_stat*)

fun mutqc_file_stat_mix usedthy commutatives forbidden_funs iter thmlist insts sz qciter filename =
 mutqc_file_stat 2 usedthy commutatives forbidden_funs iter thmlist insts sz qciter filename;

(*mutate and quickcheck-test all the theorems contained in the passed theory. 
The output will be stored in a single file*)

fun mutqc_thy option mutthy usedthy commutatives forbidden_funs iter insts sz qciter filename =
 let
   val thmlist = filter (is_executable mutthy insts o snd) (thms_of mutthy);
   fun mutthmrec [] = ()
     | mutthmrec ((name,thm)::xs) = 
         let
           val mutated = mutate option (prop_of thm) 
             usedthy commutatives forbidden_funs iter
         in
           (File.append (Path.explode filename) 
             ("--------------------------\n\nQuickchecktest of theorem " ^ name ^ ":\n\n");
           qc_test_file true mutated insts usedthy sz qciter filename;
           mutthmrec xs)
         end;
   in 
     mutthmrec thmlist
   end;

(*exchange version of function mutqc_thy*)

fun mutqc_thy_exc mutthy usedthy commutatives iter insts sz qciter filename =
 mutqc_thy 0 mutthy usedthy commutatives [] iter insts sz qciter filename;

(*signature version of function mutqc_thy*)

fun mutqc_thy_sign mutthy usedthy forbidden_funs iter insts sz qciter filename =
 mutqc_thy 1 mutthy usedthy [] forbidden_funs iter insts sz qciter filename;

(*mixed version of function mutqc_thy*)

fun mutqc_thy_mix mutthy usedthy commutatives forbidden_funs iter insts sz qciter filename =
 mutqc_thy 2 mutthy usedthy commutatives forbidden_funs iter insts sz qciter filename;

(*create a statistic representation of the call of function mutqc_thy*)

fun mutqc_thystat option p mutthy usedthy commutatives forbidden_funs iter insts sz qciter filename =
 let
   val thmlist = filter
     (fn (s, th) => not (p s th) andalso (Output.urgent_message s; is_executable mutthy insts th)) (thms_of mutthy)
   fun mutthmrec [] = ()
   |   mutthmrec ((name,thm)::xs) =
     let          
       val _ = Output.urgent_message ("mutthmrec: " ^ name);
       val mutated = mutate option (prop_of thm) usedthy
           commutatives forbidden_funs iter
       val (passednum,_,cenum,_) = qc_test mutated insts usedthy sz qciter
       val thmname =  "\ntheorem " ^ name ^ ":"
       val pnumstring = string_of_int passednum
       val cenumstring = string_of_int cenum
     in
       (File.append (Path.explode filename) 
         (thmname ^ (create_spaces thmname 50) ^ 
         pnumstring ^ (create_spaces pnumstring 20) ^ 
         cenumstring ^ (create_spaces cenumstring 20) ^ "\n");
       mutthmrec xs)
     end;
 in 
   (File.write (Path.explode filename) ("Result of the quickcheck-test of theory " ^
     ":\n\ntheorem name" ^ (create_spaces "theorem name" 50) ^ 
     "passed mutants"  ^ (create_spaces "passed mutants" 20) ^ 
     "counter examples\n\n" );
   mutthmrec thmlist)
 end;

(*exchange version of function mutqc_thystat*)

fun mutqc_thystat_exc p mutthy usedthy commutatives iter insts sz qciter filename =
 mutqc_thystat 0 p mutthy usedthy commutatives [] iter insts sz qciter filename;

(*signature version of function mutqc_thystat*)

fun mutqc_thystat_sign p mutthy usedthy forbidden_funs iter insts sz qciter filename =
 mutqc_thystat 1 p mutthy usedthy [] forbidden_funs iter insts sz qciter filename;

(*mixed version of function mutqc_thystat*)

fun mutqc_thystat_mix p mutthy usedthy commutatives forbidden_funs iter insts sz qciter filename =
 mutqc_thystat 2 p mutthy usedthy commutatives forbidden_funs iter insts sz qciter filename;
*)

end

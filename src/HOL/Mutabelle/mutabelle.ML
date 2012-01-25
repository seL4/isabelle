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
           member (op =) commutatives name
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
      ("exhaustive", ((fn _ => raise (Fail "")), Exhaustive_Generators.compile_generator_expr)) ctxt' false
  in  
    case try test (preprocess thy insts (prop_of th), []) of
      SOME _ => (Output.urgent_message "executable"; true)
    | NONE => (Output.urgent_message ("not executable"); false)
  end;                                               

end

(*  ID:         $Id$
    Author:     Claire Quigley
    Copyright   2004  University of Cambridge
*)

(* Parsing functions *)

(* Auxiliary functions *)

structure Recon_Parse =
struct

open ReconPrelim ReconTranslateProof;

exception NOPARSE_WORD
exception NOPARSE_NUM
fun to_upper s = String.translate (Char.toString o Char.toUpper) s;

fun string2int s =
  (case Int.fromString s of SOME i => i
  | NONE => raise ASSERTION "string -> int failed");


(* Parser combinators *)

exception Noparse;

fun (parser1 ++ parser2) input =
      let
        val (result1, rest1) = parser1 input
        val (result2, rest2) = parser2 rest1
      in
        ((result1, result2), rest2)
      end;

fun many parser input =
      let   (* Tree * token list*)
        val (result, next) = parser input
        val (results, rest) = many parser next
      in
        ((result::results), rest)
      end
      handle Noparse => ([], input)
|            NOPARSE_WORD => ([], input)
|            NOPARSE_NUM  => ([], input);



fun (parser >> treatment) input =
      let
        val (result, rest) = parser input
      in
        (treatment result, rest)
      end;

fun (parser1 || parser2) input = parser1 input
handle Noparse => parser2 input;

infixr 8 ++; infixr 7 >>; infixr 6 ||;

fun some p [] = raise Noparse
  | some p (h::t) = if p h then (h, t) else raise Noparse;

fun a tok = some (fn item => item = tok);

fun finished input = if input = [] then (0, input) else raise Noparse;





  (* Parsing the output from gandalf *)
datatype token = Word of string
               | Number of int
               | Other of string


      exception NOCUT
      fun is_prefix [] l = true
        | is_prefix (h::t) [] = false
        | is_prefix (h::t) (h'::t') = (h = h') andalso is_prefix t t'
      fun remove_prefix [] l = l
        | remove_prefix (h::t) [] = raise (ASSERTION "can't remove prefix")
        | remove_prefix (h::t) (h'::t') = remove_prefix t t'
      fun ccut t [] = raise NOCUT
        | ccut t s =
            if is_prefix t s then ([], remove_prefix t s) else
              let val (a, b) = ccut t (tl s) in ((hd s)::a, b) end
      fun cut t s =
        let
          val t' = explode t
          val s' = explode s
          val (a, b) = ccut t' s'
        in
          (implode a, implode b)
        end
    
      fun cut_exists t s
          = let val (a, b) = cut t s in true end handle NOCUT => false

      fun cut_before t s = let val (a, b) = cut t s in (a, t ^ b) end
      fun cut_after t s = let val (a, b) = cut t s in (a ^ t, b) end
    

    fun kill_lines 0 = Library.I
      | kill_lines n = kill_lines (n - 1) o snd o cut_after "\n";

    (*fun extract_proof s
      = if cut_exists "EMPTY CLAUSE DERIVED" s then
          (kill_lines 6
           o snd o cut_after "EMPTY CLAUSE DERIVED"
           o fst o cut_after "contradiction.\n") s
        else
          raise (GandalfError "Couldn't find a proof.")
*)

val start_E = "# Proof object starts here."
val end_E   = "# Proof object ends here."
val start_V6 = "%================== Proof: ======================"
val end_V6   = "%==============  End of proof. =================="
val start_V8 = "=========== Refutation =========="
val end_V8 = "======= End of refutation ======="


(*Identifies the start/end lines of an ATP's output*)
fun extract_proof s =
  if cut_exists "Here is a proof with" s then
    (kill_lines 0
     o snd o cut_after ":"
     o snd o cut_after "Here is a proof with"
     o fst o cut_after " ||  -> .") s
  else if cut_exists start_V8 s then
    (kill_lines 0    (*Vampire 8.0*)
     o snd o cut_after start_V8
     o fst o cut_before end_V8) s
  else if cut_exists end_E s then
    (kill_lines 0    (*eproof*)
     o snd o cut_after start_E
     o fst o cut_before end_E) s
  else "??extract_proof failed" (*Couldn't find a proof*)

fun several p = many (some p)
      fun collect (h, t) = h ^ (fold_rev (fn s1 => fn s2 => s1 ^ s2) t "")
  
      fun lower_letter s = ("a" <= s) andalso (s <= "z")
      fun upper_letter s = ("A" <= s) andalso (s <= "Z")
      fun digit s = ("0" <= s) andalso (s <= "9")
      fun letter s = lower_letter s orelse upper_letter s
      fun alpha s = letter s orelse (s = "_")
      fun alphanum s = alpha s orelse digit s
      fun space s = (s = " ") orelse (s = "\n") orelse (s = "\t")
      (* FIX this is stopping it picking up numbers *)
      val word = (some alpha ++ several alphanum) >> (Word o collect)
      val number =
            (some digit ++ several digit) >> (Number o string2int o collect)
      val other = some (K true) >> Other
      
      val token = (word || number || other) ++ several space >> fst
      val tokens = (several space ++ many token) >> snd
      val alltokens = (tokens ++ finished) >> fst
    
     (* val lex = fst ( alltokens ( (map str)  explode))*)
     fun lex s =  alltokens  (explode s)



(*String contains multiple lines, terminated with newline characters.
  A list consisting of the first number in each line is returned. *)
fun get_linenums proofstr = 
  let val numerics = String.tokens (not o Char.isDigit)
      fun firstno [] = NONE
        | firstno (x::xs) = Int.fromString x
      val lines = String.tokens (fn c => c = #"\n") proofstr
  in  List.mapPartial (firstno o numerics) lines  end


(************************************************************)

(**************************************************)
(* Code to parse SPASS proofs                     *)
(**************************************************)

datatype Tree = Leaf of string
                | Branch of Tree * Tree

   
      fun number ((Number n)::rest) = (n, rest)
        | number _ = raise NOPARSE_NUM
      fun word ((Word w)::rest) = (w, rest)
        | word _ = raise NOPARSE_WORD

      fun other_char ( (Other p)::rest) = (p, rest)
      | other_char _ =raise NOPARSE_WORD
     
      val number_list =
        (number ++ many number)
        >> (fn (a, b) => (a::b))
     
      val term_num =
        (number ++ (a (Other ".")) ++ number) >> (fn (a, (_, c)) => (a, c))


      val term_num_list = (term_num ++ many (a (Other ",") ++ term_num >> snd)
			   >> (fn (a, b) => (a::b)))

      val axiom = (a (Word "Inp"))
            >> (fn (_) => Axiom)
      
      
      val binary = (a (Word "Res")) ++ (a (Other ":"))
                   ++ term_num ++ (a (Other ","))
                   ++ term_num
            >> (fn (_, (_, (c, (_, e)))) => Binary (c, e))
      


      val factor = (a (Word "Fac")) ++ (a (Other ":")) 
                    ++ term_num ++ (a (Other ",")) 
                    ++ term_num
            >> (fn (_, (_, (c, (_, e)))) =>  Factor ((fst c), (snd c),(snd e)))
     
      val para  = (a (Word "SPm")) ++ (a (Other ":"))
                   ++ term_num ++ (a (Other ","))
                   ++ term_num
            >> (fn (_, (_, (c, (_, e)))) => Para (c, e))
      
      val super_l  = (a (Word "SpL")) ++ (a (Other ":"))
                   ++ term_num ++ (a (Other ","))
                   ++ term_num
            >> (fn (_, (_, (c, (_, e)))) => Super_l (c, e))


      val super_r  = (a (Word "SpR")) ++ (a (Other ":"))
                   ++ term_num ++ (a (Other ","))
                   ++ term_num
            >> (fn (_, (_, (c, (_, e)))) => Super_r (c, e))


      val aed = (a (Word "AED")) ++ (a (Other ":")) ++ term_num
                 >> (fn (_, (_, c)) => Obvious ((fst c),(snd c)))

      val rewrite = (a (Word "Rew")) ++ (a (Other ":")) 
                    ++ term_num_list
            >> (fn (_, (_, (c))) =>  Rewrite (c))


      val mrr = (a (Word "MRR")) ++ (a (Other ":"))
                   ++ term_num ++ (a (Other ","))
                   ++ term_num
            >> (fn (_, (_, (c, (_, e)))) => MRR (c, e))

      val ssi = (a (Word "SSi")) ++ (a (Other ":"))
                   ++ term_num ++ (a (Other ","))
                   ++ term_num
            >> (fn (_, (_, (c, (_, e)))) => SortSimp (c, e))

    val unc = (a (Word "UnC")) ++ (a (Other ":"))
                   ++ term_num ++ (a (Other ","))
                   ++ term_num
            >> (fn (_, (_, (c, (_, e)))) => UnitConf (c, e))



      val obv = (a (Word "Obv")) ++ (a (Other ":")) ++ term_num
                 >> (fn (_, (_, c)) => Obvious ((fst c),(snd c)))

      val eqres = (a (Word "EqR")) ++ (a (Other ":")) ++ term_num
                 >> (fn (_, (_, c)) => EqualRes ((fst c),(snd c)))
   
      val con = (a (Word "Con")) ++ (a (Other ":")) ++ term_num
                 >> (fn (_, (_, c)) => Condense ((fst c),(snd c)))

(*
      val hyper = a (Word "hyper")
                  ++ many ((a (Other ",") ++ number) >> snd)
                  >> (Hyper o snd)
*)
     (* val method = axiom ||binary || factor || para || hyper*)

      val method = axiom || binary || factor || para ||super_l || super_r || rewrite || mrr || obv || aed || ssi || unc|| con

      val binary_s = a (Word "binary_s") ++ a (Other ",") ++ term_num
            >> (fn (_, (_, a)) => Binary_s a)
      val factor_s = a (Word "factor_s")
            >> (fn _ => Factor_s ())
      val demod_s = a (Word "demod")
                    ++ (many ((a (Other ",") ++ term_num) >> snd))
            >> (fn (_, a) => Demod_s a)

      val hyper_s = a (Word "hyper_s")
                    ++ many ((a (Other ",") ++ number) >> snd)
                    >> (Hyper_s o snd)
      val simp_method = binary_s || factor_s || demod_s || hyper_s
      val simp = a (Other ",") ++ simp_method >> snd
      val simps = many simp
 

      val justification =
           a (Other "[") ++number ++ a (Other ":") ++ method ++ a (Other "]")
                 >> (fn (_,(_, (_,(b, _)))) => b)

     
exception NOTERM

(* FIX - should change the stars and pluses to many rather than explicit patterns *)

fun trim_prefix a b =
  let val n = String.size a 
  in  String.substring (b, n, (size b) - n)  end;
  

(* FIX - add the other things later *)
fun remove_typeinfo x  =  
    if String.isPrefix ResClause.fixed_var_prefix x
    then trim_prefix ResClause.fixed_var_prefix x
    else if String.isPrefix ResClause.schematic_var_prefix x
    then trim_prefix ResClause.schematic_var_prefix x
    else if String.isPrefix ResClause.const_prefix x
    then trim_prefix ResClause.const_prefix x
    else if String.isPrefix ResClause.tfree_prefix x
    then ""
    else if String.isPrefix ResClause.tvar_prefix x
    then ""
    else if String.isPrefix ResClause.tconst_prefix x
    then ""
    else x;                                               

fun term input = (  ntermlist ++ a (Other "-") ++ a (Other ">") ++ ptermlist >>(fn (a,(_,(_,b))) =>  (a@b))
                  ) input

(* pterms are terms from the rhs of the -> in the spass proof.  *)
(* they should have a "~" in front of them so that they match with *)
(* positive terms in the meta-clause *)
(* nterm are terms from the lhs of the spass proof, and shouldn't *)
(* "~"s added  word ++ a (Other "(") ++ arglist ++ a (Other ")") >> (fn (a,(_,(b,_ ))) =>  (a^" "^b)) *)

and  pterm input = (
           peqterm >> (fn (a) => a)
        
         || word ++ a (Other "(") ++ arglist ++  a (Other ")") ++ a (Other "*")++ a (Other "*") ++ a (Other "+")
           >> (fn (a, (_,(b, (_,(_,_))))) =>  ("~"^" "^(remove_typeinfo a)^" "^b))
         
        || word ++ a (Other "(") ++ arglist ++  a (Other ")") ++ a (Other "*") ++ a (Other "+")
           >> (fn ( a, (_,(b, (_,(_,_))))) =>  ("~"^" "^(remove_typeinfo a)^" "^b))
        
        || word ++ a (Other "(") ++ arglist ++ a (Other ")") ++ a (Other "*") ++ a (Other "*")
           >> (fn ( a, (_,(b, (_,(_,_))))) =>  ("~"^" "^(remove_typeinfo a)^" "^b))
        
	|| word ++ a (Other "(") ++ arglist ++ a (Other ")") ++ a (Other "*")
           >> (fn (a, (_,(b, (_,_)))) =>  ("~"^" "^(remove_typeinfo a)^" "^b))

        || word ++ a (Other "(") ++  arglist ++ a (Other ")") 
           >> (fn ( a, (_,(b,_ ))) => ("~"^" "^(remove_typeinfo a)^" "^b))

        || word ++ a (Other "*") >> (fn (w,b) => "~"^" "^(remove_typeinfo w))

        || word                  >> (fn w => "~"^" "^(remove_typeinfo w))) input

and  nterm input =
    
       (  
           neqterm >> (fn (a) => a)

        || word ++ a (Other "(") ++ arglist ++ a (Other ")") ++ a (Other "*") ++ a (Other "*") ++ a (Other "+")
           >> (fn ( a, (_,(b, (_,(_,_))))) =>  ((remove_typeinfo a)^" "^b))

        || word ++ a (Other "(") ++ arglist ++ a (Other ")") ++ a (Other "*") ++ a (Other "+")
           >> (fn ( a, (_,(b, (_,(_,_))))) =>  ((remove_typeinfo a)^" "^b))
        
        || word ++ a (Other "(") ++ arglist ++ a (Other ")") ++ a (Other "*") ++ a (Other "*")
           >> (fn ( a, (_,(b, (_,(_,_))))) =>  ((remove_typeinfo a)^" "^b))
        
	|| word ++ a (Other "(") ++ arglist ++ a (Other ")") ++ a (Other "*")
           >> (fn ( a, (_,(b, (_,_)))) =>  ((remove_typeinfo a)^" "^b))

        || word ++ a (Other "(") ++ arglist ++ a (Other ")") 
           >> (fn (a, (_,(b,_ ))) => ((remove_typeinfo a)^" "^b))

        || word ++ a (Other "*") >> (fn (w,b) =>  (remove_typeinfo w)) 
        || word                  >> (fn w =>  (remove_typeinfo w)) 
         ) input 


and peqterm input =(
 
         a (Word "equal") ++  a (Other "(") ++ nterm ++ a (Other ",") ++ nterm ++ a (Other ")") 
         ++ a (Other "*") ++ a (Other "*") ++ a (Other "+")
            >> (fn (_,(_,(a,(_,(b,(_,(_,(_,_)))))))) => (a^" ~= "^b))

      || a (Word "equal") ++  a (Other "(") ++ nterm ++ a (Other ",") ++ nterm ++ a (Other ")") 
          ++ a (Other "*") ++ a (Other "+")
            >> (fn (_,(_,(a,(_,(b,(_,(_,_))))))) => (a^" ~= "^b))

      || a (Word "equal") ++  a (Other "(") ++ nterm ++ a (Other ",") ++ nterm ++ a (Other ")") 
         ++ a (Other "*") ++ a (Other "*")
            >> (fn (_,(_,(a,(_,(b,(_,(_,_))))))) => (a^" ~= "^b))

      || a (Word "equal") ++  a (Other "(") ++ nterm ++ a (Other ",") ++ nterm ++ a (Other ")") 
         ++ a (Other "*") 
            >> (fn (_,(_,(a,(_,(b,(_,_)))))) => (a^" ~= "^b))


       ||a (Word "equal") ++  a (Other "(") ++ nterm ++ a (Other ",") ++ nterm ++ a (Other ")") 
            >> (fn (_,(_,(a,(_,(b,_))))) => (a^" ~= "^b))) input



and neqterm input =(
 
         a (Word "equal") ++  a (Other "(") ++ nterm ++ a (Other ",") ++ nterm ++ a (Other ")") 
         ++ a (Other "*") ++ a (Other "*") ++ a (Other "+")
            >> (fn (_,(_,(a,(_,(b,(_,(_,(_,_)))))))) => (a^" = "^b))

      || a (Word "equal") ++  a (Other "(") ++ nterm ++ a (Other ",") ++ nterm ++ a (Other ")") 
          ++ a (Other "*") ++ a (Other "+")
            >> (fn (_,(_,(a,(_,(b,(_,(_,_))))))) => (a^" = "^b))

      || a (Word "equal") ++  a (Other "(") ++ nterm ++ a (Other ",") ++ nterm ++ a (Other ")") 
         ++ a (Other "*") ++ a (Other "*")
            >> (fn (_,(_,(a,(_,(b,(_,(_,_))))))) => (a^" = "^b))

      || a (Word "equal") ++  a (Other "(") ++ nterm ++ a (Other ",") ++ nterm ++ a (Other ")") 
         ++ a (Other "*") 
            >> (fn (_,(_,(a,(_,(b,(_,_)))))) => (a^" = "^b))


       ||a (Word "equal") ++  a (Other "(") ++ nterm ++ a (Other ",") ++ nterm ++ a (Other ")") 
            >> (fn (_,(_,(a,(_,(b,_))))) => (a^" = "^b))) input



and ptermlist input = (many  pterm
                      >> (fn (a) => (a))) input

and ntermlist input = (many  nterm
                      >> (fn (a) => (a))) input

(*and arglist input = (    nterm >> (fn (a) => (a))
                     ||  nterm ++ many (a (Other ",") ++ nterm >> snd)
                      >> (fn (a, b) => (a^" "^(space_implode " " b)))) input*)

and arglist input = (   nterm ++ many (a (Other ",") ++ nterm >> snd)
                      >> (fn (a, b) => (a^" "^(space_implode " " b))) 
                      ||    nterm >> (fn (a) => (a)))input

 val clause =  term

(* not entirely sure nterm is right here, but I don't think you get negative things before the ||s *)
 val line = number ++ justification ++ many( nterm) ++ a (Other "|") ++ 
            a (Other "|") ++ clause ++ a (Other ".")
          >> (fn (a, (z, (w, (_,( _, (c, _)))))) => (a, z,(w@ c)))
       
 val lines = many line
 val alllines = (lines ++ finished) >> fst
    
 val parse = fst o alllines

end;

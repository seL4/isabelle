(*  ID:         $Id$
    Author:     Claire Quigley
    Copyright   2004  University of Cambridge
*)

(*use "Translate_Proof";*)
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
exception SPASSError of string;
exception VampError of string;


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

val proofstring =
"0:00:00.00 for the reduction.\
\\
\Here is a proof with depth 3, length 7 :\
\1[0:Inp] ||  -> P(xa)*.\
\2[0:Inp] ||  -> Q(xb)*.\
\3[0:Inp] || R(U)* -> .\
\4[0:Inp] || Q(U) P(V) -> R(x(V,U))*.\
\9[0:Res:4.2,3.0] || Q(U)*+ P(V)* -> .\
\11[0:Res:2.0,9.0] || P(U)* -> .\
\12[0:Res:1.0,11.0] ||  -> .\
\Formulae used in the proof :\
\\
\--------------------------SPASS-STOP------------------------------"

fun extract_proof s
      = if cut_exists "Here is a proof with" s then
          (kill_lines 0
           o snd o cut_after ":"
           o snd o cut_after "Here is a proof with"
           o fst o cut_after " ||  -> .") s
        else if cut_exists "%================== Proof: ======================" s then
          (kill_lines 0
           o snd o cut_after "%================== Proof: ======================"
           o fst o cut_before "==============  End of proof. ==================") s
        else
          raise SPASSError "Couldn't find a proof."

(*fun extract_proof s
      = if cut_exists "Here is a proof with" s then
          (kill_lines 0
           o snd o cut_after ":"
           o snd o cut_after "Here is a proof with"
           o fst o cut_after " ||  -> .") s
        else
          raise SPASSError "Couldn't find a proof."
*)





fun several p = many (some p)
      fun collect (h, t) = h ^ (Utils.itlist (fn s1 => fn s2 => s1 ^ s2) t "")
  
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


(*********************************************************)
(*  Temporary code to "parse" Vampire proofs             *)
(*********************************************************)

fun num_int (Number n) = n
|   num_int _ = raise VampError "Not a number"

 fun takeUntil ch [] res  = (res, [])
 |   takeUntil ch (x::xs) res = if   x = ch 
                                then
                                     (res, xs)
                                else
                                     takeUntil ch xs (res@[x])
       
fun linenums [] nums = nums
|   linenums (x::xs) nums = let val (fst, rest ) = takeUntil (Other "%") (x::xs) []
                                in 
				  if rest = [] 
				  then 
				      nums
				  else
			          let val first = hd rest
				
			          in
				    if (first = (Other "*") ) 
				    then 
					
					 linenums rest ((num_int (hd (tl rest)))::nums)
				     else
					  linenums rest ((num_int first)::nums)
			         end
                                end


(* This relies on a Vampire proof line starting "% Number" or "% * Number"*)
(* Check this is right *)

fun get_linenums proofstr = let (*val s = extract_proof proofstr*)
                                val tokens = #1(lex proofstr)
	                 
	                    in
		                rev (linenums tokens [])
		            end

(************************************************************)
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


fun implode_with_space [] = implode []
|   implode_with_space [x] = implode [x]
|   implode_with_space (x::[y]) = x^" "^y
|   implode_with_space (x::xs) =  (x^" "^(implode_with_space xs))

(* FIX - should change the stars and pluses to many rather than explicit patterns *)

(* FIX - add the other things later *)
fun remove_typeinfo x  =  if (String.isPrefix "v_" x )
                            then 
                                 (String.substring (x,2, ((size x) - 2)))
                            else if (String.isPrefix "V_" x )
                                 then 
                                      (String.substring (x,2, ((size x) - 2)))
                                 else if (String.isPrefix "typ_" x )
                                      then 
                                          ""
                                      else if (String.isPrefix "Typ_" x )
                                           then 
                                                ""
                                           else  if (String.isPrefix "tconst_" x )
                                                 then 
                                                      ""
                                                 else  if (String.isPrefix "const_" x )
                                                       then 
                                                            (String.substring  (x,6, ((size x) - 6)))
                                                       else
                                                           x
                                               

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
                      >> (fn (a, b) => (a^" "^(implode_with_space b)))) input*)

and arglist input = (   nterm ++ many (a (Other ",") ++ nterm >> snd)
                      >> (fn (a, b) => (a^" "^(implode_with_space b))) 
                      ||    nterm >> (fn (a) => (a)))input

 val clause =  term



 (*val line = number ++ justification ++ a (Other "|") ++ 
            a (Other "|") ++ clause ++ a (Other ".")
          >> (fn (a, (z, (_,( _, (c, _))))) => (a, z, c))*)


(* not entirely sure nterm is right here, but I don't think you get negative things before the ||s *)
 val line = number ++ justification ++ many( nterm) ++ a (Other "|") ++ 
            a (Other "|") ++ clause ++ a (Other ".")
          >> (fn (a, (z, (w, (_,( _, (c, _)))))) => (a, z,(w@ c)))
       


 val lines = many line
 val alllines = (lines ++ finished) >> fst
    
 val parse = fst o alllines
 val s = proofstring;
 
 


fun dropUntilNot ch []   = ( [])
 |   dropUntilNot ch (x::xs)  = if  not(x = ch )
                                then
                                     (x::xs)
                                else
                                     dropUntilNot ch xs


fun remove_spaces str  []  = str
|   remove_spaces str (x::[]) = if x = " " 
                                then 
                                    str 
                                else 
                                    (str^x)
|   remove_spaces str (x::xs) = 
      let val (first, rest) = ReconOrderClauses.takeUntil " " (x::xs) []
	  val (next) = dropUntilNot " " rest 
      in 
	  if next = []
	  then 
	       (str^(implode first)) 
	  else remove_spaces  (str^(implode first)^" ") next 
      end


fun remove_space_strs clsstrs = map (remove_spaces "") (map explode clsstrs)


fun all_spaces xs = List.filter  (not_equal " " ) xs

fun just_change_space []  = []
|   just_change_space ((clausenum, step, strs)::xs) =
      let val newstrs = remove_space_strs strs
      in
	 if (all_spaces newstrs = [] ) (* all type_info *)
	 then    
	    (clausenum, step, newstrs)::(just_change_space xs)
	 else 
	     (clausenum, step, newstrs)::(just_change_space xs) 
      end;

fun change_space []  = []
|   change_space ((clausenum, step, strs)::xs) = 
      let val newstrs = remove_space_strs strs
      in
	 if (all_spaces newstrs = [] ) (* all type_info *)
	 then    
	    (clausenum, step, T_info, newstrs)::(change_space xs)
	 else 
	     (clausenum, step, P_info, newstrs)::(change_space xs) 
      end

end;

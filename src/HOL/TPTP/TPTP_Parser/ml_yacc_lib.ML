
(******************************************************************)
(* GENERATED FILE -- DO NOT EDIT -- GENERATED FILE -- DO NOT EDIT *)
(* GENERATED FILE -- DO NOT EDIT -- GENERATED FILE -- DO NOT EDIT *)
(* GENERATED FILE -- DO NOT EDIT -- GENERATED FILE -- DO NOT EDIT *)
(******************************************************************)

print_depth 0;

(*
  This file is generated from the contents of ML-Yacc's lib directory.
  ML-Yacc's COPYRIGHT-file contents follow:

  ML-YACC COPYRIGHT NOTICE, LICENSE AND DISCLAIMER.
  
  Copyright 1989, 1990 by David R. Tarditi Jr. and Andrew W. Appel
  
  Permission to use, copy, modify, and distribute this software and its
  documentation for any purpose and without fee is hereby granted,
  provided that the above copyright notice appear in all copies and that
  both the copyright notice and this permission notice and warranty
  disclaimer appear in supporting documentation, and that the names of
  David R. Tarditi Jr. and Andrew W. Appel not be used in advertising
  or publicity pertaining to distribution of the software without
  specific, written prior permission.
  
  David R. Tarditi Jr. and Andrew W. Appel disclaim all warranties with regard to
  this software, including all implied warranties of merchantability and fitness.
  In no event shall David R. Tarditi Jr. and Andrew W. Appel be liable for any
  special, indirect or consequential damages or any damages whatsoever resulting
  from loss of use, data or profits, whether in an action of contract, negligence
  or other tortious action, arising out of or in connection with the use or
  performance of this software.
*)

(**** Original file: base.sig ****)

(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi *)

(* base.sig: Base signature file for SML-Yacc.  This file contains signatures
   that must be loaded before any of the files produced by ML-Yacc are loaded
*)

(* STREAM: signature for a lazy stream.*)

signature STREAM =
 sig type 'xa stream
     val streamify : (unit -> '_a) -> '_a stream
     val cons : '_a * '_a stream -> '_a stream
     val get : '_a stream -> '_a * '_a stream
 end

(* LR_TABLE: signature for an LR Table.

   The list of actions and gotos passed to mkLrTable must be ordered by state
   number. The values for state 0 are the first in the list, the values for
    state 1 are next, etc.
*)

signature LR_TABLE =
    sig
        datatype ('a,'b) pairlist = EMPTY | PAIR of 'a * 'b * ('a,'b) pairlist
	datatype state = STATE of int
	datatype term = T of int
	datatype nonterm = NT of int
	datatype action = SHIFT of state
			| REDUCE of int
			| ACCEPT
			| ERROR
	type table
	
	val numStates : table -> int
	val numRules : table -> int
	val describeActions : table -> state ->
				(term,action) pairlist * action
	val describeGoto : table -> state -> (nonterm,state) pairlist
	val action : table -> state * term -> action
	val goto : table -> state * nonterm -> state
	val initialState : table -> state
	exception Goto of state * nonterm

	val mkLrTable : {actions : ((term,action) pairlist * action) array,
			 gotos : (nonterm,state) pairlist array,
			 numStates : int, numRules : int,
			 initialState : state} -> table
    end

(* TOKEN: signature revealing the internal structure of a token. This signature
   TOKEN distinct from the signature {parser name}_TOKENS produced by ML-Yacc.
   The {parser name}_TOKENS structures contain some types and functions to
    construct tokens from values and positions.

   The representation of token was very carefully chosen here to allow the
   polymorphic parser to work without knowing the types of semantic values
   or line numbers.

   This has had an impact on the TOKENS structure produced by SML-Yacc, which
   is a structure parameter to lexer functors.  We would like to have some
   type 'a token which functions to construct tokens would create.  A
   constructor function for a integer token might be

	  INT: int * 'a * 'a -> 'a token.
 
   This is not possible because we need to have tokens with the representation
   given below for the polymorphic parser.

   Thus our constructur functions for tokens have the form:

	  INT: int * 'a * 'a -> (svalue,'a) token

   This in turn has had an impact on the signature that lexers for SML-Yacc
   must match and the types that a user must declare in the user declarations
   section of lexers.
*)

signature TOKEN =
    sig
	structure LrTable : LR_TABLE
        datatype ('a,'b) token = TOKEN of LrTable.term * ('a * 'b * 'b)
	val sameToken : ('a,'b) token * ('a,'b) token -> bool
    end

(* LR_PARSER: signature for a polymorphic LR parser *)

signature LR_PARSER =
    sig
	structure Stream: STREAM
	structure LrTable : LR_TABLE
	structure Token : TOKEN

	sharing LrTable = Token.LrTable

	exception ParseError

	val parse : {table : LrTable.table,
		     lexer : ('_b,'_c) Token.token Stream.stream,
		     arg: 'arg,
		     saction : int *
			       '_c *
				(LrTable.state * ('_b * '_c * '_c)) list * 
				'arg ->
				     LrTable.nonterm *
				     ('_b * '_c * '_c) *
				     ((LrTable.state *('_b * '_c * '_c)) list),
		     void : '_b,
		     ec : { is_keyword : LrTable.term -> bool,
			    noShift : LrTable.term -> bool,
			    preferred_change : (LrTable.term list * LrTable.term list) list,
			    errtermvalue : LrTable.term -> '_b,
			    showTerminal : LrTable.term -> string,
			    terms: LrTable.term list,
			    error : string * '_c * '_c -> unit
			   },
		     lookahead : int  (* max amount of lookahead used in *)
				      (* error correction *)
			} -> '_b *
			     (('_b,'_c) Token.token Stream.stream)
    end

(* LEXER: a signature that most lexers produced for use with SML-Yacc's
   output will match.  The user is responsible for declaring type token,
   type pos, and type svalue in the UserDeclarations section of a lexer.

   Note that type token is abstract in the lexer.  This allows SML-Yacc to
   create a TOKENS signature for use with lexers produced by ML-Lex that
   treats the type token abstractly.  Lexers that are functors parametrized by
   a Tokens structure matching a TOKENS signature cannot examine the structure
   of tokens.
*)

signature LEXER =
   sig
       structure UserDeclarations :
	   sig
	        type ('a,'b) token
		type pos
		type svalue
	   end
	val makeLexer : (int -> string) -> unit -> 
         (UserDeclarations.svalue,UserDeclarations.pos) UserDeclarations.token
   end

(* ARG_LEXER: the %arg option of ML-Lex allows users to produce lexers which
   also take an argument before yielding a function from unit to a token
*)

signature ARG_LEXER =
   sig
       structure UserDeclarations :
	   sig
	        type ('a,'b) token
		type pos
		type svalue
		type arg
	   end
	val makeLexer : (int -> string) -> UserDeclarations.arg -> unit -> 
         (UserDeclarations.svalue,UserDeclarations.pos) UserDeclarations.token
   end

(* PARSER_DATA: the signature of ParserData structures in {parser name}LrValsFun
   produced by  SML-Yacc.  All such structures match this signature.  

   The {parser name}LrValsFun produces a structure which contains all the values
   except for the lexer needed to call the polymorphic parser mentioned
   before.

*)

signature PARSER_DATA =
   sig
        (* the type of line numbers *)

	type pos

	(* the type of semantic values *)

	type svalue

         (* the type of the user-supplied argument to the parser *)
 	type arg
 
	(* the intended type of the result of the parser.  This value is
	   produced by applying extract from the structure Actions to the
	   final semantic value resultiing from a parse.
	 *)

	type result

	structure LrTable : LR_TABLE
	structure Token : TOKEN
	sharing Token.LrTable = LrTable

	(* structure Actions contains the functions which mantain the
	   semantic values stack in the parser.  Void is used to provide
	   a default value for the semantic stack.
	 *)

	structure Actions : 
	  sig
	      val actions : int * pos *
		   (LrTable.state * (svalue * pos * pos)) list * arg->
		         LrTable.nonterm * (svalue * pos * pos) *
			 ((LrTable.state *(svalue * pos * pos)) list)
	      val void : svalue
	      val extract : svalue -> result
	  end

	(* structure EC contains information used to improve error
	   recovery in an error-correcting parser *)

	structure EC :
	   sig
	     val is_keyword : LrTable.term -> bool
	     val noShift : LrTable.term -> bool
 	     val preferred_change : (LrTable.term list * LrTable.term list) list
	     val errtermvalue : LrTable.term -> svalue
	     val showTerminal : LrTable.term -> string
	     val terms: LrTable.term list
	   end

	(* table is the LR table for the parser *)

	val table : LrTable.table
    end

(* signature PARSER is the signature that most user parsers created by 
   SML-Yacc will match.
*)

signature PARSER =
    sig
        structure Token : TOKEN
	structure Stream : STREAM
	exception ParseError

	(* type pos is the type of line numbers *)

	type pos

	(* type result is the type of the result from the parser *)

	type result

         (* the type of the user-supplied argument to the parser *)
 	type arg
	
	(* type svalue is the type of semantic values for the semantic value
	   stack
	 *)

	type svalue

	(* val makeLexer is used to create a stream of tokens for the parser *)

	val makeLexer : (int -> string) ->
			 (svalue,pos) Token.token Stream.stream

	(* val parse takes a stream of tokens and a function to TextIO.print
	   errors and returns a value of type result and a stream containing
	   the unused tokens
	 *)

	val parse : int * ((svalue,pos) Token.token Stream.stream) *
		    (string * pos * pos -> unit) * arg ->
				result * (svalue,pos) Token.token Stream.stream

	val sameToken : (svalue,pos) Token.token * (svalue,pos) Token.token ->
				bool
     end

(* signature ARG_PARSER is the signature that will be matched by parsers whose
    lexer takes an additional argument.
*)

signature ARG_PARSER = 
    sig
        structure Token : TOKEN
	structure Stream : STREAM
	exception ParseError

	type arg
	type lexarg
	type pos
	type result
	type svalue

	val makeLexer : (int -> string) -> lexarg ->
			 (svalue,pos) Token.token Stream.stream
	val parse : int * ((svalue,pos) Token.token Stream.stream) *
		    (string * pos * pos -> unit) * arg ->
				result * (svalue,pos) Token.token Stream.stream

	val sameToken : (svalue,pos) Token.token * (svalue,pos) Token.token ->
				bool
     end


(**** Original file: join.sml ****)

(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi *)

(* functor Join creates a user parser by putting together a Lexer structure,
   an LrValues structure, and a polymorphic parser structure.  Note that
   the Lexer and LrValues structure must share the type pos (i.e. the type
   of line numbers), the type svalues for semantic values, and the type
   of tokens.
*)

functor Join(structure Lex : LEXER
	     structure ParserData: PARSER_DATA
	     structure LrParser : LR_PARSER
	     sharing ParserData.LrTable = LrParser.LrTable
	     sharing ParserData.Token = LrParser.Token
	     sharing type Lex.UserDeclarations.svalue = ParserData.svalue
	     sharing type Lex.UserDeclarations.pos = ParserData.pos
	     sharing type Lex.UserDeclarations.token = ParserData.Token.token)
		 : PARSER =
struct
    structure Token = ParserData.Token
    structure Stream = LrParser.Stream
 
    exception ParseError = LrParser.ParseError

    type arg = ParserData.arg
    type pos = ParserData.pos
    type result = ParserData.result
    type svalue = ParserData.svalue
    val makeLexer = LrParser.Stream.streamify o Lex.makeLexer
    val parse = fn (lookahead,lexer,error,arg) =>
	(fn (a,b) => (ParserData.Actions.extract a,b))
     (LrParser.parse {table = ParserData.table,
	        lexer=lexer,
		lookahead=lookahead,
		saction = ParserData.Actions.actions,
		arg=arg,
		void= ParserData.Actions.void,
	        ec = {is_keyword = ParserData.EC.is_keyword,
		      noShift = ParserData.EC.noShift,
		      preferred_change = ParserData.EC.preferred_change,
		      errtermvalue = ParserData.EC.errtermvalue,
		      error=error,
		      showTerminal = ParserData.EC.showTerminal,
		      terms = ParserData.EC.terms}}
      )
     val sameToken = Token.sameToken
end

(* functor JoinWithArg creates a variant of the parser structure produced 
   above.  In this case, the makeLexer take an additional argument before
   yielding a value of type unit -> (svalue,pos) token
 *)

functor JoinWithArg(structure Lex : ARG_LEXER
	     structure ParserData: PARSER_DATA
	     structure LrParser : LR_PARSER
	     sharing ParserData.LrTable = LrParser.LrTable
	     sharing ParserData.Token = LrParser.Token
	     sharing type Lex.UserDeclarations.svalue = ParserData.svalue
	     sharing type Lex.UserDeclarations.pos = ParserData.pos
	     sharing type Lex.UserDeclarations.token = ParserData.Token.token)
		 : ARG_PARSER  =
struct
    structure Token = ParserData.Token
    structure Stream = LrParser.Stream

    exception ParseError = LrParser.ParseError

    type arg = ParserData.arg
    type lexarg = Lex.UserDeclarations.arg
    type pos = ParserData.pos
    type result = ParserData.result
    type svalue = ParserData.svalue

    val makeLexer = fn s => fn arg =>
		 LrParser.Stream.streamify (Lex.makeLexer s arg)
    val parse = fn (lookahead,lexer,error,arg) =>
	(fn (a,b) => (ParserData.Actions.extract a,b))
     (LrParser.parse {table = ParserData.table,
	        lexer=lexer,
		lookahead=lookahead,
		saction = ParserData.Actions.actions,
		arg=arg,
		void= ParserData.Actions.void,
	        ec = {is_keyword = ParserData.EC.is_keyword,
		      noShift = ParserData.EC.noShift,
		      preferred_change = ParserData.EC.preferred_change,
		      errtermvalue = ParserData.EC.errtermvalue,
		      error=error,
		      showTerminal = ParserData.EC.showTerminal,
		      terms = ParserData.EC.terms}}
      )
    val sameToken = Token.sameToken
end;

(**** Original file: lrtable.sml ****)

(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi *)
structure LrTable : LR_TABLE = 
    struct
	open Array List
	infix 9 sub
	datatype ('a,'b) pairlist = EMPTY
				  | PAIR of 'a * 'b * ('a,'b) pairlist
	datatype term = T of int
	datatype nonterm = NT of int
	datatype state = STATE of int
	datatype action = SHIFT of state
			| REDUCE of int (* rulenum from grammar *)
			| ACCEPT
			| ERROR
	exception Goto of state * nonterm
	type table = {states: int, rules : int,initialState: state,
		      action: ((term,action) pairlist * action) array,
		      goto :  (nonterm,state) pairlist array}
	val numStates = fn ({states,...} : table) => states
	val numRules = fn ({rules,...} : table) => rules
	val describeActions =
	   fn ({action,...} : table) => 
	           fn (STATE s) => action sub s
	val describeGoto =
	   fn ({goto,...} : table) =>
	           fn (STATE s) => goto sub s
	fun findTerm (T term,row,default) =
	    let fun find (PAIR (T key,data,r)) =
		       if key < term then find r
		       else if key=term then data
		       else default
		   | find EMPTY = default
	    in find row
	    end
	fun findNonterm (NT nt,row) =
	    let fun find (PAIR (NT key,data,r)) =
		       if key < nt then find r
		       else if key=nt then SOME data
		       else NONE
		   | find EMPTY = NONE
	    in find row
	    end
	val action = fn ({action,...} : table) =>
		fn (STATE state,term) =>
		  let val (row,default) = action sub state
		  in findTerm(term,row,default)
		  end
	val goto = fn ({goto,...} : table) =>
			fn (a as (STATE state,nonterm)) =>
			  case findNonterm(nonterm,goto sub state)
			  of SOME state => state
			   | NONE => raise (Goto a)
	val initialState = fn ({initialState,...} : table) => initialState
	val mkLrTable = fn {actions,gotos,initialState,numStates,numRules} =>
	     ({action=actions,goto=gotos,
	       states=numStates,
	       rules=numRules,
               initialState=initialState} : table)
end;

(**** Original file: stream.sml ****)

(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi *)

(* Stream: a structure implementing a lazy stream.  The signature STREAM
   is found in base.sig *)

structure Stream :> STREAM =
struct
   datatype 'a str = EVAL of 'a * 'a str Unsynchronized.ref | UNEVAL of (unit->'a)

   type 'a stream = 'a str Unsynchronized.ref

   fun get(Unsynchronized.ref(EVAL t)) = t
     | get(s as Unsynchronized.ref(UNEVAL f)) = 
	    let val t = (f(), Unsynchronized.ref(UNEVAL f)) in s := EVAL t; t end

   fun streamify f = Unsynchronized.ref(UNEVAL f)
   fun cons(a,s) = Unsynchronized.ref(EVAL(a,s))

end;

(**** Original file: parser2.sml ****)

(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi *)

(* parser.sml:  This is a parser driver for LR tables with an error-recovery
   routine added to it.  The routine used is described in detail in this
   article:

	'A Practical Method for LR and LL Syntactic Error Diagnosis and
	 Recovery', by M. Burke and G. Fisher, ACM Transactions on
	 Programming Langauges and Systems, Vol. 9, No. 2, April 1987,
	 pp. 164-197.

    This program is an implementation is the partial, deferred method discussed
    in the article.  The algorithm and data structures used in the program
    are described below.  

    This program assumes that all semantic actions are delayed.  A semantic
    action should produce a function from unit -> value instead of producing the
    normal value.  The parser returns the semantic value on the top of the
    stack when accept is encountered.  The user can deconstruct this value
    and apply the unit -> value function in it to get the answer.

    It also assumes that the lexer is a lazy stream.

    Data Structures:
    ----------------
	
	* The parser:

	   The state stack has the type

		 (state * (semantic value * line # * line #)) list

	   The parser keeps a queue of (state stack * lexer pair).  A lexer pair
	 consists of a terminal * value pair and a lexer.  This allows the 
	 parser to reconstruct the states for terminals to the left of a
	 syntax error, and attempt to make error corrections there.

	   The queue consists of a pair of lists (x,y).  New additions to
	 the queue are cons'ed onto y.  The first element of x is the top
	 of the queue.  If x is nil, then y is reversed and used
	 in place of x.

    Algorithm:
    ----------

	* The steady-state parser:  

	    This parser keeps the length of the queue of state stacks at
	a steady state by always removing an element from the front when
	another element is placed on the end.

	    It has these arguments:

	   stack: current stack
	   queue: value of the queue
	   lexPair ((terminal,value),lex stream)

	When SHIFT is encountered, the state to shift to and the value are
	are pushed onto the state stack.  The state stack and lexPair are
	placed on the queue.  The front element of the queue is removed.

	When REDUCTION is encountered, the rule is applied to the current
	stack to yield a triple (nonterm,value,new stack).  A new
	stack is formed by adding (goto(top state of stack,nonterm),value)
	to the stack.

	When ACCEPT is encountered, the top value from the stack and the
	lexer are returned.

	When an ERROR is encountered, fixError is called.  FixError
	takes the arguments to the parser, fixes the error if possible and
        returns a new set of arguments.

	* The distance-parser:

	This parser includes an additional argument distance.  It pushes
	elements on the queue until it has parsed distance tokens, or an
	ACCEPT or ERROR occurs.  It returns a stack, lexer, the number of
	tokens left unparsed, a queue, and an action option.
*)

signature FIFO = 
  sig type 'a queue
      val empty : 'a queue
      exception Empty
      val get : 'a queue -> 'a * 'a queue
      val put : 'a * 'a queue -> 'a queue
  end

(* drt (12/15/89) -- the functor should be used in development work, but
   it wastes space in the release version.

functor ParserGen(structure LrTable : LR_TABLE
		  structure Stream : STREAM) : LR_PARSER =
*)

structure LrParser :> LR_PARSER =
   struct
      structure LrTable = LrTable
      structure Stream = Stream

      fun eqT (LrTable.T i, LrTable.T i') = i = i'

      structure Token : TOKEN =
	struct
	    structure LrTable = LrTable
	    datatype ('a,'b) token = TOKEN of LrTable.term * ('a * 'b * 'b)
	    val sameToken = fn (TOKEN(t,_),TOKEN(t',_)) => eqT (t,t')
        end

      open LrTable
      open Token

      val DEBUG1 = false
      val DEBUG2 = false
      exception ParseError
      exception ParseImpossible of int

      structure Fifo :> FIFO =
        struct
	  type 'a queue = ('a list * 'a list)
	  val empty = (nil,nil)
	  exception Empty
	  fun get(a::x, y) = (a, (x,y))
	    | get(nil, nil) = raise Empty
	    | get(nil, y) = get(rev y, nil)
 	  fun put(a,(x,y)) = (x,a::y)
        end

      type ('a,'b) elem = (state * ('a * 'b * 'b))
      type ('a,'b) stack = ('a,'b) elem list
      type ('a,'b) lexv = ('a,'b) token
      type ('a,'b) lexpair = ('a,'b) lexv * (('a,'b) lexv Stream.stream)
      type ('a,'b) distanceParse =
		 ('a,'b) lexpair *
		 ('a,'b) stack * 
		 (('a,'b) stack * ('a,'b) lexpair) Fifo.queue *
		 int ->
		   ('a,'b) lexpair *
		   ('a,'b) stack * 
		   (('a,'b) stack * ('a,'b) lexpair) Fifo.queue *
		   int *
		   action option

      type ('a,'b) ecRecord =
	 {is_keyword : term -> bool,
          preferred_change : (term list * term list) list,
	  error : string * 'b * 'b -> unit,
	  errtermvalue : term -> 'a,
	  terms : term list,
	  showTerminal : term -> string,
	  noShift : term -> bool}

      local 
	 
	 val println = fn s => (TextIO.print s; TextIO.print "\n")
	 val showState = fn (STATE s) => "STATE " ^ (Int.toString s)
      in
        fun printStack(stack: ('a,'b) stack, n: int) =
         case stack
           of (state,_) :: rest =>
                 (TextIO.print("\t" ^ Int.toString n ^ ": ");
                  println(showState state);
                  printStack(rest, n+1))
            | nil => ()
                
        fun prAction showTerminal
		 (stack as (state,_) :: _, next as (TOKEN (term,_),_), action) =
             (println "Parse: state stack:";
              printStack(stack, 0);
              TextIO.print("       state="
                         ^ showState state	
                         ^ " next="
                         ^ showTerminal term
                         ^ " action="
                        );
              case action
                of SHIFT state => println ("SHIFT " ^ (showState state))
                 | REDUCE i => println ("REDUCE " ^ (Int.toString i))
                 | ERROR => println "ERROR"
		 | ACCEPT => println "ACCEPT")
        | prAction _ (_,_,action) = ()
     end

    (* ssParse: parser which maintains the queue of (state * lexvalues) in a
	steady-state.  It takes a table, showTerminal function, saction
	function, and fixError function.  It parses until an ACCEPT is
	encountered, or an exception is raised.  When an error is encountered,
	fixError is called with the arguments of parseStep (lexv,stack,and
	queue).  It returns the lexv, and a new stack and queue adjusted so
	that the lexv can be parsed *)
	
    val ssParse =
      fn (table,showTerminal,saction,fixError,arg) =>
	let val prAction = prAction showTerminal
	    val action = LrTable.action table
	    val goto = LrTable.goto table
	    fun parseStep(args as
			 (lexPair as (TOKEN (terminal, value as (_,leftPos,_)),
				      lexer
				      ),
			  stack as (state,_) :: _,
			  queue)) =
	      let val nextAction = action (state,terminal)
	          val _ = if DEBUG1 then prAction(stack,lexPair,nextAction)
			  else ()
	      in case nextAction
		 of SHIFT s =>
		  let val newStack = (s,value) :: stack
		      val newLexPair = Stream.get lexer
		      val (_,newQueue) =Fifo.get(Fifo.put((newStack,newLexPair),
							    queue))
		  in parseStep(newLexPair,(s,value)::stack,newQueue)
		  end
		 | REDUCE i =>
		     (case saction(i,leftPos,stack,arg)
		      of (nonterm,value,stack as (state,_) :: _) =>
		          parseStep(lexPair,(goto(state,nonterm),value)::stack,
				    queue)
		       | _ => raise (ParseImpossible 197))
		 | ERROR => parseStep(fixError args)
		 | ACCEPT => 
			(case stack
			 of (_,(topvalue,_,_)) :: _ =>
				let val (token,restLexer) = lexPair
				in (topvalue,Stream.cons(token,restLexer))
				end
			  | _ => raise (ParseImpossible 202))
	      end
	    | parseStep _ = raise (ParseImpossible 204)
	in parseStep
	end

    (*  distanceParse: parse until n tokens are shifted, or accept or
	error are encountered.  Takes a table, showTerminal function, and
	semantic action function.  Returns a parser which takes a lexPair
	(lex result * lexer), a state stack, a queue, and a distance
	(must be > 0) to parse.  The parser returns a new lex-value, a stack
	with the nth token shifted on top, a queue, a distance, and action
	option. *)

    val distanceParse =
      fn (table,showTerminal,saction,arg) =>
	let val prAction = prAction showTerminal
	    val action = LrTable.action table
	    val goto = LrTable.goto table
	    fun parseStep(lexPair,stack,queue,0) = (lexPair,stack,queue,0,NONE)
	      | parseStep(lexPair as (TOKEN (terminal, value as (_,leftPos,_)),
				      lexer
				     ),
			  stack as (state,_) :: _,
			  queue,distance) =
	      let val nextAction = action(state,terminal)
	          val _ = if DEBUG1 then prAction(stack,lexPair,nextAction)
			  else ()
	      in case nextAction
		 of SHIFT s =>
		  let val newStack = (s,value) :: stack
		      val newLexPair = Stream.get lexer
		  in parseStep(newLexPair,(s,value)::stack,
			       Fifo.put((newStack,newLexPair),queue),distance-1)
		  end
		 | REDUCE i =>
		    (case saction(i,leftPos,stack,arg)
		      of (nonterm,value,stack as (state,_) :: _) =>
		         parseStep(lexPair,(goto(state,nonterm),value)::stack,
				 queue,distance)
		      | _ => raise (ParseImpossible 240))
		 | ERROR => (lexPair,stack,queue,distance,SOME nextAction)
		 | ACCEPT => (lexPair,stack,queue,distance,SOME nextAction)
	      end
	   | parseStep _ = raise (ParseImpossible 242)
	in parseStep : ('_a,'_b) distanceParse 
	end

(* mkFixError: function to create fixError function which adjusts parser state
   so that parse may continue in the presence of an error *)

fun mkFixError({is_keyword,terms,errtermvalue,
	      preferred_change,noShift,
	      showTerminal,error,...} : ('_a,'_b) ecRecord,
	     distanceParse : ('_a,'_b) distanceParse,
	     minAdvance,maxAdvance) 

            (lexv as (TOKEN (term,value as (_,leftPos,_)),_),stack,queue) =
    let val _ = if DEBUG2 then
			error("syntax error found at " ^ (showTerminal term),
			      leftPos,leftPos)
		else ()

        fun tokAt(t,p) = TOKEN(t,(errtermvalue t,p,p))

	val minDelta = 3

	(* pull all the state * lexv elements from the queue *)

	val stateList = 
	   let fun f q = let val (elem,newQueue) = Fifo.get q
			 in elem :: (f newQueue)
			 end handle Fifo.Empty => nil
	   in f queue
	   end

	(* now number elements of stateList, giving distance from
	   error token *)

	val (_, numStateList) =
	      List.foldr (fn (a,(num,r)) => (num+1,(a,num)::r)) (0, []) stateList

	(* Represent the set of potential changes as a linked list.

	   Values of datatype Change hold information about a potential change.

	   oper = oper to be applied
	   pos = the # of the element in stateList that would be altered.
	   distance = the number of tokens beyond the error token which the
	     change allows us to parse.
	   new = new terminal * value pair at that point
	   orig = original terminal * value pair at the point being changed.
	 *)

	datatype ('a,'b) change = CHANGE of
	   {pos : int, distance : int, leftPos: 'b, rightPos: 'b,
	    new : ('a,'b) lexv list, orig : ('a,'b) lexv list}


         val showTerms = String.concat o map (fn TOKEN(t,_) => " " ^ showTerminal t)

	 val printChange = fn c =>
	  let val CHANGE {distance,new,orig,pos,...} = c
	  in (TextIO.print ("{distance= " ^ (Int.toString distance));
	      TextIO.print (",orig ="); TextIO.print(showTerms orig);
	      TextIO.print (",new ="); TextIO.print(showTerms new);
	      TextIO.print (",pos= " ^ (Int.toString pos));
	      TextIO.print "}\n")
	  end

	val printChangeList = app printChange

(* parse: given a lexPair, a stack, and the distance from the error
   token, return the distance past the error token that we are able to parse.*)

	fun parse (lexPair,stack,queuePos : int) =
	    case distanceParse(lexPair,stack,Fifo.empty,queuePos+maxAdvance+1)
             of (_,_,_,distance,SOME ACCEPT) => 
		        if maxAdvance-distance-1 >= 0 
			    then maxAdvance 
			    else maxAdvance-distance-1
	      | (_,_,_,distance,_) => maxAdvance - distance - 1

(* catList: concatenate results of scanning list *)

	fun catList l f = List.foldr (fn(a,r)=> f a @ r) [] l

        fun keywordsDelta new = if List.exists (fn(TOKEN(t,_))=>is_keyword t) new
	               then minDelta else 0

        fun tryChange{lex,stack,pos,leftPos,rightPos,orig,new} =
	     let val lex' = List.foldr (fn (t',p)=>(t',Stream.cons p)) lex new
		 val distance = parse(lex',stack,pos+length new-length orig)
	      in if distance >= minAdvance + keywordsDelta new 
		   then [CHANGE{pos=pos,leftPos=leftPos,rightPos=rightPos,
				distance=distance,orig=orig,new=new}] 
		   else []
	     end


(* tryDelete: Try to delete n terminals.
              Return single-element [success] or nil.
	      Do not delete unshiftable terminals. *)


    fun tryDelete n ((stack,lexPair as (TOKEN(term,(_,l,r)),_)),qPos) =
	let fun del(0,accum,left,right,lexPair) =
	          tryChange{lex=lexPair,stack=stack,
			    pos=qPos,leftPos=left,rightPos=right,
			    orig=rev accum, new=[]}
	      | del(n,accum,left,right,(tok as TOKEN(term,(_,_,r)),lexer)) =
		   if noShift term then []
		   else del(n-1,tok::accum,left,r,Stream.get lexer)
         in del(n,[],l,r,lexPair)
        end

(* tryInsert: try to insert tokens before the current terminal;
       return a list of the successes  *)

        fun tryInsert((stack,lexPair as (TOKEN(_,(_,l,_)),_)),queuePos) =
	       catList terms (fn t =>
		 tryChange{lex=lexPair,stack=stack,
			   pos=queuePos,orig=[],new=[tokAt(t,l)],
			   leftPos=l,rightPos=l})
			      
(* trySubst: try to substitute tokens for the current terminal;
       return a list of the successes  *)

        fun trySubst ((stack,lexPair as (orig as TOKEN (term,(_,l,r)),lexer)),
		      queuePos) =
	      if noShift term then []
	      else
		  catList terms (fn t =>
		      tryChange{lex=Stream.get lexer,stack=stack,
				pos=queuePos,
				leftPos=l,rightPos=r,orig=[orig],
				new=[tokAt(t,r)]})

     (* do_delete(toks,lexPair) tries to delete tokens "toks" from "lexPair".
         If it succeeds, returns SOME(toks',l,r,lp), where
	     toks' is the actual tokens (with positions and values) deleted,
	     (l,r) are the (leftmost,rightmost) position of toks', 
	     lp is what remains of the stream after deletion 
     *)
        fun do_delete(nil,lp as (TOKEN(_,(_,l,_)),_)) = SOME(nil,l,l,lp)
          | do_delete([t],(tok as TOKEN(t',(_,l,r)),lp')) =
	       if eqT (t, t')
		   then SOME([tok],l,r,Stream.get lp')
                   else NONE
          | do_delete(t::rest,(tok as TOKEN(t',(_,l,r)),lp')) =
	       if eqT (t,t')
		   then case do_delete(rest,Stream.get lp')
                         of SOME(deleted,l',r',lp'') =>
			       SOME(tok::deleted,l,r',lp'')
			  | NONE => NONE
		   else NONE
			     
        fun tryPreferred((stack,lexPair),queuePos) =
	    catList preferred_change (fn (delete,insert) =>
	       if List.exists noShift delete then [] (* should give warning at
						 parser-generation time *)
               else case do_delete(delete,lexPair)
                     of SOME(deleted,l,r,lp) => 
			    tryChange{lex=lp,stack=stack,pos=queuePos,
				      leftPos=l,rightPos=r,orig=deleted,
				      new=map (fn t=>(tokAt(t,r))) insert}
		      | NONE => [])

	val changes = catList numStateList tryPreferred @
	                catList numStateList tryInsert @
			  catList numStateList trySubst @
			    catList numStateList (tryDelete 1) @
			      catList numStateList (tryDelete 2) @
			        catList numStateList (tryDelete 3)

	val findMaxDist = fn l => 
	  List.foldr (fn (CHANGE {distance,...},high) => Int.max(distance,high)) 0 l

(* maxDist: max distance past error taken that we could parse *)

	val maxDist = findMaxDist changes

(* remove changes which did not parse maxDist tokens past the error token *)

        val changes = catList changes 
	      (fn(c as CHANGE{distance,...}) => 
		  if distance=maxDist then [c] else [])

      in case changes 
	  of (l as change :: _) =>
	      let fun print_msg (CHANGE {new,orig,leftPos,rightPos,...}) =
		  let val s = 
		      case (orig,new)
			  of (_::_,[]) => "deleting " ^ (showTerms orig)
	                   | ([],_::_) => "inserting " ^ (showTerms new)
			   | _ => "replacing " ^ (showTerms orig) ^
				 " with " ^ (showTerms new)
		  in error ("syntax error: " ^ s,leftPos,rightPos)
		  end
		   
		  val _ = 
		      (if length l > 1 andalso DEBUG2 then
			   (TextIO.print "multiple fixes possible; could fix it by:\n";
			    app print_msg l;
			    TextIO.print "chosen correction:\n")
		       else ();
		       print_msg change)

		  (* findNth: find nth queue entry from the error
		   entry.  Returns the Nth queue entry and the  portion of
		   the queue from the beginning to the nth-1 entry.  The
		   error entry is at the end of the queue.

		   Examples:

		   queue = a b c d e
		   findNth 0 = (e,a b c d)
		   findNth 1 =  (d,a b c)
		   *)

		  val findNth = fn n =>
		      let fun f (h::t,0) = (h,rev t)
			    | f (h::t,n) = f(t,n-1)
			    | f (nil,_) = let exception FindNth
					  in raise FindNth
					  end
		      in f (rev stateList,n)
		      end
		
		  val CHANGE {pos,orig,new,...} = change
		  val (last,queueFront) = findNth pos
		  val (stack,lexPair) = last

		  val lp1 = List.foldl(fn (_,(_,r)) => Stream.get r) lexPair orig
		  val lp2 = List.foldr(fn(t,r)=>(t,Stream.cons r)) lp1 new

		  val restQueue = 
		      Fifo.put((stack,lp2),
			       List.foldl Fifo.put Fifo.empty queueFront)

		  val (lexPair,stack,queue,_,_) =
		      distanceParse(lp2,stack,restQueue,pos)

	      in (lexPair,stack,queue)
	      end
	| nil => (error("syntax error found at " ^ (showTerminal term),
			leftPos,leftPos); raise ParseError)
    end

   val parse = fn {arg,table,lexer,saction,void,lookahead,
		   ec=ec as {showTerminal,...} : ('_a,'_b) ecRecord} =>
	let val distance = 15   (* defer distance tokens *)
	    val minAdvance = 1  (* must parse at least 1 token past error *)
	    val maxAdvance = Int.max(lookahead,0)(* max distance for parse check *)
	    val lexPair = Stream.get lexer
	    val (TOKEN (_,(_,leftPos,_)),_) = lexPair
	    val startStack = [(initialState table,(void,leftPos,leftPos))]
	    val startQueue = Fifo.put((startStack,lexPair),Fifo.empty)
	    val distanceParse = distanceParse(table,showTerminal,saction,arg)
	    val fixError = mkFixError(ec,distanceParse,minAdvance,maxAdvance)
	    val ssParse = ssParse(table,showTerminal,saction,fixError,arg)
	    fun loop (lexPair,stack,queue,_,SOME ACCEPT) =
		   ssParse(lexPair,stack,queue)
	      | loop (lexPair,stack,queue,0,_) = ssParse(lexPair,stack,queue)
	      | loop (lexPair,stack,queue,distance,SOME ERROR) =
		 let val (lexPair,stack,queue) = fixError(lexPair,stack,queue)
		 in loop (distanceParse(lexPair,stack,queue,distance))
		 end
	      | loop _ = let exception ParseInternal
			 in raise ParseInternal
			 end
	in loop (distanceParse(lexPair,startStack,startQueue,distance))
	end
 end;

;
print_depth 10;

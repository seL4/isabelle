(* ========================================================================= *)
(* PRETTY-PRINTING                                                           *)
(* Copyright (c) 2001-2008 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

structure Print :> Print =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Constants.                                                                *)
(* ------------------------------------------------------------------------- *)

val initialLineLength = 75;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun revAppend xs s =
    case xs of
      [] => s ()
    | x :: xs => revAppend xs (K (Stream.Cons (x,s)));

fun revConcat strm =
    case strm of
      Stream.Nil => Stream.Nil
    | Stream.Cons (h,t) => revAppend h (revConcat o t);

local
  fun join current prev = (prev ^ "\n", current);
in
  fun joinNewline strm =
      case strm of
        Stream.Nil => Stream.Nil
      | Stream.Cons (h,t) => Stream.maps join Stream.singleton h (t ());
end;

local
  fun calcSpaces n = nChars #" " n;

  val cachedSpaces = Vector.tabulate (initialLineLength,calcSpaces);
in
  fun nSpaces n =
      if n < initialLineLength then Vector.sub (cachedSpaces,n)
      else calcSpaces n;
end;

(* ------------------------------------------------------------------------- *)
(* A type of pretty-printers.                                                *)
(* ------------------------------------------------------------------------- *)

datatype breakStyle = Consistent | Inconsistent;

datatype ppStep =
    BeginBlock of breakStyle * int
  | EndBlock
  | AddString of string
  | AddBreak of int
  | AddNewline;

type ppstream = ppStep Stream.stream;

type 'a pp = 'a -> ppstream;

fun breakStyleToString style =
    case style of
      Consistent => "Consistent"
    | Inconsistent => "Inconsistent";

fun ppStepToString step =
    case step of
      BeginBlock _ => "BeginBlock"
    | EndBlock => "EndBlock"
    | AddString _ => "AddString"
    | AddBreak _ => "AddBreak"
    | AddNewline => "AddNewline";

(* ------------------------------------------------------------------------- *)
(* Pretty-printer primitives.                                                *)
(* ------------------------------------------------------------------------- *)

fun beginBlock style indent = Stream.singleton (BeginBlock (style,indent));

val endBlock = Stream.singleton EndBlock;

fun addString s = Stream.singleton (AddString s);

fun addBreak spaces = Stream.singleton (AddBreak spaces);

val addNewline = Stream.singleton AddNewline;

val skip : ppstream = Stream.Nil;

fun sequence pp1 pp2 : ppstream = Stream.append pp1 (K pp2);

local
  fun dup pp n () = if n = 1 then pp else Stream.append pp (dup pp (n - 1));
in
  fun duplicate n pp = if n = 0 then skip else dup pp n ();
end;

val program : ppstream list -> ppstream = Stream.concatList;

val stream : ppstream Stream.stream -> ppstream = Stream.concat;

fun block style indent pp = program [beginBlock style indent, pp, endBlock];

fun blockProgram style indent pps = block style indent (program pps);

fun bracket l r pp =
    blockProgram Inconsistent (size l)
      [addString l,
       pp,
       addString r];

fun field f pp =
    blockProgram Inconsistent 2
      [addString (f ^ " ="),
       addBreak 1,
       pp];

val record =
    let
      val sep = sequence (addString ",") (addBreak 1)

      fun recordField (f,pp) = field f pp

      fun sepField f = sequence sep (recordField f)

      fun fields [] = []
        | fields (f :: fs) = recordField f :: map sepField fs
    in
      bracket "{" "}" o blockProgram Consistent 0 o fields
    end;

(* ------------------------------------------------------------------------- *)
(* Pretty-printer combinators.                                               *)
(* ------------------------------------------------------------------------- *)

fun ppMap f ppB a : ppstream = ppB (f a);

fun ppBracket l r ppA a = bracket l r (ppA a);

fun ppOp s = sequence (if s = "" then skip else addString s) (addBreak 1);

fun ppOp2 ab ppA ppB (a,b) =
    blockProgram Inconsistent 0
      [ppA a,
       ppOp ab,
       ppB b];

fun ppOp3 ab bc ppA ppB ppC (a,b,c) =
    blockProgram Inconsistent 0
      [ppA a,
       ppOp ab,
       ppB b,
       ppOp bc,
       ppC c];

fun ppOpList s ppA =
    let
      fun ppOpA a = sequence (ppOp s) (ppA a)
    in
      fn [] => skip
       | h :: t => blockProgram Inconsistent 0 (ppA h :: map ppOpA t)
    end;

fun ppOpStream s ppA =
    let
      fun ppOpA a = sequence (ppOp s) (ppA a)
    in
      fn Stream.Nil => skip
       | Stream.Cons (h,t) =>
         blockProgram Inconsistent 0
           [ppA h,
            Stream.concat (Stream.map ppOpA (t ()))]
    end;

(* ------------------------------------------------------------------------- *)
(* Pretty-printers for common types.                                         *)
(* ------------------------------------------------------------------------- *)

fun ppChar c = addString (str c);

val ppString = addString;

fun ppEscapeString {escape} =
    let
      val escapeMap = map (fn c => (c, "\\" ^ str c)) escape

      fun escapeChar c =
          case c of
            #"\\" => "\\\\"
          | #"\n" => "\\n"
          | #"\t" => "\\t"
          | _ =>
            case List.find (equal c o fst) escapeMap of
              SOME (_,s) => s
            | NONE => str c
    in
      fn s => addString (String.translate escapeChar s)
    end;

val ppUnit : unit pp = K (addString "()");

fun ppBool b = addString (if b then "true" else "false");

fun ppInt i = addString (Int.toString i);

local
  val ppNeg = addString "~"
  and ppSep = addString ","
  and ppZero = addString "0"
  and ppZeroZero = addString "00";

  fun ppIntBlock i =
      if i < 10 then sequence ppZeroZero (ppInt i)
      else if i < 100 then sequence ppZero (ppInt i)
      else ppInt i;

  fun ppIntBlocks i =
      if i < 1000 then ppInt i
      else sequence (ppIntBlocks (i div 1000))
             (sequence ppSep (ppIntBlock (i mod 1000)));
in
  fun ppPrettyInt i =
      if i < 0 then sequence ppNeg (ppIntBlocks (~i))
      else ppIntBlocks i;
end;

fun ppReal r = addString (Real.toString r);

fun ppPercent p = addString (percentToString p);

fun ppOrder x =
    addString
      (case x of
         LESS => "Less"
       | EQUAL => "Equal"
       | GREATER => "Greater");

fun ppList ppA = ppBracket "[" "]" (ppOpList "," ppA);

fun ppStream ppA = ppBracket "[" "]" (ppOpStream "," ppA);

fun ppOption ppA ao =
    case ao of
      SOME a => ppA a
    | NONE => addString "-";

fun ppPair ppA ppB = ppBracket "(" ")" (ppOp2 "," ppA ppB);

fun ppTriple ppA ppB ppC = ppBracket "(" ")" (ppOp3 "," "," ppA ppB ppC);

fun ppBreakStyle style = addString (breakStyleToString style);

fun ppPpStep step =
    let
      val cmd = ppStepToString step
    in
      blockProgram Inconsistent 2
        (addString cmd ::
         (case step of
            BeginBlock style_indent =>
              [addBreak 1,
               ppPair ppBreakStyle ppInt style_indent]
          | EndBlock => []
          | AddString s =>
              [addBreak 1,
               addString ("\"" ^ s ^ "\"")]
          | AddBreak n =>
              [addBreak 1,
               ppInt n]
          | AddNewline => []))
    end;

val ppPpstream = ppStream ppPpStep;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing infix operators.                                          *)
(* ------------------------------------------------------------------------- *)

datatype infixes =
    Infixes of
      {token : string,
       precedence : int,
       leftAssoc : bool} list;

local
  fun chop l =
      case l of
        #" " :: l => let val (n,l) = chop l in (n + 1, l) end
      | _ => (0,l);
in
  fun opSpaces tok =
      let
        val tok = explode tok
        val (r,tok) = chop (rev tok)
        val (l,tok) = chop (rev tok)
        val tok = implode tok
      in
        {leftSpaces = l, token = tok, rightSpaces = r}
      end;
end;

fun ppOpSpaces {leftSpaces,token,rightSpaces} =
    let
      val leftSpacesToken =
          if leftSpaces = 0 then token else nSpaces leftSpaces ^ token
    in
      sequence
        (addString leftSpacesToken)
        (addBreak rightSpaces)
    end;

local
  fun new t l acc = {tokens = [opSpaces t], leftAssoc = l} :: acc;

  fun add t l acc =
      case acc of
        [] => raise Bug "Print.layerInfixOps.layer"
      | {tokens = ts, leftAssoc = l'} :: acc =>
        if l = l' then {tokens = opSpaces t :: ts, leftAssoc = l} :: acc
        else raise Bug "Print.layerInfixOps: mixed assocs";

  fun layer ({token = t, precedence = p, leftAssoc = l}, (acc,p')) =
      let
        val acc = if p = p' then add t l acc else new t l acc
      in
        (acc,p)
      end;
in
  fun layerInfixes (Infixes i) =
      case sortMap #precedence Int.compare i of
        [] => []
      | {token = t, precedence = p, leftAssoc = l} :: i =>
        let
          val acc = new t l []

          val (acc,_) = List.foldl layer (acc,p) i
        in
          acc
        end;
end;

val tokensLayeredInfixes =
    let
      fun addToken ({leftSpaces = _, token = t, rightSpaces = _}, s) =
          StringSet.add s t

      fun addTokens ({tokens = t, leftAssoc = _}, s) =
          List.foldl addToken s t
    in
      List.foldl addTokens StringSet.empty
    end;

val tokensInfixes = tokensLayeredInfixes o layerInfixes;

local
  val mkTokenMap =
      let
        fun add (token,m) =
            let
              val {leftSpaces = _, token = t, rightSpaces = _} = token
            in
              StringMap.insert m (t, ppOpSpaces token)
            end
      in
        List.foldl add (StringMap.new ())
      end;
in
  fun ppGenInfix {tokens,leftAssoc} =
      let
        val tokenMap = mkTokenMap tokens
      in
        fn dest => fn ppSub =>
           let
             fun dest' tm =
                 case dest tm of
                   NONE => NONE
                 | SOME (t,a,b) =>
                   case StringMap.peek tokenMap t of
                     NONE => NONE
                   | SOME p => SOME (p,a,b)

             fun ppGo (tmr as (tm,r)) =
                 case dest' tm of
                   NONE => ppSub tmr
                 | SOME (p,a,b) =>
                   program
                     [(if leftAssoc then ppGo else ppSub) (a,true),
                      p,
                      (if leftAssoc then ppSub else ppGo) (b,r)]
           in
             fn tmr as (tm,_) =>
                if Option.isSome (dest' tm) then
                  block Inconsistent 0 (ppGo tmr)
                else
                  ppSub tmr
           end
      end;
end

fun ppInfixes ops =
    let
      val layeredOps = layerInfixes ops

      val toks = tokensLayeredInfixes layeredOps

      val iprinters = List.map ppGenInfix layeredOps
    in
      fn dest => fn ppSub =>
         let
           fun printer sub = foldl (fn (ip,p) => ip dest p) sub iprinters

           fun isOp t =
               case dest t of
                 SOME (x,_,_) => StringSet.member x toks
               | NONE => false

           fun subpr (tmr as (tm,_)) =
               if isOp tm then
                 blockProgram Inconsistent 1
                   [addString "(",
                    printer subpr (tm,false),
                    addString ")"]
               else
                 ppSub tmr
         in
           fn tmr => block Inconsistent 0 (printer subpr tmr)
         end
    end;

(* ------------------------------------------------------------------------- *)
(* Executing pretty-printers to generate lines.                              *)
(* ------------------------------------------------------------------------- *)

datatype blockBreakStyle =
    InconsistentBlock
  | ConsistentBlock
  | BreakingBlock;

datatype block =
    Block of
      {indent : int,
       style : blockBreakStyle,
       size : int,
       chunks : chunk list}

and chunk =
    StringChunk of {size : int, string : string}
  | BreakChunk of int
  | BlockChunk of block;

datatype state =
    State of
      {blocks : block list,
       lineIndent : int,
       lineSize : int};

val initialIndent = 0;

val initialStyle = Inconsistent;

fun liftStyle style =
    case style of
      Inconsistent => InconsistentBlock
    | Consistent => ConsistentBlock;

fun breakStyle style =
    case style of
      ConsistentBlock => BreakingBlock
    | _ => style;

fun sizeBlock (Block {size,...}) = size;

fun sizeChunk chunk =
    case chunk of
      StringChunk {size,...} => size
    | BreakChunk spaces => spaces
    | BlockChunk block => sizeBlock block;

val splitChunks =
    let
      fun split _ [] = NONE
        | split acc (chunk :: chunks) =
          case chunk of
            BreakChunk _ => SOME (rev acc, chunks)
          | _ => split (chunk :: acc) chunks
    in
      split []
    end;

val sizeChunks = List.foldl (fn (c,z) => sizeChunk c + z) 0;

local
  fun render acc [] = acc
    | render acc (chunk :: chunks) =
      case chunk of
        StringChunk {string = s, ...} => render (acc ^ s) chunks
      | BreakChunk n => render (acc ^ nSpaces n) chunks
      | BlockChunk (Block {chunks = l, ...}) =>
        render acc (List.revAppend (l,chunks));
in
  fun renderChunks indent chunks = render (nSpaces indent) (rev chunks);

  fun renderChunk indent chunk = renderChunks indent [chunk];
end;

fun isEmptyBlock block =
    let
      val Block {indent = _, style = _, size, chunks} = block

      val empty = null chunks

(*BasicDebug
      val _ = not empty orelse size = 0 orelse
              raise Bug "Print.isEmptyBlock: bad size"
*)
    in
      empty
    end;

fun checkBlock ind block =
    let
      val Block {indent, style = _, size, chunks} = block
      val _ = indent >= ind orelse raise Bug "Print.checkBlock: bad indents"
      val size' = checkChunks indent chunks
      val _ = size = size' orelse raise Bug "Print.checkBlock: wrong size"
    in
      size
    end

and checkChunks ind chunks =
    case chunks of
      [] => 0
    | chunk :: chunks => checkChunk ind chunk + checkChunks ind chunks

and checkChunk ind chunk =
    case chunk of
      StringChunk {size,...} => size
    | BreakChunk spaces => spaces
    | BlockChunk block => checkBlock ind block;

val checkBlocks =
    let
      fun check ind blocks =
          case blocks of
            [] => 0
          | block :: blocks =>
            let
              val Block {indent,...} = block
            in
              checkBlock ind block + check indent blocks
            end
    in
      check initialIndent o rev
    end;

val initialBlock =
    let
      val indent = initialIndent
      val style = liftStyle initialStyle
      val size = 0
      val chunks = []
    in
      Block
        {indent = indent,
         style = style,
         size = size,
         chunks = chunks}
    end;

val initialState =
    let
      val blocks = [initialBlock]
      val lineIndent = initialIndent
      val lineSize = 0
    in
      State
        {blocks = blocks,
         lineIndent = lineIndent,
         lineSize = lineSize}
    end;

(*BasicDebug
fun checkState state =
    (let
       val State {blocks, lineIndent = _, lineSize} = state
       val lineSize' = checkBlocks blocks
       val _ = lineSize = lineSize' orelse
               raise Error "wrong lineSize"
     in
       ()
     end
     handle Error err => raise Bug err)
    handle Bug bug => raise Bug ("Print.checkState: " ^ bug);
*)

fun isFinalState state =
    let
      val State {blocks,lineIndent,lineSize} = state
    in
      case blocks of
        [] => raise Bug "Print.isFinalState: no block"
      | [block] => isEmptyBlock block
      | _ :: _ :: _ => false
    end;

local
  fun renderBreak lineIndent (chunks,lines) =
      let
        val line = renderChunks lineIndent chunks

        val lines = line :: lines
      in
        lines
      end;

  fun renderBreaks lineIndent lineIndent' breaks lines =
      case rev breaks of
        [] => raise Bug "Print.renderBreaks"
      | c :: cs =>
        let
          val lines = renderBreak lineIndent (c,lines)
        in
          List.foldl (renderBreak lineIndent') lines cs
        end;

  fun splitAllChunks cumulatingChunks =
      let
        fun split chunks =
            case splitChunks chunks of
              SOME (prefix,chunks) => prefix :: split chunks
            | NONE => [List.concat (chunks :: cumulatingChunks)]
      in
        split
      end;

  fun mkBreak style cumulatingChunks chunks =
      case splitChunks chunks of
        NONE => NONE
      | SOME (chunks,broken) =>
        let
          val breaks =
              case style of
                InconsistentBlock =>
                [List.concat (broken :: cumulatingChunks)]
              | _ => splitAllChunks cumulatingChunks broken
        in
          SOME (breaks,chunks)
        end;

  fun naturalBreak blocks =
      case blocks of
        [] => Right ([],[])
      | block :: blocks =>
        case naturalBreak blocks of
          Left (breaks,blocks,lineIndent,lineSize) =>
          let
            val Block {size,...} = block

            val blocks = block :: blocks

            val lineSize = lineSize + size
          in
            Left (breaks,blocks,lineIndent,lineSize)
          end
        | Right (cumulatingChunks,blocks) =>
          let
            val Block {indent,style,size,chunks} = block

            val style = breakStyle style
          in
            case mkBreak style cumulatingChunks chunks of
              SOME (breaks,chunks) =>
              let
                val size = sizeChunks chunks

                val block =
                    Block
                      {indent = indent,
                       style = style,
                       size = size,
                       chunks = chunks}

                val blocks = block :: blocks

                val lineIndent = indent

                val lineSize = size
              in
                Left (breaks,blocks,lineIndent,lineSize)
              end
            | NONE =>
              let
                val cumulatingChunks = chunks :: cumulatingChunks

                val size = 0

                val chunks = []

                val block =
                    Block
                      {indent = indent,
                       style = style,
                       size = size,
                       chunks = chunks}

                val blocks = block :: blocks
              in
                Right (cumulatingChunks,blocks)
              end
          end;

  fun forceBreakBlock cumulatingChunks block =
      let
        val Block {indent, style, size = _, chunks} = block

        val style = breakStyle style

        val break =
            case mkBreak style cumulatingChunks chunks of
              SOME (breaks,chunks) =>
              let
                val lineSize = sizeChunks chunks
                val lineIndent = indent
              in
                SOME (breaks,chunks,lineIndent,lineSize)
              end
            | NONE => forceBreakChunks cumulatingChunks chunks
      in
        case break of
          SOME (breaks,chunks,lineIndent,lineSize) =>
          let
            val size = lineSize

            val block =
                Block
                  {indent = indent,
                   style = style,
                   size = size,
                   chunks = chunks}
          in
            SOME (breaks,block,lineIndent,lineSize)
          end
        | NONE => NONE
      end

  and forceBreakChunks cumulatingChunks chunks =
      case chunks of
        [] => NONE
      | chunk :: chunks =>
        case forceBreakChunk (chunks :: cumulatingChunks) chunk of
          SOME (breaks,chunk,lineIndent,lineSize) =>
          let
            val chunks = [chunk]
          in
            SOME (breaks,chunks,lineIndent,lineSize)
          end
        | NONE =>
          case forceBreakChunks cumulatingChunks chunks of
            SOME (breaks,chunks,lineIndent,lineSize) =>
            let
              val chunks = chunk :: chunks

              val lineSize = lineSize + sizeChunk chunk
            in
              SOME (breaks,chunks,lineIndent,lineSize)
            end
          | NONE => NONE

  and forceBreakChunk cumulatingChunks chunk =
      case chunk of
        StringChunk _ => NONE
      | BreakChunk _ => raise Bug "Print.forceBreakChunk: BreakChunk"
      | BlockChunk block =>
        case forceBreakBlock cumulatingChunks block of
          SOME (breaks,block,lineIndent,lineSize) =>
          let
            val chunk = BlockChunk block
          in
            SOME (breaks,chunk,lineIndent,lineSize)
          end
        | NONE => NONE;

  fun forceBreak cumulatingChunks blocks' blocks =
      case blocks of
        [] => NONE
      | block :: blocks =>
        let
          val cumulatingChunks =
              case cumulatingChunks of
                [] => raise Bug "Print.forceBreak: null cumulatingChunks"
              | _ :: cumulatingChunks => cumulatingChunks

          val blocks' =
              case blocks' of
                [] => raise Bug "Print.forceBreak: null blocks'"
              | _ :: blocks' => blocks'
        in
          case forceBreakBlock cumulatingChunks block of
            SOME (breaks,block,lineIndent,lineSize) =>
            let
              val blocks = block :: blocks'
            in
              SOME (breaks,blocks,lineIndent,lineSize)
            end
          | NONE =>
            case forceBreak cumulatingChunks blocks' blocks of
              SOME (breaks,blocks,lineIndent,lineSize) =>
              let
                val blocks = block :: blocks

                val Block {size,...} = block

                val lineSize = lineSize + size
              in
                SOME (breaks,blocks,lineIndent,lineSize)
              end
            | NONE => NONE
        end;

  fun normalize lineLength lines state =
      let
        val State {blocks,lineIndent,lineSize} = state
      in
        if lineIndent + lineSize <= lineLength then (lines,state)
        else
          let
            val break =
                case naturalBreak blocks of
                  Left break => SOME break
                | Right (c,b) => forceBreak c b blocks
          in
            case break of
              SOME (breaks,blocks,lineIndent',lineSize) =>
              let
                val lines = renderBreaks lineIndent lineIndent' breaks lines

                val state =
                    State
                      {blocks = blocks,
                       lineIndent = lineIndent',
                       lineSize = lineSize}
              in
                normalize lineLength lines state
              end
            | NONE => (lines,state)
          end
      end;

(*BasicDebug
  val normalize = fn lineLength => fn lines => fn state =>
      let
        val () = checkState state
      in
        normalize lineLength lines state
      end
      handle Bug bug =>
        raise Bug ("Print.normalize: before normalize:\n" ^ bug)
*)

  fun executeBeginBlock (style,ind) lines state =
      let
        val State {blocks,lineIndent,lineSize} = state

        val Block {indent,...} =
            case blocks of
              [] => raise Bug "Print.executeBeginBlock: no block"
            | block :: _ => block

        val indent = indent + ind

        val style = liftStyle style

        val size = 0

        val chunks = []

        val block =
            Block
              {indent = indent,
               style = style,
               size = size,
               chunks = chunks}

        val blocks = block :: blocks

        val state =
            State
              {blocks = blocks,
               lineIndent = lineIndent,
               lineSize = lineSize}
      in
        (lines,state)
      end;

  fun executeEndBlock lines state =
      let
        val State {blocks,lineIndent,lineSize} = state

        val (lineSize,blocks) =
            case blocks of
              [] => raise Bug "Print.executeEndBlock: no block"
            | topBlock :: blocks =>
              let
                val Block
                      {indent = topIndent,
                       style = topStyle,
                       size = topSize,
                       chunks = topChunks} = topBlock
              in
                case topChunks of
                  [] => (lineSize,blocks)
                | headTopChunks :: tailTopChunks =>
                  let
                    val (lineSize,topSize,topChunks) =
                        case headTopChunks of
                          BreakChunk spaces =>
                          let
                            val lineSize = lineSize - spaces
                            and topSize = topSize - spaces
                            and topChunks = tailTopChunks
                          in
                            (lineSize,topSize,topChunks)
                          end
                        | _ => (lineSize,topSize,topChunks)

                    val topBlock =
                        Block
                          {indent = topIndent,
                           style = topStyle,
                           size = topSize,
                           chunks = topChunks}
                  in
                    case blocks of
                      [] => raise Error "Print.executeEndBlock: no block"
                    | block :: blocks =>
                      let
                        val Block {indent,style,size,chunks} = block

                        val size = size + topSize

                        val chunks = BlockChunk topBlock :: chunks

                        val block =
                            Block
                              {indent = indent,
                               style = style,
                               size = size,
                               chunks = chunks}

                        val blocks = block :: blocks
                      in
                        (lineSize,blocks)
                      end
                  end
              end

        val state =
            State
              {blocks = blocks,
               lineIndent = lineIndent,
               lineSize = lineSize}
      in
        (lines,state)
      end;

  fun executeAddString lineLength s lines state =
      let
        val State {blocks,lineIndent,lineSize} = state

        val n = size s

        val blocks =
            case blocks of
              [] => raise Bug "Print.executeAddString: no block"
            | Block {indent,style,size,chunks} :: blocks =>
              let
                val size = size + n

                val chunk = StringChunk {size = n, string = s}

                val chunks = chunk :: chunks

                val block =
                    Block
                      {indent = indent,
                       style = style,
                       size = size,
                       chunks = chunks}

                val blocks = block :: blocks
              in
                blocks
              end

        val lineSize = lineSize + n

        val state =
            State
              {blocks = blocks,
               lineIndent = lineIndent,
               lineSize = lineSize}
      in
        normalize lineLength lines state
      end;

  fun executeAddBreak lineLength spaces lines state =
      let
        val State {blocks,lineIndent,lineSize} = state

        val (blocks,lineSize) =
            case blocks of
              [] => raise Bug "Print.executeAddBreak: no block"
            | Block {indent,style,size,chunks} :: blocks' =>
              case chunks of
                [] => (blocks,lineSize)
              | chunk :: chunks' =>
                let
                  val spaces =
                      case style of
                        BreakingBlock => lineLength + 1
                      | _ => spaces

                  val size = size + spaces

                  val chunks =
                      case chunk of
                        BreakChunk k => BreakChunk (k + spaces) :: chunks'
                      | _ => BreakChunk spaces :: chunks

                  val block =
                      Block
                        {indent = indent,
                         style = style,
                         size = size,
                         chunks = chunks}

                  val blocks = block :: blocks'

                  val lineSize = lineSize + spaces
                in
                  (blocks,lineSize)
                end

        val state =
            State
              {blocks = blocks,
               lineIndent = lineIndent,
               lineSize = lineSize}
      in
        normalize lineLength lines state
      end;

  fun executeBigBreak lineLength lines state =
      executeAddBreak lineLength (lineLength + 1) lines state;

  fun executeAddNewline lineLength lines state =
      let
        val (lines,state) = executeAddString lineLength "" lines state
        val (lines,state) = executeBigBreak lineLength lines state
      in
        executeAddString lineLength "" lines state
      end;

  fun final lineLength lines state =
      let
        val lines =
            if isFinalState state then lines
            else
              let
                val (lines,state) = executeBigBreak lineLength lines state

(*BasicDebug
                val _ = isFinalState state orelse raise Bug "Print.final"
*)
              in
                lines
              end
      in
        if null lines then Stream.Nil else Stream.singleton lines
      end;
in
  fun execute {lineLength} =
      let
        fun advance step state =
            let
              val lines = []
            in
              case step of
                BeginBlock style_ind => executeBeginBlock style_ind lines state
              | EndBlock => executeEndBlock lines state
              | AddString s => executeAddString lineLength s lines state
              | AddBreak spaces => executeAddBreak lineLength spaces lines state
              | AddNewline => executeAddNewline lineLength lines state
            end

(*BasicDebug
        val advance = fn step => fn state =>
            let
              val (lines,state) = advance step state
              val () = checkState state
            in
              (lines,state)
            end
            handle Bug bug =>
              raise Bug ("Print.advance: after " ^ ppStepToString step ^
                         " command:\n" ^ bug)
*)
      in
        revConcat o Stream.maps advance (final lineLength []) initialState
      end;
end;

(* ------------------------------------------------------------------------- *)
(* Executing pretty-printers with a global line length.                      *)
(* ------------------------------------------------------------------------- *)

val lineLength = ref initialLineLength;

fun toStream ppA a =
    Stream.map (fn s => s ^ "\n")
      (execute {lineLength = !lineLength} (ppA a));

fun toString ppA a =
    case execute {lineLength = !lineLength} (ppA a) of
      Stream.Nil => ""
    | Stream.Cons (h,t) => Stream.foldl (fn (s,z) => z ^ "\n" ^ s) h (t ());

fun trace ppX nameX x =
    Useful.trace (toString (ppOp2 " =" ppString ppX) (nameX,x) ^ "\n");

end

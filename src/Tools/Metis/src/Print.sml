(* ========================================================================= *)
(* PRETTY-PRINTING                                                           *)
(* Copyright (c) 2008 Joe Hurd, distributed under the BSD License            *)
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
  fun calcSpaces n = nChars #" " n;

  val cacheSize = 2 * initialLineLength;

  val cachedSpaces = Vector.tabulate (cacheSize,calcSpaces);
in
  fun nSpaces n =
      if n < cacheSize then Vector.sub (cachedSpaces,n)
      else calcSpaces n;
end;

(* ------------------------------------------------------------------------- *)
(* Escaping strings.                                                         *)
(* ------------------------------------------------------------------------- *)

fun escapeString {escape} =
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
      String.translate escapeChar
    end;

(* ------------------------------------------------------------------------- *)
(* A type of strings annotated with their size.                              *)
(* ------------------------------------------------------------------------- *)

type stringSize = string * int;

fun mkStringSize s = (s, size s);

val emptyStringSize = mkStringSize "";

(* ------------------------------------------------------------------------- *)
(* A type of pretty-printers.                                                *)
(* ------------------------------------------------------------------------- *)

datatype breakStyle = Consistent | Inconsistent;

datatype step =
    BeginBlock of breakStyle * int
  | EndBlock
  | AddString of stringSize
  | AddBreak of int
  | AddNewline;

type ppstream = step Stream.stream;

fun breakStyleToString style =
    case style of
      Consistent => "Consistent"
    | Inconsistent => "Inconsistent";

fun stepToString step =
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
  fun flatten acc chunks =
      case chunks of
        [] => rev acc
      | chunk :: chunks =>
        case chunk of
          StringChunk {string = s, ...} => flatten (s :: acc) chunks
        | BreakChunk n => flatten (nSpaces n :: acc) chunks
        | BlockChunk (Block {chunks = l, ...}) =>
          flatten acc (List.revAppend (l,chunks));
in
  fun renderChunks indent chunks =
      {indent = indent,
       line = String.concat (flatten [] (rev chunks))};
end;

fun renderChunk indent chunk = renderChunks indent [chunk];

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

(*BasicDebug
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
*)

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

  fun executeAddString lineLength (s,n) lines state =
      let
        val State {blocks,lineIndent,lineSize} = state

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
        val (lines,state) =
            executeAddString lineLength emptyStringSize lines state

        val (lines,state) =
            executeBigBreak lineLength lines state
      in
        executeAddString lineLength emptyStringSize lines state
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
              raise Bug ("Print.advance: after " ^ stepToString step ^
                         " command:\n" ^ bug)
*)
      in
        revConcat o Stream.maps advance (final lineLength []) initialState
      end;
end;

(* ------------------------------------------------------------------------- *)
(* Pretty-printer combinators.                                               *)
(* ------------------------------------------------------------------------- *)

type 'a pp = 'a -> ppstream;

fun ppMap f ppB a : ppstream = ppB (f a);

fun ppBracket' l r ppA a =
    let
      val (_,n) = l
    in
      blockProgram Inconsistent n
        [addString l,
         ppA a,
         addString r]
    end;

fun ppOp' s = sequence (addString s) (addBreak 1);

fun ppOp2' ab ppA ppB (a,b) =
    blockProgram Inconsistent 0
      [ppA a,
       ppOp' ab,
       ppB b];

fun ppOp3' ab bc ppA ppB ppC (a,b,c) =
    blockProgram Inconsistent 0
      [ppA a,
       ppOp' ab,
       ppB b,
       ppOp' bc,
       ppC c];

fun ppOpList' s ppA =
    let
      fun ppOpA a = sequence (ppOp' s) (ppA a)
    in
      fn [] => skip
       | h :: t => blockProgram Inconsistent 0 (ppA h :: map ppOpA t)
    end;

fun ppOpStream' s ppA =
    let
      fun ppOpA a = sequence (ppOp' s) (ppA a)
    in
      fn Stream.Nil => skip
       | Stream.Cons (h,t) =>
         blockProgram Inconsistent 0
           [ppA h,
            Stream.concat (Stream.map ppOpA (t ()))]
    end;

fun ppBracket l r = ppBracket' (mkStringSize l) (mkStringSize r);

fun ppOp s = ppOp' (mkStringSize s);

fun ppOp2 ab = ppOp2' (mkStringSize ab);

fun ppOp3 ab bc = ppOp3' (mkStringSize ab) (mkStringSize bc);

fun ppOpList s = ppOpList' (mkStringSize s);

fun ppOpStream s = ppOpStream' (mkStringSize s);

(* ------------------------------------------------------------------------- *)
(* Pretty-printers for common types.                                         *)
(* ------------------------------------------------------------------------- *)

fun ppChar c = addString (str c, 1);

fun ppString s = addString (mkStringSize s);

fun ppEscapeString escape = ppMap (escapeString escape) ppString;

local
  val pp = ppString "()";
in
  fun ppUnit () = pp;
end;

local
  val ppTrue = ppString "true"
  and ppFalse = ppString "false";
in
  fun ppBool b = if b then ppTrue else ppFalse;
end;

val ppInt = ppMap Int.toString ppString;

local
  val ppNeg = ppString "~"
  and ppSep = ppString ","
  and ppZero = ppString "0"
  and ppZeroZero = ppString "00";

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

val ppReal = ppMap Real.toString ppString;

val ppPercent = ppMap percentToString ppString;

local
  val ppLess = ppString "Less"
  and ppEqual = ppString "Equal"
  and ppGreater = ppString "Greater";
in
  fun ppOrder ord =
      case ord of
        LESS => ppLess
      | EQUAL => ppEqual
      | GREATER => ppGreater;
end;

local
  val left = mkStringSize "["
  and right = mkStringSize "]"
  and sep = mkStringSize ",";
in
  fun ppList ppX xs = ppBracket' left right (ppOpList' sep ppX) xs;

  fun ppStream ppX xs = ppBracket' left right (ppOpStream' sep ppX) xs;
end;

local
  val ppNone = ppString "-";
in
  fun ppOption ppX xo =
      case xo of
        SOME x => ppX x
      | NONE => ppNone;
end;

local
  val left = mkStringSize "("
  and right = mkStringSize ")"
  and sep = mkStringSize ",";
in
  fun ppPair ppA ppB =
      ppBracket' left right (ppOp2' sep ppA ppB);

  fun ppTriple ppA ppB ppC =
      ppBracket' left right (ppOp3' sep sep ppA ppB ppC);
end;

val ppBreakStyle = ppMap breakStyleToString ppString;

val ppStep = ppMap stepToString ppString;

val ppStringSize =
    let
      val left = mkStringSize "\""
      and right = mkStringSize "\""
      and escape = {escape = [#"\""]}

      val pp = ppBracket' left right (ppEscapeString escape)
    in
      fn (s,n) => if size s = n then pp s else ppPair pp ppInt (s,n)
    end;

fun ppStep step =
    blockProgram Inconsistent 2
      (ppStep step ::
       (case step of
          BeginBlock style_indent =>
            [addBreak 1,
             ppPair ppBreakStyle ppInt style_indent]
        | EndBlock => []
        | AddString s =>
            [addBreak 1,
             ppStringSize s]
        | AddBreak n =>
            [addBreak 1,
             ppInt n]
        | AddNewline => []));

val ppPpstream = ppStream ppStep;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing infix operators.                                          *)
(* ------------------------------------------------------------------------- *)

type token = string;

datatype assoc =
    LeftAssoc
  | NonAssoc
  | RightAssoc;

datatype infixes =
    Infixes of
      {token : token,
       precedence : int,
       assoc : assoc} list;

local
  fun comparePrecedence (io1,io2) =
      let
        val {token = _, precedence = p1, assoc = _} = io1
        and {token = _, precedence = p2, assoc = _} = io2
      in
        Int.compare (p2,p1)
      end;

  fun equalAssoc a a' =
      case a of
        LeftAssoc => (case a' of LeftAssoc => true | _ => false)
      | NonAssoc => (case a' of NonAssoc => true | _ => false)
      | RightAssoc => (case a' of RightAssoc => true | _ => false);

  fun new t a acc = {tokens = StringSet.singleton t, assoc = a} :: acc;

  fun add t a' acc =
      case acc of
        [] => raise Bug "Print.layerInfixes: null"
      | {tokens = ts, assoc = a} :: acc =>
        if equalAssoc a a' then {tokens = StringSet.add ts t, assoc = a} :: acc
        else raise Bug "Print.layerInfixes: mixed assocs";

  fun layer ({token = t, precedence = p, assoc = a}, (acc,p')) =
      let
        val acc = if p = p' then add t a acc else new t a acc
      in
        (acc,p)
      end;
in
  fun layerInfixes (Infixes ios) =
      case sort comparePrecedence ios of
        [] => []
      | {token = t, precedence = p, assoc = a} :: ios =>
        let
          val acc = new t a []

          val (acc,_) = List.foldl layer (acc,p) ios
        in
          acc
        end;
end;

local
  fun add ({tokens = ts, assoc = _}, tokens) = StringSet.union ts tokens;
in
  fun tokensLayeredInfixes l = List.foldl add StringSet.empty l;
end;

fun tokensInfixes ios = tokensLayeredInfixes (layerInfixes ios);

fun destInfixOp dest tokens tm =
    case dest tm of
      NONE => NONE
    | s as SOME (t,a,b) => if StringSet.member t tokens then s else NONE;

fun ppLayeredInfixes dest ppTok {tokens,assoc} ppLower ppSub =
    let
      fun isLayer t = StringSet.member t tokens

      fun ppTerm aligned (tm,r) =
          case dest tm of
            NONE => ppSub (tm,r)
          | SOME (t,a,b) =>
            if aligned andalso isLayer t then ppLayer (tm,t,a,b,r)
            else ppLower (tm,t,a,b,r)

      and ppLeft tm_r =
          let
            val aligned = case assoc of LeftAssoc => true | _ => false
          in
            ppTerm aligned tm_r
          end

      and ppLayer (tm,t,a,b,r) =
          program
            [ppLeft (a,true),
             ppTok (tm,t),
             ppRight (b,r)]

      and ppRight tm_r =
          let
            val aligned = case assoc of RightAssoc => true | _ => false
          in
            ppTerm aligned tm_r
          end
    in
      fn tm_t_a_b_r as (_,t,_,_,_) =>
         if isLayer t then block Inconsistent 0 (ppLayer tm_t_a_b_r)
         else ppLower tm_t_a_b_r
    end;

local
  val leftBrack = mkStringSize "("
  and rightBrack = mkStringSize ")";
in
  fun ppInfixes ops =
      let
        val layers = layerInfixes ops

        val toks = tokensLayeredInfixes layers
      in
        fn dest => fn ppTok => fn ppSub =>
           let
             fun destOp tm = destInfixOp dest toks tm

             fun ppInfix tm_t_a_b_r = ppLayers layers tm_t_a_b_r

             and ppLayers ls (tm,t,a,b,r) =
                 case ls of
                   [] =>
                   ppBracket' leftBrack rightBrack ppInfix (tm,t,a,b,false)
                 | l :: ls =>
                   let
                     val ppLower = ppLayers ls
                   in
                     ppLayeredInfixes destOp ppTok l ppLower ppSub (tm,t,a,b,r)
                   end
           in
             fn (tm,r) =>
                case destOp tm of
                  SOME (t,a,b) => ppInfix (tm,t,a,b,r)
                | NONE => ppSub (tm,r)
           end
      end;
end;

(* ------------------------------------------------------------------------- *)
(* Executing pretty-printers with a global line length.                      *)
(* ------------------------------------------------------------------------- *)

val lineLength = ref initialLineLength;

fun toStream ppA a =
    Stream.map (fn {indent,line} => nSpaces indent ^ line ^ "\n")
      (execute {lineLength = !lineLength} (ppA a));

local
  fun inc {indent,line} acc = line :: nSpaces indent :: acc;

  fun incn (indent_line,acc) = inc indent_line ("\n" :: acc);
in
  fun toString ppA a =
      case execute {lineLength = !lineLength} (ppA a) of
        Stream.Nil => ""
      | Stream.Cons (h,t) =>
        let
          val lines = Stream.foldl incn (inc h []) (t ())
        in
          String.concat (rev lines)
        end;
end;

local
  val sep = mkStringSize " =";
in
  fun trace ppX nameX x =
      Useful.trace (toString (ppOp2' sep ppString ppX) (nameX,x) ^ "\n");
end;

end

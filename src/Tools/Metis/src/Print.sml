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
    | Stream.Cons (h,t) => revAppend h (fn () => revConcat (t ()));

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
      val escapeMap = List.map (fn c => (c, "\\" ^ str c)) escape

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
(* Pretty-printing blocks.                                                   *)
(* ------------------------------------------------------------------------- *)

datatype style = Consistent | Inconsistent;

datatype block =
    Block of
      {style : style,
       indent : int};

fun toStringStyle style =
    case style of
      Consistent => "Consistent"
    | Inconsistent => "Inconsistent";

fun isConsistentStyle style =
    case style of
      Consistent => true
    | Inconsistent => false;

fun isInconsistentStyle style =
    case style of
      Inconsistent => true
    | Consistent => false;

fun mkBlock style indent =
    Block
      {style = style,
       indent = indent};

val mkConsistentBlock = mkBlock Consistent;

val mkInconsistentBlock = mkBlock Inconsistent;

fun styleBlock (Block {style = x, ...}) = x;

fun indentBlock (Block {indent = x, ...}) = x;

fun isConsistentBlock block = isConsistentStyle (styleBlock block);

fun isInconsistentBlock block = isInconsistentStyle (styleBlock block);

(* ------------------------------------------------------------------------- *)
(* Words are unbreakable strings annotated with their effective size.        *)
(* ------------------------------------------------------------------------- *)

datatype word = Word of {word : string, size : int};

fun mkWord s = Word {word = s, size = String.size s};

val emptyWord = mkWord "";

fun charWord c = mkWord (str c);

fun spacesWord i = Word {word = nSpaces i, size = i};

fun sizeWord (Word {size = x, ...}) = x;

fun renderWord (Word {word = x, ...}) = x;

(* ------------------------------------------------------------------------- *)
(* Possible line breaks.                                                     *)
(* ------------------------------------------------------------------------- *)

datatype break = Break of {size : int, extraIndent : int};

fun mkBreak n = Break {size = n, extraIndent = 0};

fun sizeBreak (Break {size = x, ...}) = x;

fun extraIndentBreak (Break {extraIndent = x, ...}) = x;

fun renderBreak b = nSpaces (sizeBreak b);

fun updateSizeBreak size break =
    let
      val Break {size = _, extraIndent} = break
    in
      Break
        {size = size,
         extraIndent = extraIndent}
    end;

fun appendBreak break1 break2 =
    let
(*BasicDebug
      val () = warn "merging consecutive pretty-printing breaks"
*)
      val Break {size = size1, extraIndent = extraIndent1} = break1
      and Break {size = size2, extraIndent = extraIndent2} = break2

      val size = size1 + size2
      and extraIndent = Int.max (extraIndent1,extraIndent2)
    in
      Break
        {size = size,
         extraIndent = extraIndent}
    end;

(* ------------------------------------------------------------------------- *)
(* A type of pretty-printers.                                                *)
(* ------------------------------------------------------------------------- *)

datatype step =
    BeginBlock of block
  | EndBlock
  | AddWord of word
  | AddBreak of break
  | AddNewline;

type ppstream = step Stream.stream;

type 'a pp = 'a -> ppstream;

fun toStringStep step =
    case step of
      BeginBlock _ => "BeginBlock"
    | EndBlock => "EndBlock"
    | AddWord _ => "Word"
    | AddBreak _ => "Break"
    | AddNewline => "Newline";

val skip : ppstream = Stream.Nil;

fun sequence pp1 pp2 : ppstream = Stream.append pp1 (K pp2);

local
  fun dup pp n () = if n = 1 then pp else Stream.append pp (dup pp (n - 1));
in
  fun duplicate n pp : ppstream =
      let
(*BasicDebug
        val () = if 0 <= n then () else raise Bug "Print.duplicate"
*)
      in
        if n = 0 then skip else dup pp n ()
      end;
end;

val program : ppstream list -> ppstream = Stream.concatList;

val stream : ppstream Stream.stream -> ppstream = Stream.concat;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing blocks.                                                   *)
(* ------------------------------------------------------------------------- *)

local
  fun beginBlock b = Stream.singleton (BeginBlock b);

  val endBlock = Stream.singleton EndBlock;
in
  fun block b pp = program [beginBlock b, pp, endBlock];
end;

fun consistentBlock i pps = block (mkConsistentBlock i) (program pps);

fun inconsistentBlock i pps = block (mkInconsistentBlock i) (program pps);

(* ------------------------------------------------------------------------- *)
(* Words are unbreakable strings annotated with their effective size.        *)
(* ------------------------------------------------------------------------- *)

fun ppWord w = Stream.singleton (AddWord w);

val space = ppWord (mkWord " ");

fun spaces i = ppWord (spacesWord i);

(* ------------------------------------------------------------------------- *)
(* Possible line breaks.                                                     *)
(* ------------------------------------------------------------------------- *)

fun ppBreak b = Stream.singleton (AddBreak b);

fun breaks i = ppBreak (mkBreak i);

val break = breaks 1;

(* ------------------------------------------------------------------------- *)
(* Forced line breaks.                                                       *)
(* ------------------------------------------------------------------------- *)

val newline = Stream.singleton AddNewline;

fun newlines i = duplicate i newline;

(* ------------------------------------------------------------------------- *)
(* Pretty-printer combinators.                                               *)
(* ------------------------------------------------------------------------- *)

fun ppMap f ppB a : ppstream = ppB (f a);

fun ppBracket' l r ppA a =
    let
      val n = sizeWord l
    in
      inconsistentBlock n
        [ppWord l,
         ppA a,
         ppWord r]
    end;

fun ppOp' w = sequence (ppWord w) break;

fun ppOp2' ab ppA ppB (a,b) =
    inconsistentBlock 0
      [ppA a,
       ppOp' ab,
       ppB b];

fun ppOp3' ab bc ppA ppB ppC (a,b,c) =
    inconsistentBlock 0
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
       | h :: t => inconsistentBlock 0 (ppA h :: List.map ppOpA t)
    end;

fun ppOpStream' s ppA =
    let
      fun ppOpA a = sequence (ppOp' s) (ppA a)
    in
      fn Stream.Nil => skip
       | Stream.Cons (h,t) =>
         inconsistentBlock 0
           [ppA h,
            Stream.concat (Stream.map ppOpA (t ()))]
    end;

fun ppBracket l r = ppBracket' (mkWord l) (mkWord r);

fun ppOp s = ppOp' (mkWord s);

fun ppOp2 ab = ppOp2' (mkWord ab);

fun ppOp3 ab bc = ppOp3' (mkWord ab) (mkWord bc);

fun ppOpList s = ppOpList' (mkWord s);

fun ppOpStream s = ppOpStream' (mkWord s);

(* ------------------------------------------------------------------------- *)
(* Pretty-printers for common types.                                         *)
(* ------------------------------------------------------------------------- *)

fun ppChar c = ppWord (charWord c);

fun ppString s = ppWord (mkWord s);

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
  val left = mkWord "["
  and right = mkWord "]"
  and sep = mkWord ",";
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
  val left = mkWord "("
  and right = mkWord ")"
  and sep = mkWord ",";
in
  fun ppPair ppA ppB =
      ppBracket' left right (ppOp2' sep ppA ppB);

  fun ppTriple ppA ppB ppC =
      ppBracket' left right (ppOp3' sep sep ppA ppB ppC);
end;

fun ppException e = ppString (exnMessage e);

(* ------------------------------------------------------------------------- *)
(* A type of pretty-printers.                                                *)
(* ------------------------------------------------------------------------- *)

local
  val ppStepType = ppMap toStringStep ppString;

  val ppStyle = ppMap toStringStyle ppString;

  val ppBlockInfo =
      let
        val sep = mkWord " "
      in
        fn Block {style = s, indent = i} =>
           program [ppStyle s, ppWord sep, ppInt i]
      end;

  val ppWordInfo =
      let
        val left = mkWord "\""
        and right = mkWord "\""
        and escape = {escape = [#"\""]}

        val pp = ppBracket' left right (ppEscapeString escape)
      in
        fn Word {word = s, size = n} =>
           if size s = n then pp s else ppPair pp ppInt (s,n)
      end;

  val ppBreakInfo =
      let
        val sep = mkWord "+"
      in
        fn Break {size = n, extraIndent = k} =>
           if k = 0 then ppInt n else program [ppInt n, ppWord sep, ppInt k]
      end;

  fun ppStep step =
      inconsistentBlock 2
        (ppStepType step ::
         (case step of
            BeginBlock b =>
              [break,
               ppBlockInfo b]
          | EndBlock => []
          | AddWord w =>
              [break,
               ppWordInfo w]
          | AddBreak b =>
              [break,
               ppBreakInfo b]
          | AddNewline => []));
in
  val ppPpstream = ppStream ppStep;
end;

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
         if isLayer t then inconsistentBlock 0 [ppLayer tm_t_a_b_r]
         else ppLower tm_t_a_b_r
    end;

local
  val leftBrack = mkWord "("
  and rightBrack = mkWord ")";
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
(* A type of output lines.                                                   *)
(* ------------------------------------------------------------------------- *)

type line = {indent : int, line : string};

val emptyLine =
    let
      val indent = 0
      and line = ""
    in
      {indent = indent,
       line = line}
    end;

fun addEmptyLine lines = emptyLine :: lines;

fun addLine lines indent line = {indent = indent, line = line} :: lines;

(* ------------------------------------------------------------------------- *)
(* Pretty-printer rendering.                                                 *)
(* ------------------------------------------------------------------------- *)

datatype chunk =
    WordChunk of word
  | BreakChunk of break
  | FrameChunk of frame

and frame =
    Frame of
      {block : block,
       broken : bool,
       indent : int,
       size : int,
       chunks : chunk list};

datatype state =
    State of
      {lineIndent : int,
       lineSize : int,
       stack : frame list};

fun blockFrame (Frame {block = x, ...}) = x;

fun brokenFrame (Frame {broken = x, ...}) = x;

fun indentFrame (Frame {indent = x, ...}) = x;

fun sizeFrame (Frame {size = x, ...}) = x;

fun chunksFrame (Frame {chunks = x, ...}) = x;

fun styleFrame frame = styleBlock (blockFrame frame);

fun isConsistentFrame frame = isConsistentBlock (blockFrame frame);

fun breakingFrame frame = isConsistentFrame frame andalso brokenFrame frame;

fun sizeChunk chunk =
    case chunk of
      WordChunk w => sizeWord w
    | BreakChunk b => sizeBreak b
    | FrameChunk f => sizeFrame f;

local
  fun add (c,acc) = sizeChunk c + acc;
in
  fun sizeChunks cs = List.foldl add 0 cs;
end;

local
  fun flattenChunks acc chunks =
      case chunks of
        [] => acc
      | chunk :: chunks => flattenChunk acc chunk chunks

  and flattenChunk acc chunk chunks =
      case chunk of
        WordChunk w => flattenChunks (renderWord w :: acc) chunks
      | BreakChunk b => flattenChunks (renderBreak b :: acc) chunks
      | FrameChunk f => flattenFrame acc f chunks

  and flattenFrame acc frame chunks =
      flattenChunks acc (chunksFrame frame @ chunks);
in
  fun renderChunks chunks = String.concat (flattenChunks [] chunks);
end;

fun addChunksLine lines indent chunks =
    addLine lines indent (renderChunks chunks);

local
  fun add baseIndent ((extraIndent,chunks),lines) =
      addChunksLine lines (baseIndent + extraIndent) chunks;
in
  fun addIndentChunksLines lines baseIndent indent_chunks =
      List.foldl (add baseIndent) lines indent_chunks;
end;

fun isEmptyFrame frame =
    let
      val chunks = chunksFrame frame

      val empty = List.null chunks

(*BasicDebug
      val () =
          if not empty orelse sizeFrame frame = 0 then ()
          else raise Bug "Print.isEmptyFrame: bad size"
*)
    in
      empty
    end;

local
  fun breakInconsistent blockIndent =
      let
        fun break chunks =
            case chunks of
              [] => NONE
            | chunk :: chunks =>
              case chunk of
                BreakChunk b =>
                let
                  val pre = chunks
                  and indent = blockIndent + extraIndentBreak b
                  and post = []
                in
                  SOME (pre,indent,post)
                end
              | _ =>
                case break chunks of
                  SOME (pre,indent,post) =>
                  let
                    val post = chunk :: post
                  in
                    SOME (pre,indent,post)
                  end
                | NONE => NONE
      in
        break
      end;

  fun breakConsistent blockIndent =
      let
        fun break indent_chunks chunks =
            case breakInconsistent blockIndent chunks of
              NONE => (chunks,indent_chunks)
            | SOME (pre,indent,post) =>
              break ((indent,post) :: indent_chunks) pre
      in
        break []
      end;
in
  fun breakFrame frame =
      let
        val Frame
              {block,
               broken = _,
               indent = _,
               size = _,
               chunks} = frame

        val blockIndent = indentBlock block
      in
        case breakInconsistent blockIndent chunks of
          NONE => NONE
        | SOME (pre,indent,post) =>
          let
            val broken = true
            and size = sizeChunks post

            val frame =
                Frame
                  {block = block,
                   broken = broken,
                   indent = indent,
                   size = size,
                   chunks = post}
          in
            case styleBlock block of
              Inconsistent =>
              let
                val indent_chunks = []
              in
                SOME (pre,indent_chunks,frame)
              end
            | Consistent =>
              let
                val (pre,indent_chunks) = breakConsistent blockIndent pre
              in
                SOME (pre,indent_chunks,frame)
              end
          end
      end;
end;

fun removeChunksFrame frame =
    let
      val Frame
            {block,
             broken,
             indent,
             size = _,
             chunks} = frame
    in
      if broken andalso List.null chunks then NONE
      else
        let
          val frame =
              Frame
                {block = block,
                 broken = true,
                 indent = indent,
                 size = 0,
                 chunks = []}
        in
          SOME (chunks,frame)
        end
    end;

val removeChunksFrames =
    let
      fun remove frames =
          case frames of
            [] =>
            let
              val chunks = []
              and frames = NONE
              and indent = 0
            in
              (chunks,frames,indent)
            end
          | top :: rest =>
            let
              val (chunks,rest',indent) = remove rest

              val indent = indent + indentFrame top

              val (chunks,top') =
                  case removeChunksFrame top of
                    NONE => (chunks,NONE)
                  | SOME (topChunks,top) => (topChunks @ chunks, SOME top)

              val frames' =
                  case (top',rest') of
                    (NONE,NONE) => NONE
                  | (SOME top, NONE) => SOME (top :: rest)
                  | (NONE, SOME rest) => SOME (top :: rest)
                  | (SOME top, SOME rest) => SOME (top :: rest)
            in
              (chunks,frames',indent)
            end
    in
      fn frames =>
         let
           val (chunks,frames',indent) = remove frames

           val frames = Option.getOpt (frames',frames)
         in
           (chunks,frames,indent)
         end
    end;

local
  fun breakUp lines lineIndent frames =
      case frames of
        [] => NONE
      | frame :: frames =>
        case breakUp lines lineIndent frames of
          SOME (lines_indent,lineSize,frames) =>
          let
            val lineSize = lineSize + sizeFrame frame
            and frames = frame :: frames
          in
            SOME (lines_indent,lineSize,frames)
          end
        | NONE =>
          case breakFrame frame of
            NONE => NONE
          | SOME (frameChunks,indent_chunks,frame) =>
            let
              val (chunks,frames,indent) = removeChunksFrames frames

              val chunks = frameChunks @ chunks

              val lines = addChunksLine lines lineIndent chunks

              val lines = addIndentChunksLines lines indent indent_chunks

              val lineIndent = indent + indentFrame frame

              val lineSize = sizeFrame frame

              val frames = frame :: frames
            in
              SOME ((lines,lineIndent),lineSize,frames)
            end;

  fun breakInsideChunk chunk =
      case chunk of
        WordChunk _ => NONE
      | BreakChunk _ => raise Bug "Print.breakInsideChunk"
      | FrameChunk frame =>
        case breakFrame frame of
          SOME (pathChunks,indent_chunks,frame) =>
          let
            val pathIndent = 0
            and breakIndent = indentFrame frame
          in
            SOME (pathChunks,pathIndent,indent_chunks,breakIndent,frame)
          end
        | NONE => breakInsideFrame frame

  and breakInsideChunks chunks =
      case chunks of
        [] => NONE
      | chunk :: chunks =>
        case breakInsideChunk chunk of
          SOME (pathChunks,pathIndent,indent_chunks,breakIndent,frame) =>
          let
            val pathChunks = pathChunks @ chunks
            and chunks = [FrameChunk frame]
          in
            SOME (pathChunks,pathIndent,indent_chunks,breakIndent,chunks)
          end
        | NONE =>
          case breakInsideChunks chunks of
            SOME (pathChunks,pathIndent,indent_chunks,breakIndent,chunks) =>
            let
              val chunks = chunk :: chunks
            in
              SOME (pathChunks,pathIndent,indent_chunks,breakIndent,chunks)
            end
          | NONE => NONE

  and breakInsideFrame frame =
      let
        val Frame
              {block,
               broken = _,
               indent,
               size = _,
               chunks} = frame
      in
        case breakInsideChunks chunks of
          SOME (pathChunks,pathIndent,indent_chunks,breakIndent,chunks) =>
          let
            val pathIndent = pathIndent + indent
            and broken = true
            and size = sizeChunks chunks

            val frame =
                Frame
                  {block = block,
                   broken = broken,
                   indent = indent,
                   size = size,
                   chunks = chunks}
          in
            SOME (pathChunks,pathIndent,indent_chunks,breakIndent,frame)
          end
        | NONE => NONE
      end;

  fun breakInside lines lineIndent frames =
      case frames of
        [] => NONE
      | frame :: frames =>
        case breakInsideFrame frame of
          SOME (pathChunks,pathIndent,indent_chunks,breakIndent,frame) =>
          let
            val (chunks,frames,indent) = removeChunksFrames frames

            val chunks = pathChunks @ chunks
            and indent = indent + pathIndent

            val lines = addChunksLine lines lineIndent chunks

            val lines = addIndentChunksLines lines indent indent_chunks

            val lineIndent = indent + breakIndent

            val lineSize = sizeFrame frame

            val frames = frame :: frames
          in
            SOME ((lines,lineIndent),lineSize,frames)
          end
        | NONE =>
          case breakInside lines lineIndent frames of
            SOME (lines_indent,lineSize,frames) =>
            let
              val lineSize = lineSize + sizeFrame frame
              and frames = frame :: frames
            in
              SOME (lines_indent,lineSize,frames)
            end
          | NONE => NONE;
in
  fun breakFrames lines lineIndent frames =
      case breakUp lines lineIndent frames of
        SOME ((lines,lineIndent),lineSize,frames) =>
        SOME (lines,lineIndent,lineSize,frames)
      | NONE =>
        case breakInside lines lineIndent frames of
          SOME ((lines,lineIndent),lineSize,frames) =>
          SOME (lines,lineIndent,lineSize,frames)
        | NONE => NONE;
end;

(*BasicDebug
fun checkChunk chunk =
    case chunk of
      WordChunk t => (false, sizeWord t)
    | BreakChunk b => (false, sizeBreak b)
    | FrameChunk b => checkFrame b

and checkChunks chunks =
    case chunks of
      [] => (false,0)
    | chunk :: chunks =>
      let
        val (bk,sz) = checkChunk chunk

        val (bk',sz') = checkChunks chunks
      in
        (bk orelse bk', sz + sz')
      end

and checkFrame frame =
    let
      val Frame
            {block = _,
             broken,
             indent = _,
             size,
             chunks} = frame

      val (bk,sz) = checkChunks chunks

      val () =
          if size = sz then ()
          else raise Bug "Print.checkFrame: wrong size"

      val () =
          if broken orelse not bk then ()
          else raise Bug "Print.checkFrame: deep broken frame"
    in
      (broken,size)
    end;

fun checkFrames frames =
    case frames of
      [] => (true,0)
    | frame :: frames =>
      let
        val (bk,sz) = checkFrame frame

        val (bk',sz') = checkFrames frames

        val () =
            if bk' orelse not bk then ()
            else raise Bug "Print.checkFrame: broken stack frame"
      in
        (bk, sz + sz')
      end;
*)

(*BasicDebug
fun checkState state =
    (let
       val State {lineIndent,lineSize,stack} = state

       val () =
           if not (List.null stack) then ()
           else raise Error "no stack"

       val (_,sz) = checkFrames stack

       val () =
           if lineSize = sz then ()
           else raise Error "wrong lineSize"
     in
       ()
     end
     handle Error err => raise Bug err)
    handle Bug bug => raise Bug ("Print.checkState: " ^ bug);
*)

fun isEmptyState state =
    let
      val State {lineSize,stack,...} = state
    in
      lineSize = 0 andalso List.all isEmptyFrame stack
    end;

fun isFinalState state =
    let
      val State {stack,...} = state
    in
      case stack of
        [] => raise Bug "Print.isFinalState: empty stack"
      | [frame] => isEmptyFrame frame
      | _ :: _ :: _ => false
    end;

local
  val initialBlock =
      let
        val indent = 0
        and style = Inconsistent
      in
        Block
          {indent = indent,
           style = style}
      end;

  val initialFrame =
      let
        val block = initialBlock
        and broken = false
        and indent = 0
        and size = 0
        and chunks = []
      in
        Frame
          {block = block,
           broken = broken,
           indent = indent,
           size = size,
           chunks = chunks}
      end;
in
  val initialState =
      let
        val lineIndent = 0
        and lineSize = 0
        and stack = [initialFrame]
      in
        State
          {lineIndent = lineIndent,
           lineSize = lineSize,
           stack = stack}
      end;
end;

fun normalizeState lineLength lines state =
    let
      val State {lineIndent,lineSize,stack} = state

      val within =
          case lineLength of
            NONE => true
          | SOME len => lineIndent + lineSize <= len
    in
      if within then (lines,state)
      else
        case breakFrames lines lineIndent stack of
          NONE => (lines,state)
        | SOME (lines,lineIndent,lineSize,stack) =>
          let
(*BasicDebug
            val () = checkState state
*)
            val state =
                State
                  {lineIndent = lineIndent,
                   lineSize = lineSize,
                   stack = stack}
          in
            normalizeState lineLength lines state
          end
    end
(*BasicDebug
    handle Bug bug => raise Bug ("Print.normalizeState:\n" ^ bug)
*)

local
  fun executeBeginBlock block lines state =
      let
        val State {lineIndent,lineSize,stack} = state

        val broken = false
        and indent = indentBlock block
        and size = 0
        and chunks = []

        val frame =
            Frame
              {block = block,
               broken = broken,
               indent = indent,
               size = size,
               chunks = chunks}

        val stack = frame :: stack

        val state =
            State
              {lineIndent = lineIndent,
               lineSize = lineSize,
               stack = stack}
      in
        (lines,state)
      end;

  fun executeEndBlock lines state =
      let
        val State {lineIndent,lineSize,stack} = state

        val (lineSize,stack) =
            case stack of
              [] => raise Bug "Print.executeEndBlock: empty stack"
            | topFrame :: stack =>
              let
                val Frame
                      {block = topBlock,
                       broken = topBroken,
                       indent = topIndent,
                       size = topSize,
                       chunks = topChunks} = topFrame

                val (lineSize,topSize,topChunks,topFrame) =
                    case topChunks of
                      BreakChunk break :: chunks =>
                      let
(*BasicDebug
                        val () =
                            let
                              val mesg =
                                  "ignoring a break at the end of a " ^
                                  "pretty-printing block"
                            in
                              warn mesg
                            end
*)
                        val n = sizeBreak break

                        val lineSize = lineSize - n
                        and topSize = topSize - n
                        and topChunks = chunks

                        val topFrame =
                            Frame
                              {block = topBlock,
                               broken = topBroken,
                               indent = topIndent,
                               size = topSize,
                               chunks = topChunks}
                      in
                        (lineSize,topSize,topChunks,topFrame)
                      end
                    | _ => (lineSize,topSize,topChunks,topFrame)
              in
                if List.null topChunks then (lineSize,stack)
                else
                  case stack of
                    [] => raise Error "Print.execute: too many end blocks"
                  | frame :: stack =>
                    let
                      val Frame
                            {block,
                             broken,
                             indent,
                             size,
                             chunks} = frame

                      val size = size + topSize

                      val chunk = FrameChunk topFrame

                      val chunks = chunk :: chunks

                      val frame =
                          Frame
                            {block = block,
                             broken = broken,
                             indent = indent,
                             size = size,
                             chunks = chunks}

                      val stack = frame :: stack
                    in
                      (lineSize,stack)
                    end
              end

        val state =
            State
              {lineIndent = lineIndent,
               lineSize = lineSize,
               stack = stack}
      in
        (lines,state)
      end;

  fun executeAddWord lineLength word lines state =
      let
        val State {lineIndent,lineSize,stack} = state

        val n = sizeWord word

        val lineSize = lineSize + n

        val stack =
            case stack of
              [] => raise Bug "Print.executeAddWord: empty stack"
            | frame :: stack =>
              let
                val Frame
                      {block,
                       broken,
                       indent,
                       size,
                       chunks} = frame

                val size = size + n

                val chunk = WordChunk word

                val chunks = chunk :: chunks

                val frame =
                    Frame
                      {block = block,
                       broken = broken,
                       indent = indent,
                       size = size,
                       chunks = chunks}

                val stack = frame :: stack
              in
                stack
              end

        val state =
            State
              {lineIndent = lineIndent,
               lineSize = lineSize,
               stack = stack}
      in
        normalizeState lineLength lines state
      end;

  fun executeAddBreak lineLength break lines state =
      let
        val State {lineIndent,lineSize,stack} = state

        val (topFrame,restFrames) =
            case stack of
              [] => raise Bug "Print.executeAddBreak: empty stack"
            | topFrame :: restFrames => (topFrame,restFrames)

        val Frame
              {block = topBlock,
               broken = topBroken,
               indent = topIndent,
               size = topSize,
               chunks = topChunks} = topFrame
      in
        case topChunks of
          [] => (lines,state)
        | topChunk :: restTopChunks =>
          let
            val (topChunks,n) =
                case topChunk of
                  BreakChunk break' =>
                  let
                    val break = appendBreak break' break

                    val chunk = BreakChunk break

                    val topChunks = chunk :: restTopChunks
                    and n = sizeBreak break - sizeBreak break'
                  in
                    (topChunks,n)
                  end
                | _ =>
                  let
                    val chunk = BreakChunk break

                    val topChunks = chunk :: topChunks
                    and n = sizeBreak break
                  in
                    (topChunks,n)
                  end

            val lineSize = lineSize + n

            val topSize = topSize + n

            val topFrame =
                Frame
                  {block = topBlock,
                   broken = topBroken,
                   indent = topIndent,
                   size = topSize,
                   chunks = topChunks}

            val stack = topFrame :: restFrames

            val state =
                State
                  {lineIndent = lineIndent,
                   lineSize = lineSize,
                   stack = stack}

            val lineLength =
                if breakingFrame topFrame then SOME ~1 else lineLength
          in
            normalizeState lineLength lines state
          end
      end;

  fun executeBigBreak lines state =
      let
        val lineLength = SOME ~1
        and break = mkBreak 0
      in
        executeAddBreak lineLength break lines state
      end;

  fun executeAddNewline lineLength lines state =
      if isEmptyState state then (addEmptyLine lines, state)
      else executeBigBreak lines state;

  fun executeEof lineLength lines state =
      if isFinalState state then (lines,state)
      else
        let
          val (lines,state) = executeBigBreak lines state

(*BasicDebug
          val () =
              if isFinalState state then ()
              else raise Bug "Print.executeEof: not a final state"
*)
        in
          (lines,state)
        end;
in
  fun render {lineLength} =
      let
        fun execute step state =
            let
              val lines = []
            in
              case step of
                BeginBlock block => executeBeginBlock block lines state
              | EndBlock => executeEndBlock lines state
              | AddWord word => executeAddWord lineLength word lines state
              | AddBreak break => executeAddBreak lineLength break lines state
              | AddNewline => executeAddNewline lineLength lines state
            end

(*BasicDebug
        val execute = fn step => fn state =>
            let
              val (lines,state) = execute step state

              val () = checkState state
            in
              (lines,state)
            end
            handle Bug bug =>
              raise Bug ("Print.execute: after " ^ toStringStep step ^
                         " command:\n" ^ bug)
*)

        fun final state =
            let
              val lines = []

              val (lines,state) = executeEof lineLength lines state

(*BasicDebug
              val () = checkState state
*)
            in
              if List.null lines then Stream.Nil else Stream.singleton lines
            end
(*BasicDebug
            handle Bug bug => raise Bug ("Print.final: " ^ bug)
*)
      in
        fn pps =>
           let
             val lines = Stream.maps execute final initialState pps
           in
             revConcat lines
           end
      end;
end;

local
  fun inc {indent,line} acc = line :: nSpaces indent :: acc;

  fun incn (indent_line,acc) = inc indent_line ("\n" :: acc);
in
  fun toStringWithLineLength len ppA a =
      case render len (ppA a) of
        Stream.Nil => ""
      | Stream.Cons (h,t) =>
        let
          val lines = Stream.foldl incn (inc h []) (t ())
        in
          String.concat (List.rev lines)
        end;
end;

local
  fun renderLine {indent,line} = nSpaces indent ^ line ^ "\n";
in
  fun toStreamWithLineLength len ppA a =
      Stream.map renderLine (render len (ppA a));
end;

fun toLine ppA a = toStringWithLineLength {lineLength = NONE} ppA a;

(* ------------------------------------------------------------------------- *)
(* Pretty-printer rendering with a global line length.                       *)
(* ------------------------------------------------------------------------- *)

val lineLength = ref initialLineLength;

fun toString ppA a =
    let
      val len = {lineLength = SOME (!lineLength)}
    in
      toStringWithLineLength len ppA a
    end;

fun toStream ppA a =
    let
      val len = {lineLength = SOME (!lineLength)}
    in
      toStreamWithLineLength len ppA a
    end;

local
  val sep = mkWord " =";
in
  fun trace ppX nameX x =
      Useful.trace (toString (ppOp2' sep ppString ppX) (nameX,x) ^ "\n");
end;

end

structure Sos = 
struct

val rat_0 = Rat.zero;
val rat_1 = Rat.one;
val rat_2 = Rat.two;
val rat_10 = Rat.rat_of_int 10;
val rat_1_2 = rat_1 // rat_2;
val max = curry IntInf.max;
val min = curry IntInf.min;

val denominator_rat = Rat.quotient_of_rat #> snd #> Rat.rat_of_int;
val numerator_rat = Rat.quotient_of_rat #> fst #> Rat.rat_of_int;
fun int_of_rat a = 
    case Rat.quotient_of_rat a of (i,1) => i | _ => error "int_of_rat: not an int";
fun lcm_rat x y = Rat.rat_of_int (Integer.lcm (int_of_rat x) (int_of_rat y));

fun rat_pow r i = 
 let fun pow r i = 
   if i = 0 then rat_1 else 
   let val d = pow r (i div 2)
   in d */ d */ (if i mod 2 = 0 then rat_1 else r)
   end
 in if i < 0 then pow (Rat.inv r) (~ i) else pow r i end;

fun round_rat r = 
 let val (a,b) = Rat.quotient_of_rat (Rat.abs r)
     val d = a div b
     val s = if r </ rat_0 then (Rat.neg o Rat.rat_of_int) else Rat.rat_of_int
     val x2 = 2 * (a - (b * d))
 in s (if x2 >= b then d + 1 else d) end

val abs_rat = Rat.abs;
val pow2 = rat_pow rat_2;
val pow10 = rat_pow rat_10;

val debugging = ref false;

exception Sanity;

exception Unsolvable;

(* Turn a rational into a decimal string with d sig digits.                  *)

local
fun normalize y =
  if abs_rat y </ (rat_1 // rat_10) then normalize (rat_10 */ y) - 1
  else if abs_rat y >=/ rat_1 then normalize (y // rat_10) + 1
  else 0 
 in
fun decimalize d x =
  if x =/ rat_0 then "0.0" else
  let 
   val y = Rat.abs x
   val e = normalize y
   val z = pow10(~ e) */ y +/ rat_1
   val k = int_of_rat (round_rat(pow10 d */ z))
  in (if x </ rat_0 then "-0." else "0.") ^
     implode(tl(explode(string_of_int k))) ^
     (if e = 0 then "" else "e"^string_of_int e)
  end
end;

(* Iterations over numbers, and lists indexed by numbers.                    *)

fun itern k l f a =
  case l of
    [] => a
  | h::t => itern (k + 1) t f (f h k a);

fun iter (m,n) f a =
  if n < m then a
  else iter (m+1,n) f (f m a);

(* The main types.                                                           *)

fun strict_ord ord (x,y) = case ord (x,y) of LESS => LESS | _ => GREATER

structure Intpairfunc = FuncFun(type key = int*int val ord = prod_ord int_ord int_ord);

type vector = int* Rat.rat Intfunc.T;

type matrix = (int*int)*(Rat.rat Intpairfunc.T);

type monomial = int Ctermfunc.T;

val cterm_ord = (fn (s,t) => TermOrd.fast_term_ord(term_of s, term_of t))
 fun monomial_ord (m1,m2) = list_ord (prod_ord cterm_ord int_ord) (Ctermfunc.graph m1, Ctermfunc.graph m2)
structure Monomialfunc = FuncFun(type key = monomial val ord = monomial_ord)

type poly = Rat.rat Monomialfunc.T;

 fun iszero (k,r) = r =/ rat_0;

fun fold_rev2 f l1 l2 b =
  case (l1,l2) of
    ([],[]) => b
  | (h1::t1,h2::t2) => f h1 h2 (fold_rev2 f t1 t2 b)
  | _ => error "fold_rev2";
 
(* Vectors. Conventionally indexed 1..n.                                     *)

fun vector_0 n = (n,Intfunc.undefined):vector;

fun dim (v:vector) = fst v;

fun vector_const c n =
  if c =/ rat_0 then vector_0 n
  else (n,fold_rev (fn k => Intfunc.update (k,c)) (1 upto n) Intfunc.undefined) :vector;

val vector_1 = vector_const rat_1;

fun vector_cmul c (v:vector) =
 let val n = dim v 
 in if c =/ rat_0 then vector_0 n
    else (n,Intfunc.mapf (fn x => c */ x) (snd v))
 end;

fun vector_neg (v:vector) = (fst v,Intfunc.mapf Rat.neg (snd v)) :vector;

fun vector_add (v1:vector) (v2:vector) =
 let val m = dim v1  
     val n = dim v2 
 in if m <> n then error "vector_add: incompatible dimensions"
    else (n,Intfunc.combine (curry op +/) (fn x => x =/ rat_0) (snd v1) (snd v2)) :vector 
 end;

fun vector_sub v1 v2 = vector_add v1 (vector_neg v2);

fun vector_dot (v1:vector) (v2:vector) =
 let val m = dim v1 
     val n = dim v2 
 in if m <> n then error "vector_dot: incompatible dimensions" 
    else Intfunc.fold (fn (i,x) => fn a => x +/ a) 
        (Intfunc.combine (curry op */) (fn x => x =/ rat_0) (snd v1) (snd v2)) rat_0
 end;

fun vector_of_list l =
 let val n = length l 
 in (n,fold_rev2 (curry Intfunc.update) (1 upto n) l Intfunc.undefined) :vector
 end;

(* Matrices; again rows and columns indexed from 1.                          *)

fun matrix_0 (m,n) = ((m,n),Intpairfunc.undefined):matrix;

fun dimensions (m:matrix) = fst m;

fun matrix_const c (mn as (m,n)) =
  if m <> n then error "matrix_const: needs to be square"
  else if c =/ rat_0 then matrix_0 mn
  else (mn,fold_rev (fn k => Intpairfunc.update ((k,k), c)) (1 upto n) Intpairfunc.undefined) :matrix;;

val matrix_1 = matrix_const rat_1;

fun matrix_cmul c (m:matrix) =
 let val (i,j) = dimensions m 
 in if c =/ rat_0 then matrix_0 (i,j)
    else ((i,j),Intpairfunc.mapf (fn x => c */ x) (snd m))
 end;

fun matrix_neg (m:matrix) = 
  (dimensions m, Intpairfunc.mapf Rat.neg (snd m)) :matrix;

fun matrix_add (m1:matrix) (m2:matrix) =
 let val d1 = dimensions m1 
     val d2 = dimensions m2 
 in if d1 <> d2 
     then error "matrix_add: incompatible dimensions"
    else (d1,Intpairfunc.combine (curry op +/) (fn x => x =/ rat_0) (snd m1) (snd m2)) :matrix
 end;;

fun matrix_sub m1 m2 = matrix_add m1 (matrix_neg m2);

fun row k (m:matrix) =
 let val (i,j) = dimensions m 
 in (j,
   Intpairfunc.fold (fn ((i,j), c) => fn a => if i = k then Intfunc.update (j,c) a else a) (snd m) Intfunc.undefined ) : vector
 end;

fun column k (m:matrix) =
  let val (i,j) = dimensions m 
  in (i,
   Intpairfunc.fold (fn ((i,j), c) => fn a => if j = k then Intfunc.update (i,c) a else a) (snd m)  Intfunc.undefined)
   : vector
 end;

fun transp (m:matrix) =
  let val (i,j) = dimensions m 
  in
  ((j,i),Intpairfunc.fold (fn ((i,j), c) => fn a => Intpairfunc.update ((j,i), c) a) (snd m) Intpairfunc.undefined) :matrix
 end;

fun diagonal (v:vector) =
 let val n = dim v 
 in ((n,n),Intfunc.fold (fn (i, c) => fn a => Intpairfunc.update ((i,i), c) a) (snd v) Intpairfunc.undefined) : matrix
 end;

fun matrix_of_list l =
 let val m = length l 
 in if m = 0 then matrix_0 (0,0) else
   let val n = length (hd l) 
   in ((m,n),itern 1 l (fn v => fn i => itern 1 v (fn c => fn j => Intpairfunc.update ((i,j), c))) Intpairfunc.undefined)
   end
 end;

(* Monomials.                                                                *)

fun monomial_eval assig (m:monomial) =
  Ctermfunc.fold (fn (x, k) => fn a => a */ rat_pow (Ctermfunc.apply assig x) k)
        m rat_1;
val monomial_1 = (Ctermfunc.undefined:monomial);

fun monomial_var x = Ctermfunc.onefunc (x, 1) :monomial;

val (monomial_mul:monomial->monomial->monomial) =
  Ctermfunc.combine (curry op +) (K false);

fun monomial_pow (m:monomial) k =
  if k = 0 then monomial_1
  else Ctermfunc.mapf (fn x => k * x) m;

fun monomial_divides (m1:monomial) (m2:monomial) =
  Ctermfunc.fold (fn (x, k) => fn a => Ctermfunc.tryapplyd m2 x 0 >= k andalso a) m1 true;;

fun monomial_div (m1:monomial) (m2:monomial) =
 let val m = Ctermfunc.combine (curry op +) 
   (fn x => x = 0) m1 (Ctermfunc.mapf (fn x => ~ x) m2) 
 in if Ctermfunc.fold (fn (x, k) => fn a => k >= 0 andalso a) m true then m
  else error "monomial_div: non-divisible"
 end;

fun monomial_degree x (m:monomial) = 
  Ctermfunc.tryapplyd m x 0;;

fun monomial_lcm (m1:monomial) (m2:monomial) =
  fold_rev (fn x => Ctermfunc.update (x, max (monomial_degree x m1) (monomial_degree x m2)))
          (gen_union (is_equal o  cterm_ord) (Ctermfunc.dom m1, Ctermfunc.dom m2)) (Ctermfunc.undefined :monomial);

fun monomial_multidegree (m:monomial) = 
 Ctermfunc.fold (fn (x, k) => fn a => k + a) m 0;;

fun monomial_variables m = Ctermfunc.dom m;;

(* Polynomials.                                                              *)

fun eval assig (p:poly) =
  Monomialfunc.fold (fn (m, c) => fn a => a +/ c */ monomial_eval assig m) p rat_0;

val poly_0 = (Monomialfunc.undefined:poly);

fun poly_isconst (p:poly) = 
  Monomialfunc.fold (fn (m, c) => fn a => Ctermfunc.is_undefined m andalso a) p true;

fun poly_var x = Monomialfunc.onefunc (monomial_var x,rat_1) :poly;

fun poly_const c =
  if c =/ rat_0 then poly_0 else Monomialfunc.onefunc(monomial_1, c);

fun poly_cmul c (p:poly) =
  if c =/ rat_0 then poly_0
  else Monomialfunc.mapf (fn x => c */ x) p;

fun poly_neg (p:poly) = (Monomialfunc.mapf Rat.neg p :poly);;

fun poly_add (p1:poly) (p2:poly) =
  (Monomialfunc.combine (curry op +/) (fn x => x =/ rat_0) p1 p2 :poly);

fun poly_sub p1 p2 = poly_add p1 (poly_neg p2);

fun poly_cmmul (c,m) (p:poly) =
 if c =/ rat_0 then poly_0
 else if Ctermfunc.is_undefined m 
      then Monomialfunc.mapf (fn d => c */ d) p
      else Monomialfunc.fold (fn (m', d) => fn a => (Monomialfunc.update (monomial_mul m m', c */ d) a)) p poly_0;

fun poly_mul (p1:poly) (p2:poly) =
  Monomialfunc.fold (fn (m, c) => fn a => poly_add (poly_cmmul (c,m) p2) a) p1 poly_0;

fun poly_div (p1:poly) (p2:poly) =
 if not(poly_isconst p2) 
 then error "poly_div: non-constant" else
 let val c = eval Ctermfunc.undefined p2 
 in if c =/ rat_0 then error "poly_div: division by zero"
    else poly_cmul (Rat.inv c) p1
 end;

fun poly_square p = poly_mul p p;

fun poly_pow p k =
 if k = 0 then poly_const rat_1
 else if k = 1 then p
 else let val q = poly_square(poly_pow p (k div 2)) in
      if k mod 2 = 1 then poly_mul p q else q end;

fun poly_exp p1 p2 =
  if not(poly_isconst p2) 
  then error "poly_exp: not a constant" 
  else poly_pow p1 (int_of_rat (eval Ctermfunc.undefined p2));

fun degree x (p:poly) = 
 Monomialfunc.fold (fn (m,c) => fn a => max (monomial_degree x m) a) p 0;

fun multidegree (p:poly) =
  Monomialfunc.fold (fn (m, c) => fn a => max (monomial_multidegree m) a) p 0;

fun poly_variables (p:poly) =
  sort cterm_ord (Monomialfunc.fold_rev (fn (m, c) => curry (gen_union (is_equal o  cterm_ord)) (monomial_variables m)) p []);;

(* Order monomials for human presentation.                                   *)

fun cterm_ord (t,t') = TermOrd.fast_term_ord (term_of t, term_of t');

val humanorder_varpow = prod_ord cterm_ord (rev_order o int_ord);

local
 fun ord (l1,l2) = case (l1,l2) of
  (_,[]) => LESS 
 | ([],_) => GREATER
 | (h1::t1,h2::t2) => 
   (case humanorder_varpow (h1, h2) of 
     LESS => LESS
   | EQUAL => ord (t1,t2)
   | GREATER => GREATER)
in fun humanorder_monomial m1 m2 = 
 ord (sort humanorder_varpow (Ctermfunc.graph m1),
  sort humanorder_varpow (Ctermfunc.graph m2))
end;

fun fold1 f l =  case l of
   []     => error "fold1"
 | [x]    => x
 | (h::t) => f h (fold1 f t);

(* Conversions to strings.                                                   *)

fun string_of_vector min_size max_size (v:vector) =
 let val n_raw = dim v 
 in if n_raw = 0 then "[]" else
  let 
   val n = max min_size (min n_raw max_size) 
   val xs = map (Rat.string_of_rat o (fn i => Intfunc.tryapplyd (snd v) i rat_0)) (1 upto n) 
  in "[" ^ fold1 (fn s => fn t => s ^ ", " ^ t) xs ^
  (if n_raw > max_size then ", ...]" else "]")
  end
 end;

fun string_of_matrix max_size (m:matrix) =
 let 
  val (i_raw,j_raw) = dimensions m
  val i = min max_size i_raw 
  val j = min max_size j_raw
  val rstr = map (fn k => string_of_vector j j (row k m)) (1 upto i) 
 in "["^ fold1 (fn s => fn t => s^";\n "^t) rstr ^
  (if j > max_size then "\n ...]" else "]")
 end;

fun string_of_term t = 
 case t of
   a$b => "("^(string_of_term a)^" "^(string_of_term b)^")"
 | Abs x => 
    let val (xn, b) = Term.dest_abs x
    in "(\\"^xn^"."^(string_of_term b)^")"
    end
 | Const(s,_) => s
 | Free (s,_) => s
 | Var((s,_),_) => s
 | _ => error "string_of_term";

val string_of_cterm = string_of_term o term_of;

fun string_of_varpow x k =
  if k = 1 then string_of_cterm x 
  else string_of_cterm x^"^"^string_of_int k;

fun string_of_monomial m =
 if Ctermfunc.is_undefined m then "1" else
 let val vps = fold_rev (fn (x,k) => fn a => string_of_varpow x k :: a)
  (sort humanorder_varpow (Ctermfunc.graph m)) [] 
 in fold1 (fn s => fn t => s^"*"^t) vps
 end;

fun string_of_cmonomial (c,m) =
 if Ctermfunc.is_undefined m then Rat.string_of_rat c
 else if c =/ rat_1 then string_of_monomial m
 else Rat.string_of_rat c ^ "*" ^ string_of_monomial m;;

fun string_of_poly (p:poly) =
 if Monomialfunc.is_undefined p then "<<0>>" else
 let 
  val cms = sort (fn ((m1,_),(m2,_)) => humanorder_monomial m1  m2) (Monomialfunc.graph p)
  val s = fold (fn (m,c) => fn a =>
             if c </ rat_0 then a ^ " - " ^ string_of_cmonomial(Rat.neg c,m)
             else a ^ " + " ^ string_of_cmonomial(c,m))
          cms ""
  val s1 = String.substring (s, 0, 3)
  val s2 = String.substring (s, 3, String.size s - 3) 
 in "<<" ^(if s1 = " + " then s2 else "-"^s2)^">>"
 end;

(* Conversion from HOL term.                                                 *)

local
 val neg_tm = @{cterm "uminus :: real => _"}
 val add_tm = @{cterm "op + :: real => _"}
 val sub_tm = @{cterm "op - :: real => _"}
 val mul_tm = @{cterm "op * :: real => _"}
 val inv_tm = @{cterm "inverse :: real => _"}
 val div_tm = @{cterm "op / :: real => _"}
 val pow_tm = @{cterm "op ^ :: real => _"}
 val zero_tm = @{cterm "0:: real"}
 val is_numeral = can (HOLogic.dest_number o term_of)
 fun is_comb t = case t of _$_ => true | _ => false
 fun poly_of_term tm =
  if tm aconvc zero_tm then poly_0
  else if RealArith.is_ratconst tm 
       then poly_const(RealArith.dest_ratconst tm)
  else 
  (let val (lop,r) = Thm.dest_comb tm
   in if lop aconvc neg_tm then poly_neg(poly_of_term r)
      else if lop aconvc inv_tm then
       let val p = poly_of_term r 
       in if poly_isconst p 
          then poly_const(Rat.inv (eval Ctermfunc.undefined p))
          else error "poly_of_term: inverse of non-constant polyomial"
       end
   else (let val (opr,l) = Thm.dest_comb lop
         in 
          if opr aconvc pow_tm andalso is_numeral r 
          then poly_pow (poly_of_term l) ((snd o HOLogic.dest_number o term_of) r)
          else if opr aconvc add_tm 
           then poly_add (poly_of_term l) (poly_of_term r)
          else if opr aconvc sub_tm 
           then poly_sub (poly_of_term l) (poly_of_term r)
          else if opr aconvc mul_tm 
           then poly_mul (poly_of_term l) (poly_of_term r)
          else if opr aconvc div_tm 
           then let 
                  val p = poly_of_term l 
                  val q = poly_of_term r 
                in if poly_isconst q then poly_cmul (Rat.inv (eval Ctermfunc.undefined q)) p
                   else error "poly_of_term: division by non-constant polynomial"
                end
          else poly_var tm
 
         end
         handle CTERM ("dest_comb",_) => poly_var tm)
   end
   handle CTERM ("dest_comb",_) => poly_var tm)
in
val poly_of_term = fn tm =>
 if type_of (term_of tm) = @{typ real} then poly_of_term tm
 else error "poly_of_term: term does not have real type"
end;

(* String of vector (just a list of space-separated numbers).                *)

fun sdpa_of_vector (v:vector) =
 let 
  val n = dim v
  val strs = map (decimalize 20 o (fn i => Intfunc.tryapplyd (snd v) i rat_0)) (1 upto n) 
 in fold1 (fn x => fn y => x ^ " " ^ y) strs ^ "\n"
 end;

fun increasing f ord (x,y) = ord (f x, f y);
fun triple_int_ord ((a,b,c),(a',b',c')) = 
 prod_ord int_ord (prod_ord int_ord int_ord) 
    ((a,(b,c)),(a',(b',c')));
structure Inttriplefunc = FuncFun(type key = int*int*int val ord = triple_int_ord);

(* String for block diagonal matrix numbered k.                              *)

fun sdpa_of_blockdiagonal k m =
 let 
  val pfx = string_of_int k ^" "
  val ents =
    Inttriplefunc.fold (fn ((b,i,j), c) => fn a => if i > j then a else ((b,i,j),c)::a) m []
  val entss = sort (increasing fst triple_int_ord ) ents
 in  fold_rev (fn ((b,i,j),c) => fn a =>
     pfx ^ string_of_int b ^ " " ^ string_of_int i ^ " " ^ string_of_int j ^
     " " ^ decimalize 20 c ^ "\n" ^ a) entss ""
 end;

(* String for a matrix numbered k, in SDPA sparse format.                    *)

fun sdpa_of_matrix k (m:matrix) =
 let 
  val pfx = string_of_int k ^ " 1 "
  val ms = Intpairfunc.fold (fn ((i,j), c) => fn  a => if i > j then a else ((i,j),c)::a) (snd m) [] 
  val mss = sort (increasing fst (prod_ord int_ord int_ord)) ms 
 in fold_rev (fn ((i,j),c) => fn a =>
     pfx ^ string_of_int i ^ " " ^ string_of_int j ^
     " " ^ decimalize 20 c ^ "\n" ^ a) mss ""
 end;;

(* ------------------------------------------------------------------------- *)
(* String in SDPA sparse format for standard SDP problem:                    *)
(*                                                                           *)
(*    X = v_1 * [M_1] + ... + v_m * [M_m] - [M_0] must be PSD                *)
(*    Minimize obj_1 * v_1 + ... obj_m * v_m                                 *)
(* ------------------------------------------------------------------------- *)

fun sdpa_of_problem comment obj mats =
 let 
  val m = length mats - 1
  val (n,_) = dimensions (hd mats) 
 in "\"" ^ comment ^ "\"\n" ^
  string_of_int m ^ "\n" ^
  "1\n" ^
  string_of_int n ^ "\n" ^
  sdpa_of_vector obj ^
  fold_rev2 (fn k => fn m => fn a => sdpa_of_matrix (k - 1) m ^ a) (1 upto length mats) mats ""
 end;

fun index_char str chr pos =
  if pos >= String.size str then ~1
  else if String.sub(str,pos) = chr then pos
  else index_char str chr (pos + 1);
fun rat_of_quotient (a,b) = if b = 0 then rat_0 else Rat.rat_of_quotient (a,b);
fun rat_of_string s = 
 let val n = index_char s #"/" 0 in
  if n = ~1 then s |> IntInf.fromString |> valOf |> Rat.rat_of_int
  else 
   let val SOME numer = IntInf.fromString(String.substring(s,0,n))
       val SOME den = IntInf.fromString (String.substring(s,n+1,String.size s - n - 1))
   in rat_of_quotient(numer, den)
   end
 end;

fun isspace x = x = " " ;
fun isnum x = x mem_string ["0","1","2","3","4","5","6","7","8","9"]

(* More parser basics.                                                       *)

local
 open Scan
in 
 val word = this_string
 fun token s =
  repeat ($$ " ") |-- word s --| repeat ($$ " ")
 val numeral = one isnum
 val decimalint = bulk numeral >> (rat_of_string o implode)
 val decimalfrac = bulk numeral
    >> (fn s => rat_of_string(implode s) // pow10 (length s))
 val decimalsig =
    decimalint -- option (Scan.$$ "." |-- decimalfrac)
    >> (fn (h,NONE) => h | (h,SOME x) => h +/ x)
 fun signed prs =
       $$ "-" |-- prs >> Rat.neg 
    || $$ "+" |-- prs
    || prs;

fun emptyin def xs = if null xs then (def,xs) else Scan.fail xs

 val exponent = ($$ "e" || $$ "E") |-- signed decimalint;

 val decimal = signed decimalsig -- (emptyin rat_0|| exponent)
    >> (fn (h, x) => h */ pow10 (int_of_rat x));
end;

 fun mkparser p s =
  let val (x,rst) = p (explode s) 
  in if null rst then x 
     else error "mkparser: unparsed input"
  end;;
val parse_decimal = mkparser decimal;

fun fix err prs = 
  prs || (fn x=> error err);

fun listof prs sep err =
  prs -- Scan.bulk (sep |-- fix err prs) >> uncurry cons;

(* Parse back a vector.                                                      *)

 val vector = 
    token "{" |-- listof decimal (token ",") "decimal" --| token "}"
               >> vector_of_list 
 val parse_vector = mkparser vector
 fun skipupto dscr prs inp =
   (dscr |-- prs 
    || Scan.one (K true) |-- skipupto dscr prs) inp 
 fun ignore inp = ((),[])
 fun sdpaoutput inp =  skipupto (word "xVec" -- token "=")
             (vector --| ignore) inp
 fun csdpoutput inp =  ((decimal -- Scan.bulk (Scan.$$ " " |-- Scan.option decimal) >> (fn (h,to) => map_filter I ((SOME h)::to))) --| ignore >> vector_of_list) inp
 val parse_sdpaoutput = mkparser sdpaoutput
 val parse_csdpoutput = mkparser csdpoutput

(* Also parse the SDPA output to test success (CSDP yields a return code).   *)

local
 val prs = 
  skipupto (word "phase.value" -- token "=")
   (Scan.option (Scan.$$ "p") -- Scan.option (Scan.$$ "d") 
    -- (word "OPT" || word "FEAS")) 
in
 fun sdpa_run_succeeded s = 
  (prs (explode s); true) handle _ => false
end;

(* The default parameters. Unfortunately this goes to a fixed file.          *)

val sdpa_default_parameters =
"100     unsigned int maxIteration; \n1.0E-7  double 0.0 < epsilonStar;\n1.0E2   double 0.0 < lambdaStar;\n2.0     double 1.0 < omegaStar;\n-1.0E5  double lowerBound;\n1.0E5   double upperBound;\n0.1     double 0.0 <= betaStar <  1.0;\n0.2     double 0.0 <= betaBar  <  1.0, betaStar <= betaBar;\n0.9     double 0.0 < gammaStar  <  1.0;\n1.0E-7  double 0.0 < epsilonDash;\n";;

(* These were suggested by Makoto Yamashita for problems where we are        *)
(* right at the edge of the semidefinite cone, as sometimes happens.         *)

val sdpa_alt_parameters =
"1000    unsigned int maxIteration;\n1.0E-7  double 0.0 < epsilonStar;\n1.0E4   double 0.0 < lambdaStar;\n2.0     double 1.0 < omegaStar;\n-1.0E5  double lowerBound;\n1.0E5   double upperBound;\n0.1     double 0.0 <= betaStar <  1.0;\n0.2     double 0.0 <= betaBar  <  1.0, betaStar <= betaBar;\n0.9     double 0.0 < gammaStar  <  1.0;\n1.0E-7  double 0.0 < epsilonDash;\n";;

val sdpa_params = sdpa_alt_parameters;;

(* CSDP parameters; so far I'm sticking with the defaults.                   *)

val csdp_default_parameters =
"axtol=1.0e-8\natytol=1.0e-8\nobjtol=1.0e-8\npinftol=1.0e8\ndinftol=1.0e8\nmaxiter=100\nminstepfrac=0.9\nmaxstepfrac=0.97\nminstepp=1.0e-8\nminstepd=1.0e-8\nusexzgap=1\ntweakgap=0\naffine=0\nprintlevel=1\n";;

val csdp_params = csdp_default_parameters;;

fun tmp_file pre suf =
 let val i = string_of_int (round (random()))
   val name = Path.append (Path.variable "ISABELLE_TMP") (Path.explode (pre ^ i ^ suf))
 in 
   if File.exists name then tmp_file pre suf 
   else name 
 end;

(* Now call SDPA on a problem and parse back the output.                     *)

fun run_sdpa dbg obj mats =
 let 
  val input_file = tmp_file "sos" ".dat-s"
  val output_file = tmp_file "sos" ".out"
  val params_file = tmp_file "param" ".sdpa" 
  val current_dir = File.pwd()
  val _ = File.write input_file 
                         (sdpa_of_problem "" obj mats)
  val _ = File.write params_file sdpa_params
  val _ = File.cd (Path.variable "ISABELLE_TMP")
  val _ = File.system_command ("sdpa "^ (Path.implode input_file) ^ " " ^ 
                               (Path.implode output_file) ^
                               (if dbg then "" else "> /dev/null"))
  val opr = File.read output_file 
 in if not(sdpa_run_succeeded opr) then error "sdpa: call failed" 
    else
      let val res = parse_sdpaoutput opr 
      in ((if dbg then ()
           else (File.rm input_file; File.rm output_file ; File.cd current_dir));
          res)
      end
 end;

fun sdpa obj mats = run_sdpa (!debugging) obj mats;

(* The same thing with CSDP.                                                 *)

fun run_csdp dbg obj mats =
 let 
  val input_file = tmp_file "sos" ".dat-s"
  val output_file = tmp_file "sos" ".out"
  val params_file = tmp_file "param" ".csdp"
  val current_dir = File.pwd()
  val _ = File.write input_file (sdpa_of_problem "" obj mats)
  val _ = File.write params_file csdp_params
  val _ = File.cd (Path.variable "ISABELLE_TMP")
  val rv = system ("csdp "^(Path.implode input_file) ^ " " 
                   ^ (Path.implode output_file) ^
                   (if dbg then "" else "> /dev/null"))
  val  opr = File.read output_file 
  val res = parse_csdpoutput opr 
 in
    ((if dbg then ()
      else (File.rm input_file; File.rm output_file ; File.cd current_dir));
     (rv,res))
 end;

fun csdp obj mats =
 let 
  val (rv,res) = run_csdp (!debugging) obj mats 
 in
   ((if rv = 1 orelse rv = 2 then error "csdp: Problem is infeasible"
    else if rv = 3 then writeln "csdp warning: Reduced accuracy"
    else if rv <> 0 then error ("csdp: error "^string_of_int rv)
    else ());
   res)
 end;

(* Try some apparently sensible scaling first. Note that this is purely to   *)
(* get a cleaner translation to floating-point, and doesn't affect any of    *)
(* the results, in principle. In practice it seems a lot better when there   *)
(* are extreme numbers in the original problem.                              *)

  (* Version for (int*int) keys *)
local
  fun max_rat x y = if x </ y then y else x
  fun common_denominator fld amat acc =
      fld (fn (m,c) => fn a => lcm_rat (denominator_rat c) a) amat acc
  fun maximal_element fld amat acc =
    fld (fn (m,c) => fn maxa => max_rat maxa (abs_rat c)) amat acc 
fun float_of_rat x = let val (a,b) = Rat.quotient_of_rat x
                     in Real.fromLargeInt a / Real.fromLargeInt b end;
in

fun pi_scale_then solver (obj:vector)  mats =
 let 
  val cd1 = fold_rev (common_denominator Intpairfunc.fold) mats (rat_1)
  val cd2 = common_denominator Intfunc.fold (snd obj)  (rat_1) 
  val mats' = map (Intpairfunc.mapf (fn x => cd1 */ x)) mats
  val obj' = vector_cmul cd2 obj
  val max1 = fold_rev (maximal_element Intpairfunc.fold) mats' (rat_0)
  val max2 = maximal_element Intfunc.fold (snd obj') (rat_0) 
  val scal1 = pow2 (20 - trunc(Math.ln (float_of_rat max1) / Math.ln 2.0))
  val scal2 = pow2 (20 - trunc(Math.ln (float_of_rat max2) / Math.ln 2.0)) 
  val mats'' = map (Intpairfunc.mapf (fn x => x */ scal1)) mats'
  val obj'' = vector_cmul scal2 obj' 
 in solver obj'' mats''
  end
end;

(* Try some apparently sensible scaling first. Note that this is purely to   *)
(* get a cleaner translation to floating-point, and doesn't affect any of    *)
(* the results, in principle. In practice it seems a lot better when there   *)
(* are extreme numbers in the original problem.                              *)

  (* Version for (int*int*int) keys *)
local
  fun max_rat x y = if x </ y then y else x
  fun common_denominator fld amat acc =
      fld (fn (m,c) => fn a => lcm_rat (denominator_rat c) a) amat acc
  fun maximal_element fld amat acc =
    fld (fn (m,c) => fn maxa => max_rat maxa (abs_rat c)) amat acc 
fun float_of_rat x = let val (a,b) = Rat.quotient_of_rat x
                     in Real.fromLargeInt a / Real.fromLargeInt b end;
fun int_of_float x = (trunc x handle Overflow => 0 | Domain => 0)
in

fun tri_scale_then solver (obj:vector)  mats =
 let 
  val cd1 = fold_rev (common_denominator Inttriplefunc.fold) mats (rat_1)
  val cd2 = common_denominator Intfunc.fold (snd obj)  (rat_1) 
  val mats' = map (Inttriplefunc.mapf (fn x => cd1 */ x)) mats
  val obj' = vector_cmul cd2 obj
  val max1 = fold_rev (maximal_element Inttriplefunc.fold) mats' (rat_0)
  val max2 = maximal_element Intfunc.fold (snd obj') (rat_0) 
  val scal1 = pow2 (20 - int_of_float(Math.ln (float_of_rat max1) / Math.ln 2.0))
  val scal2 = pow2 (20 - int_of_float(Math.ln (float_of_rat max2) / Math.ln 2.0)) 
  val mats'' = map (Inttriplefunc.mapf (fn x => x */ scal1)) mats'
  val obj'' = vector_cmul scal2 obj' 
 in solver obj'' mats''
  end
end;

(* Round a vector to "nice" rationals.                                       *)

fun nice_rational n x = round_rat (n */ x) // n;;
fun nice_vector n ((d,v) : vector) = 
 (d, Intfunc.fold (fn (i,c) => fn a => 
   let val y = nice_rational n c 
   in if c =/ rat_0 then a 
      else Intfunc.update (i,y) a end) v Intfunc.undefined):vector


(* Reduce linear program to SDP (diagonal matrices) and test with CSDP. This *)
(* one tests A [-1;x1;..;xn] >= 0 (i.e. left column is negated constants).   *)

fun linear_program_basic a =
 let 
  val (m,n) = dimensions a
  val mats =  map (fn j => diagonal (column j a)) (1 upto n)
  val obj = vector_const rat_1 m 
  val (rv,res) = run_csdp false obj mats 
 in if rv = 1 orelse rv = 2 then false
    else if rv = 0 then true
    else error "linear_program: An error occurred in the SDP solver"
 end;

(* Alternative interface testing A x >= b for matrix A, vector b.            *)

fun linear_program a b =
 let val (m,n) = dimensions a 
 in if dim b <> m then error "linear_program: incompatible dimensions" 
    else
    let 
     val mats = diagonal b :: map (fn j => diagonal (column j a)) (1 upto n)
     val obj = vector_const rat_1 m 
     val (rv,res) = run_csdp false obj mats 
    in if rv = 1 orelse rv = 2 then false
       else if rv = 0 then true
       else error "linear_program: An error occurred in the SDP solver"
    end
 end;

(* Test whether a point is in the convex hull of others. Rather than use     *)
(* computational geometry, express as linear inequalities and call CSDP.     *)
(* This is a bit lazy of me, but it's easy and not such a bottleneck so far. *)

fun in_convex_hull pts pt =
 let 
  val pts1 = (1::pt) :: map (fn x => 1::x) pts 
  val pts2 = map (fn p => map (fn x => ~x) p @ p) pts1
  val n = length pts + 1
  val v = 2 * (length pt + 1)
  val m = v + n - 1 
  val mat = ((m,n),
  itern 1 pts2 (fn pts => fn j => itern 1 pts 
               (fn x => fn i => Intpairfunc.update ((i,j), Rat.rat_of_int x)))
  (iter (1,n) (fn i => Intpairfunc.update((v + i,i+1), rat_1)) 
      Intpairfunc.undefined))
 in linear_program_basic mat
 end;

(* Filter down a set of points to a minimal set with the same convex hull.   *)

local
 fun augment1 (m::ms) = if in_convex_hull ms m then ms else ms@[m]
 fun augment m ms = funpow 3 augment1 (m::ms)
in
fun minimal_convex_hull mons =
 let val mons' = fold_rev augment (tl mons) [hd mons] 
 in funpow (length mons') augment1 mons'
 end
end;

fun dest_ord f x = is_equal (f x);

(* Stuff for "equations" ((int*int*int)->num functions).                         *)

fun tri_equation_cmul c eq =
  if c =/ rat_0 then Inttriplefunc.undefined else Inttriplefunc.mapf (fn d => c */ d) eq;

fun tri_equation_add eq1 eq2 = Inttriplefunc.combine (curry op +/) (fn x => x =/ rat_0) eq1 eq2;

fun tri_equation_eval assig eq =
 let fun value v = Inttriplefunc.apply assig v 
 in Inttriplefunc.fold (fn (v, c) => fn a => a +/ value v */ c) eq rat_0
 end;

(* Eliminate among linear equations: return unconstrained variables and      *)
(* assignments for the others in terms of them. We give one pseudo-variable  *)
(* "one" that's used for a constant term.                                    *)

local
  fun extract_first p l = case l of  (* FIXME : use find_first instead *)
   [] => error "extract_first"
 | h::t => if p h then (h,t) else
          let val (k,s) = extract_first p t in (k,h::s) end
fun eliminate vars dun eqs = case vars of 
  [] => if forall Inttriplefunc.is_undefined eqs then dun
        else raise Unsolvable
 | v::vs =>
  ((let 
    val (eq,oeqs) = extract_first (fn e => Inttriplefunc.defined e v) eqs 
    val a = Inttriplefunc.apply eq v
    val eq' = tri_equation_cmul ((Rat.neg rat_1) // a) (Inttriplefunc.undefine v eq)
    fun elim e =
     let val b = Inttriplefunc.tryapplyd e v rat_0 
     in if b =/ rat_0 then e else
        tri_equation_add e (tri_equation_cmul (Rat.neg b // a) eq)
     end
   in eliminate vs (Inttriplefunc.update (v,eq') (Inttriplefunc.mapf elim dun)) (map elim oeqs)
   end)
  handle ERROR _ => eliminate vs dun eqs)
in
fun tri_eliminate_equations one vars eqs =
 let 
  val assig = eliminate vars Inttriplefunc.undefined eqs
  val vs = Inttriplefunc.fold (fn (x, f) => fn a => remove (dest_ord triple_int_ord) one (Inttriplefunc.dom f) @ a) assig []
  in (distinct (dest_ord triple_int_ord) vs, assig)
  end
end;

(* Eliminate all variables, in an essentially arbitrary order.               *)

fun tri_eliminate_all_equations one =
 let 
  fun choose_variable eq =
   let val (v,_) = Inttriplefunc.choose eq 
   in if is_equal (triple_int_ord(v,one)) then
      let val eq' = Inttriplefunc.undefine v eq 
      in if Inttriplefunc.is_undefined eq' then error "choose_variable" 
         else fst (Inttriplefunc.choose eq')
      end
    else v 
   end
  fun eliminate dun eqs = case eqs of 
    [] => dun
  | eq::oeqs =>
    if Inttriplefunc.is_undefined eq then eliminate dun oeqs else
    let val v = choose_variable eq
        val a = Inttriplefunc.apply eq v
        val eq' = tri_equation_cmul ((Rat.rat_of_int ~1) // a) 
                   (Inttriplefunc.undefine v eq)
        fun elim e =
         let val b = Inttriplefunc.tryapplyd e v rat_0 
         in if b =/ rat_0 then e 
            else tri_equation_add e (tri_equation_cmul (Rat.neg b // a) eq)
         end
    in eliminate (Inttriplefunc.update(v, eq') (Inttriplefunc.mapf elim dun)) 
                 (map elim oeqs) 
    end
in fn eqs =>
 let 
  val assig = eliminate Inttriplefunc.undefined eqs
  val vs = Inttriplefunc.fold (fn (x, f) => fn a => remove (dest_ord triple_int_ord) one (Inttriplefunc.dom f) @ a) assig []
 in (distinct (dest_ord triple_int_ord) vs,assig)
 end
end;
 
(* Solve equations by assigning arbitrary numbers.                           *)

fun tri_solve_equations one eqs =
 let 
  val (vars,assigs) = tri_eliminate_all_equations one eqs
  val vfn = fold_rev (fn v => Inttriplefunc.update(v,rat_0)) vars 
            (Inttriplefunc.onefunc(one, Rat.rat_of_int ~1))
  val ass =
    Inttriplefunc.combine (curry op +/) (K false) 
    (Inttriplefunc.mapf (tri_equation_eval vfn) assigs) vfn 
 in if forall (fn e => tri_equation_eval ass e =/ rat_0) eqs
    then Inttriplefunc.undefine one ass else raise Sanity
 end;

(* Multiply equation-parametrized poly by regular poly and add accumulator.  *)

fun tri_epoly_pmul p q acc =
 Monomialfunc.fold (fn (m1, c) => fn a =>
  Monomialfunc.fold (fn (m2,e) => fn b =>
   let val m =  monomial_mul m1 m2
       val es = Monomialfunc.tryapplyd b m Inttriplefunc.undefined 
   in Monomialfunc.update (m,tri_equation_add (tri_equation_cmul c e) es) b 
   end) q a) p acc ;

(* Usual operations on equation-parametrized poly.                           *)

fun tri_epoly_cmul c l =
  if c =/ rat_0 then Inttriplefunc.undefined else Inttriplefunc.mapf (tri_equation_cmul c) l;;

val tri_epoly_neg = tri_epoly_cmul (Rat.rat_of_int ~1);

val tri_epoly_add = Inttriplefunc.combine tri_equation_add Inttriplefunc.is_undefined;

fun tri_epoly_sub p q = tri_epoly_add p (tri_epoly_neg q);;

(* Stuff for "equations" ((int*int)->num functions).                         *)

fun pi_equation_cmul c eq =
  if c =/ rat_0 then Inttriplefunc.undefined else Inttriplefunc.mapf (fn d => c */ d) eq;

fun pi_equation_add eq1 eq2 = Inttriplefunc.combine (curry op +/) (fn x => x =/ rat_0) eq1 eq2;

fun pi_equation_eval assig eq =
 let fun value v = Inttriplefunc.apply assig v 
 in Inttriplefunc.fold (fn (v, c) => fn a => a +/ value v */ c) eq rat_0
 end;

(* Eliminate among linear equations: return unconstrained variables and      *)
(* assignments for the others in terms of them. We give one pseudo-variable  *)
(* "one" that's used for a constant term.                                    *)

local
fun extract_first p l = case l of 
   [] => error "extract_first"
 | h::t => if p h then (h,t) else
          let val (k,s) = extract_first p t in (k,h::s) end
fun eliminate vars dun eqs = case vars of 
  [] => if forall Inttriplefunc.is_undefined eqs then dun
        else raise Unsolvable
 | v::vs =>
   let 
    val (eq,oeqs) = extract_first (fn e => Inttriplefunc.defined e v) eqs 
    val a = Inttriplefunc.apply eq v
    val eq' = pi_equation_cmul ((Rat.neg rat_1) // a) (Inttriplefunc.undefine v eq)
    fun elim e =
     let val b = Inttriplefunc.tryapplyd e v rat_0 
     in if b =/ rat_0 then e else
        pi_equation_add e (pi_equation_cmul (Rat.neg b // a) eq)
     end
   in eliminate vs (Inttriplefunc.update (v,eq') (Inttriplefunc.mapf elim dun)) (map elim oeqs)
   end
  handle ERROR _ => eliminate vs dun eqs
in
fun pi_eliminate_equations one vars eqs =
 let 
  val assig = eliminate vars Inttriplefunc.undefined eqs
  val vs = Inttriplefunc.fold (fn (x, f) => fn a => remove (dest_ord triple_int_ord) one (Inttriplefunc.dom f) @ a) assig []
  in (distinct (dest_ord triple_int_ord) vs, assig)
  end
end;

(* Eliminate all variables, in an essentially arbitrary order.               *)

fun pi_eliminate_all_equations one =
 let 
  fun choose_variable eq =
   let val (v,_) = Inttriplefunc.choose eq 
   in if is_equal (triple_int_ord(v,one)) then
      let val eq' = Inttriplefunc.undefine v eq 
      in if Inttriplefunc.is_undefined eq' then error "choose_variable" 
         else fst (Inttriplefunc.choose eq')
      end
    else v 
   end
  fun eliminate dun eqs = case eqs of 
    [] => dun
  | eq::oeqs =>
    if Inttriplefunc.is_undefined eq then eliminate dun oeqs else
    let val v = choose_variable eq
        val a = Inttriplefunc.apply eq v
        val eq' = pi_equation_cmul ((Rat.rat_of_int ~1) // a) 
                   (Inttriplefunc.undefine v eq)
        fun elim e =
         let val b = Inttriplefunc.tryapplyd e v rat_0 
         in if b =/ rat_0 then e 
            else pi_equation_add e (pi_equation_cmul (Rat.neg b // a) eq)
         end
    in eliminate (Inttriplefunc.update(v, eq') (Inttriplefunc.mapf elim dun)) 
                 (map elim oeqs) 
    end
in fn eqs =>
 let 
  val assig = eliminate Inttriplefunc.undefined eqs
  val vs = Inttriplefunc.fold (fn (x, f) => fn a => remove (dest_ord triple_int_ord) one (Inttriplefunc.dom f) @ a) assig []
 in (distinct (dest_ord triple_int_ord) vs,assig)
 end
end;
 
(* Solve equations by assigning arbitrary numbers.                           *)

fun pi_solve_equations one eqs =
 let 
  val (vars,assigs) = pi_eliminate_all_equations one eqs
  val vfn = fold_rev (fn v => Inttriplefunc.update(v,rat_0)) vars 
            (Inttriplefunc.onefunc(one, Rat.rat_of_int ~1))
  val ass =
    Inttriplefunc.combine (curry op +/) (K false) 
    (Inttriplefunc.mapf (pi_equation_eval vfn) assigs) vfn 
 in if forall (fn e => pi_equation_eval ass e =/ rat_0) eqs
    then Inttriplefunc.undefine one ass else raise Sanity
 end;

(* Multiply equation-parametrized poly by regular poly and add accumulator.  *)

fun pi_epoly_pmul p q acc =
 Monomialfunc.fold (fn (m1, c) => fn a =>
  Monomialfunc.fold (fn (m2,e) => fn b =>
   let val m =  monomial_mul m1 m2
       val es = Monomialfunc.tryapplyd b m Inttriplefunc.undefined 
   in Monomialfunc.update (m,pi_equation_add (pi_equation_cmul c e) es) b 
   end) q a) p acc ;

(* Usual operations on equation-parametrized poly.                           *)

fun pi_epoly_cmul c l =
  if c =/ rat_0 then Inttriplefunc.undefined else Inttriplefunc.mapf (pi_equation_cmul c) l;;

val pi_epoly_neg = pi_epoly_cmul (Rat.rat_of_int ~1);

val pi_epoly_add = Inttriplefunc.combine pi_equation_add Inttriplefunc.is_undefined;

fun pi_epoly_sub p q = pi_epoly_add p (pi_epoly_neg q);;

fun allpairs f l1 l2 =  fold_rev (fn x => (curry (op @)) (map (f x) l2)) l1 [];

(* Hence produce the "relevant" monomials: those whose squares lie in the    *)
(* Newton polytope of the monomials in the input. (This is enough according  *)
(* to Reznik: "Extremal PSD forms with few terms", Duke Math. Journal,       *)
(* vol 45, pp. 363--374, 1978.                                               *)
(*                                                                           *)
(* These are ordered in sort of decreasing degree. In particular the         *)
(* constant monomial is last; this gives an order in diagonalization of the  *)
(* quadratic form that will tend to display constants.                       *)

fun newton_polytope pol =
 let 
  val vars = poly_variables pol
  val mons = map (fn m => map (fn x => monomial_degree x m) vars) 
             (Monomialfunc.dom pol)
  val ds = map (fn x => (degree x pol + 1) div 2) vars
  val all = fold_rev (fn n => allpairs cons (0 upto n)) ds [[]]
  val mons' = minimal_convex_hull mons
  val all' =
    filter (fn m => in_convex_hull mons' (map (fn x => 2 * x) m)) all 
 in map (fn m => fold_rev2 (fn v => fn i => fn a => if i = 0 then a else Ctermfunc.update (v,i) a)
                        vars m monomial_1) (rev all')
 end;

(* Diagonalize (Cholesky/LDU) the matrix corresponding to a quadratic form.  *)

local
fun diagonalize n i m =
 if Intpairfunc.is_undefined (snd m) then [] 
 else
  let val a11 = Intpairfunc.tryapplyd (snd m) (i,i) rat_0 
  in if a11 </ rat_0 then error "diagonalize: not PSD"
    else if a11 =/ rat_0 then
          if Intfunc.is_undefined (snd (row i m)) then diagonalize n (i + 1) m
          else error "diagonalize: not PSD ___ "
    else
     let 
      val v = row i m
      val v' = (fst v, Intfunc.fold (fn (i, c) => fn a => 
       let val y = c // a11 
       in if y = rat_0 then a else Intfunc.update (i,y) a 
       end)  (snd v) Intfunc.undefined)
      fun upt0 x y a = if y = rat_0 then a else Intpairfunc.update (x,y) a
      val m' =
      ((n,n),
      iter (i+1,n) (fn j =>
          iter (i+1,n) (fn k =>
              (upt0 (j,k) (Intpairfunc.tryapplyd (snd m) (j,k) rat_0 -/ Intfunc.tryapplyd (snd v) j rat_0 */ Intfunc.tryapplyd (snd v') k rat_0))))
          Intpairfunc.undefined)
     in (a11,v')::diagonalize n (i + 1) m' 
     end
  end
in
fun diag m =
 let 
   val nn = dimensions m 
   val n = fst nn 
 in if snd nn <> n then error "diagonalize: non-square matrix" 
    else diagonalize n 1 m
 end
end;

fun gcd_rat a b = Rat.rat_of_int (Integer.gcd (int_of_rat a) (int_of_rat b));

(* Adjust a diagonalization to collect rationals at the start.               *)
  (* FIXME : Potentially polymorphic keys, but here only: integers!! *)
local
 fun upd0 x y a = if y =/ rat_0 then a else Intfunc.update(x,y) a;
 fun mapa f (d,v) = 
  (d, Intfunc.fold (fn (i,c) => fn a => upd0 i (f c) a) v Intfunc.undefined)
 fun adj (c,l) =
 let val a = 
  Intfunc.fold (fn (i,c) => fn a => lcm_rat a (denominator_rat c)) 
    (snd l) rat_1 //
  Intfunc.fold (fn (i,c) => fn a => gcd_rat a (numerator_rat c)) 
    (snd l) rat_0
  in ((c // (a */ a)),mapa (fn x => a */ x) l)
  end
in
fun deration d = if null d then (rat_0,d) else
 let val d' = map adj d
     val a = fold (lcm_rat o denominator_rat o fst) d' rat_1 //
          fold (gcd_rat o numerator_rat o fst) d' rat_0 
 in ((rat_1 // a),map (fn (c,l) => (a */ c,l)) d')
 end
end;
 
(* Enumeration of monomials with given multidegree bound.                    *)

fun enumerate_monomials d vars = 
 if d < 0 then []
 else if d = 0 then [Ctermfunc.undefined]
 else if null vars then [monomial_1] else
 let val alts =
  map (fn k => let val oths = enumerate_monomials (d - k) (tl vars) 
               in map (fn ks => if k = 0 then ks else Ctermfunc.update (hd vars, k) ks) oths end) (0 upto d) 
 in fold1 (curry op @) alts
 end;

(* Enumerate products of distinct input polys with degree <= d.              *)
(* We ignore any constant input polynomials.                                 *)
(* Give the output polynomial and a record of how it was derived.            *)

local
 open RealArith
in
fun enumerate_products d pols =
if d = 0 then [(poly_const rat_1,Rational_lt rat_1)] 
else if d < 0 then [] else
case pols of 
   [] => [(poly_const rat_1,Rational_lt rat_1)]
 | (p,b)::ps => 
    let val e = multidegree p 
    in if e = 0 then enumerate_products d ps else
       enumerate_products d ps @
       map (fn (q,c) => (poly_mul p q,Product(b,c)))
         (enumerate_products (d - e) ps)
    end
end;

(* Convert regular polynomial. Note that we treat (0,0,0) as -1.             *)

fun epoly_of_poly p =
  Monomialfunc.fold (fn (m,c) => fn a => Monomialfunc.update (m, Inttriplefunc.onefunc ((0,0,0), Rat.neg c)) a) p Monomialfunc.undefined;

(* String for block diagonal matrix numbered k.                              *)

fun sdpa_of_blockdiagonal k m =
 let 
  val pfx = string_of_int k ^" "
  val ents =
    Inttriplefunc.fold 
      (fn ((b,i,j),c) => fn a => if i > j then a else ((b,i,j),c)::a) 
      m [] 
  val entss = sort (increasing fst triple_int_ord) ents 
 in fold_rev (fn ((b,i,j),c) => fn a =>
     pfx ^ string_of_int b ^ " " ^ string_of_int i ^ " " ^ string_of_int j ^
     " " ^ decimalize 20 c ^ "\n" ^ a) entss ""
 end;

(* SDPA for problem using block diagonal (i.e. multiple SDPs)                *)

fun sdpa_of_blockproblem comment nblocks blocksizes obj mats =
 let val m = length mats - 1 
 in  "\"" ^ comment ^ "\"\n" ^
  string_of_int m ^ "\n" ^
  string_of_int nblocks ^ "\n" ^
  (fold1 (fn s => fn t => s^" "^t) (map string_of_int blocksizes)) ^
  "\n" ^
  sdpa_of_vector obj ^
  fold_rev2 (fn k => fn m => fn a => sdpa_of_blockdiagonal (k - 1) m ^ a)
    (1 upto length mats) mats ""
 end;

(* Hence run CSDP on a problem in block diagonal form.                       *)

fun run_csdp dbg nblocks blocksizes obj mats =
 let 
  val input_file = tmp_file "sos" ".dat-s" 
  val output_file = tmp_file "sos" ".out"
  val params_file = tmp_file "param" ".csdp" 
  val _ = File.write input_file
   (sdpa_of_blockproblem "" nblocks blocksizes obj mats)
  val _ = File.write params_file csdp_params
  val current_dir = File.pwd()
  val _ = File.cd (Path.variable "ISABELLE_TMP")
  val rv = system ("csdp "^(Path.implode input_file) ^ " " 
                   ^ (Path.implode output_file) ^
                   (if dbg then "" else "> /dev/null"))
  val  opr = File.read output_file 
  val res = parse_csdpoutput opr 
 in
   ((if dbg then ()
     else (File.rm input_file ; File.rm output_file ; File.cd current_dir));
    (rv,res))
 end;

fun csdp nblocks blocksizes obj mats =
 let 
  val (rv,res) = run_csdp (!debugging) nblocks blocksizes obj mats 
 in ((if rv = 1 orelse rv = 2 then error "csdp: Problem is infeasible"
     else if rv = 3 then writeln "csdp warning: Reduced accuracy"
     else if rv <> 0 then error ("csdp: error "^string_of_int rv)
     else ());
     res)
 end;

(* 3D versions of matrix operations to consider blocks separately.           *)

val bmatrix_add = Inttriplefunc.combine (curry op +/) (fn x => x =/ rat_0);
fun bmatrix_cmul c bm =
  if c =/ rat_0 then Inttriplefunc.undefined
  else Inttriplefunc.mapf (fn x => c */ x) bm;

val bmatrix_neg = bmatrix_cmul (Rat.rat_of_int ~1);
fun bmatrix_sub m1 m2 = bmatrix_add m1 (bmatrix_neg m2);;

(* Smash a block matrix into components.                                     *)

fun blocks blocksizes bm =
 map (fn (bs,b0) =>
      let val m = Inttriplefunc.fold
          (fn ((b,i,j),c) => fn a => if b = b0 then Intpairfunc.update ((i,j),c) a else a) bm Intpairfunc.undefined
          val d = Intpairfunc.fold (fn ((i,j),c) => fn a => max a (max i j)) m 0 
      in (((bs,bs),m):matrix) end)
 (blocksizes ~~ (1 upto length blocksizes));;

(* FIXME : Get rid of this !!!*)
fun tryfind f [] = error "tryfind"
  | tryfind f (x::xs) = (f x handle ERROR _ => tryfind f xs);


(* Positiv- and Nullstellensatz. Flag "linf" forces a linear representation. *)


local
 open RealArith
in
fun real_positivnullstellensatz_general linf d eqs leqs pol =
let 
 val vars = fold_rev (curry (gen_union (op aconvc)) o poly_variables) 
              (pol::eqs @ map fst leqs) []
 val monoid = if linf then 
      (poly_const rat_1,Rational_lt rat_1)::
      (filter (fn (p,c) => multidegree p <= d) leqs)
    else enumerate_products d leqs
 val nblocks = length monoid
 fun mk_idmultiplier k p =
  let 
   val e = d - multidegree p
   val mons = enumerate_monomials e vars
   val nons = mons ~~ (1 upto length mons) 
  in (mons,
      fold_rev (fn (m,n) => Monomialfunc.update(m,Inttriplefunc.onefunc((~k,~n,n),rat_1))) nons Monomialfunc.undefined)
  end

 fun mk_sqmultiplier k (p,c) =
  let 
   val e = (d - multidegree p) div 2
   val mons = enumerate_monomials e vars
   val nons = mons ~~ (1 upto length mons) 
  in (mons, 
      fold_rev (fn (m1,n1) =>
       fold_rev (fn (m2,n2) => fn  a =>
        let val m = monomial_mul m1 m2 
        in if n1 > n2 then a else
          let val c = if n1 = n2 then rat_1 else rat_2
              val e = Monomialfunc.tryapplyd a m Inttriplefunc.undefined 
          in Monomialfunc.update(m, tri_equation_add (Inttriplefunc.onefunc((k,n1,n2), c)) e) a
          end
        end)  nons)
       nons Monomialfunc.undefined)
  end

  val (sqmonlist,sqs) = split_list (map2 mk_sqmultiplier (1 upto length monoid) monoid)
  val (idmonlist,ids) =  split_list(map2 mk_idmultiplier (1 upto length eqs) eqs)
  val blocksizes = map length sqmonlist
  val bigsum =
    fold_rev2 (fn p => fn q => fn a => tri_epoly_pmul p q a) eqs ids
            (fold_rev2 (fn (p,c) => fn s => fn a => tri_epoly_pmul p s a) monoid sqs
                     (epoly_of_poly(poly_neg pol)))
  val eqns = Monomialfunc.fold (fn (m,e) => fn a => e::a) bigsum []
  val (pvs,assig) = tri_eliminate_all_equations (0,0,0) eqns
  val qvars = (0,0,0)::pvs
  val allassig = fold_rev (fn v => Inttriplefunc.update(v,(Inttriplefunc.onefunc(v,rat_1)))) pvs assig
  fun mk_matrix v =
    Inttriplefunc.fold (fn ((b,i,j), ass) => fn m => 
        if b < 0 then m else
         let val c = Inttriplefunc.tryapplyd ass v rat_0
         in if c = rat_0 then m else
            Inttriplefunc.update ((b,j,i), c) (Inttriplefunc.update ((b,i,j), c) m)
         end)
          allassig Inttriplefunc.undefined
  val diagents = Inttriplefunc.fold
    (fn ((b,i,j), e) => fn a => if b > 0 andalso i = j then tri_equation_add e a else a)
    allassig Inttriplefunc.undefined

  val mats = map mk_matrix qvars
  val obj = (length pvs,
            itern 1 pvs (fn v => fn i => Intfunc.updatep iszero (i,Inttriplefunc.tryapplyd diagents v rat_0))
                        Intfunc.undefined)
  val raw_vec = if null pvs then vector_0 0
                else tri_scale_then (csdp nblocks blocksizes) obj mats
  fun int_element (d,v) i = Intfunc.tryapplyd v i rat_0
  fun cterm_element (d,v) i = Ctermfunc.tryapplyd v i rat_0

  fun find_rounding d =
   let 
    val _ = if !debugging 
          then writeln ("Trying rounding with limit "^Rat.string_of_rat d ^ "\n") 
          else ()
    val vec = nice_vector d raw_vec
    val blockmat = iter (1,dim vec)
     (fn i => fn a => bmatrix_add (bmatrix_cmul (int_element vec i) (nth mats i)) a)
     (bmatrix_neg (nth mats 0))
    val allmats = blocks blocksizes blockmat 
   in (vec,map diag allmats)
   end
  val (vec,ratdias) =
    if null pvs then find_rounding rat_1
    else tryfind find_rounding (map Rat.rat_of_int (1 upto 31) @
                                map pow2 (5 upto 66))
  val newassigs =
    fold_rev (fn k => Inttriplefunc.update (nth pvs (k - 1), int_element vec k))
           (1 upto dim vec) (Inttriplefunc.onefunc ((0,0,0), Rat.rat_of_int ~1))
  val finalassigs =
    Inttriplefunc.fold (fn (v,e) => fn a => Inttriplefunc.update(v, tri_equation_eval newassigs e) a) allassig newassigs
  fun poly_of_epoly p =
    Monomialfunc.fold (fn (v,e) => fn a => Monomialfunc.updatep iszero (v,tri_equation_eval finalassigs e) a)
          p Monomialfunc.undefined
  fun  mk_sos mons =
   let fun mk_sq (c,m) =
    (c,fold_rev (fn k=> fn a => Monomialfunc.updatep iszero (nth mons (k - 1), int_element m k) a)
                 (1 upto length mons) Monomialfunc.undefined)
   in map mk_sq
   end
  val sqs = map2 mk_sos sqmonlist ratdias
  val cfs = map poly_of_epoly ids
  val msq = filter (fn (a,b) => not (null b)) (map2 pair monoid sqs)
  fun eval_sq sqs = fold_rev (fn (c,q) => poly_add (poly_cmul c (poly_mul q q))) sqs poly_0
  val sanity =
    fold_rev (fn ((p,c),s) => poly_add (poly_mul p (eval_sq s))) msq
           (fold_rev2 (fn p => fn q => poly_add (poly_mul p q)) cfs eqs
                    (poly_neg pol))

in if not(Monomialfunc.is_undefined sanity) then raise Sanity else
  (cfs,map (fn (a,b) => (snd a,b)) msq)
 end


end;

(* Iterative deepening.                                                      *)

fun deepen f n = 
  (writeln ("Searching with depth limit " ^ string_of_int n) ; (f n handle ERROR s => (writeln ("failed with message: " ^ s) ; deepen f (n+1))))

(* The ordering so we can create canonical HOL polynomials.                  *)

fun dest_monomial mon = sort (increasing fst cterm_ord) (Ctermfunc.graph mon);

fun monomial_order (m1,m2) =
 if Ctermfunc.is_undefined m2 then LESS 
 else if Ctermfunc.is_undefined m1 then GREATER 
 else
  let val mon1 = dest_monomial m1 
      val mon2 = dest_monomial m2
      val deg1 = fold (curry op + o snd) mon1 0
      val deg2 = fold (curry op + o snd) mon2 0 
  in if deg1 < deg2 then GREATER else if deg1 > deg2 then LESS
     else list_ord (prod_ord cterm_ord int_ord) (mon1,mon2)
  end;

fun dest_poly p =
  map (fn (m,c) => (c,dest_monomial m))
      (sort (prod_ord monomial_order (K EQUAL)) (Monomialfunc.graph p));

(* Map back polynomials and their composites to HOL.                         *)

local
 open Thm Numeral RealArith
in

fun cterm_of_varpow x k = if k = 1 then x else capply (capply @{cterm "op ^ :: real => _"} x) 
  (mk_cnumber @{ctyp nat} k)

fun cterm_of_monomial m = 
 if Ctermfunc.is_undefined m then @{cterm "1::real"} 
 else 
  let 
   val m' = dest_monomial m
   val vps = fold_rev (fn (x,k) => cons (cterm_of_varpow x k)) m' [] 
  in fold1 (fn s => fn t => capply (capply @{cterm "op * :: real => _"} s) t) vps
  end

fun cterm_of_cmonomial (m,c) = if Ctermfunc.is_undefined m then cterm_of_rat c
    else if c = Rat.one then cterm_of_monomial m
    else capply (capply @{cterm "op *::real => _"} (cterm_of_rat c)) (cterm_of_monomial m);

fun cterm_of_poly p = 
 if Monomialfunc.is_undefined p then @{cterm "0::real"} 
 else
  let 
   val cms = map cterm_of_cmonomial
     (sort (prod_ord monomial_order (K EQUAL)) (Monomialfunc.graph p))
  in fold1 (fn t1 => fn t2 => capply(capply @{cterm "op + :: real => _"} t1) t2) cms
  end;

fun cterm_of_sqterm (c,p) = Product(Rational_lt c,Square(cterm_of_poly p));

fun cterm_of_sos (pr,sqs) = if null sqs then pr
  else Product(pr,fold1 (fn a => fn b => Sum(a,b)) (map cterm_of_sqterm sqs));

end

(* Interface to HOL.                                                         *)
local
  open Thm Conv RealArith
  val concl = dest_arg o cprop_of
  fun simple_cterm_ord t u = TermOrd.fast_term_ord (term_of t, term_of u) = LESS
in
  (* FIXME: Replace tryfind by get_first !! *)
fun real_nonlinear_prover ctxt =
 let 
  val {add,mul,neg,pow,sub,main} =  Normalizer.semiring_normalizers_ord_wrapper ctxt
      (valOf (NormalizerData.match ctxt @{cterm "(0::real) + 1"})) 
     simple_cterm_ord
  val (real_poly_add_conv,real_poly_mul_conv,real_poly_neg_conv,
       real_poly_pow_conv,real_poly_sub_conv,real_poly_conv) = (add,mul,neg,pow,sub,main)
  fun mainf  translator (eqs,les,lts) = 
  let 
   val eq0 = map (poly_of_term o dest_arg1 o concl) eqs
   val le0 = map (poly_of_term o dest_arg o concl) les
   val lt0 = map (poly_of_term o dest_arg o concl) lts
   val eqp0 = map (fn (t,i) => (t,Axiom_eq i)) (eq0 ~~ (0 upto (length eq0 - 1)))
   val lep0 = map (fn (t,i) => (t,Axiom_le i)) (le0 ~~ (0 upto (length le0 - 1)))
   val ltp0 = map (fn (t,i) => (t,Axiom_lt i)) (lt0 ~~ (0 upto (length lt0 - 1)))
   val (keq,eq) = List.partition (fn (p,_) => multidegree p = 0) eqp0
   val (klep,lep) = List.partition (fn (p,_) => multidegree p = 0) lep0
   val (kltp,ltp) = List.partition (fn (p,_) => multidegree p = 0) ltp0
   fun trivial_axiom (p,ax) =
    case ax of
       Axiom_eq n => if eval Ctermfunc.undefined p <>/ Rat.zero then nth eqs n 
                     else error "trivial_axiom: Not a trivial axiom"
     | Axiom_le n => if eval Ctermfunc.undefined p </ Rat.zero then nth les n 
                     else error "trivial_axiom: Not a trivial axiom"
     | Axiom_lt n => if eval Ctermfunc.undefined p <=/ Rat.zero then nth lts n 
                     else error "trivial_axiom: Not a trivial axiom"
     | _ => error "trivial_axiom: Not a trivial axiom"
   in 
  ((let val th = tryfind trivial_axiom (keq @ klep @ kltp)
   in fconv_rule (arg_conv (arg1_conv real_poly_conv) then_conv field_comp_conv) th end)
   handle ERROR _ => (
    let 
     val pol = fold_rev poly_mul (map fst ltp) (poly_const Rat.one)
     val leq = lep @ ltp
     fun tryall d =
      let val e = multidegree pol
          val k = if e = 0 then 0 else d div e
          val eq' = map fst eq 
      in tryfind (fn i => (d,i,real_positivnullstellensatz_general false d eq' leq
                            (poly_neg(poly_pow pol i))))
              (0 upto k)
      end
    val (d,i,(cert_ideal,cert_cone)) = deepen tryall 0
    val proofs_ideal =
      map2 (fn q => fn (p,ax) => Eqmul(cterm_of_poly q,ax)) cert_ideal eq
    val proofs_cone = map cterm_of_sos cert_cone
    val proof_ne = if null ltp then Rational_lt Rat.one else
      let val p = fold1 (fn s => fn t => Product(s,t)) (map snd ltp) 
      in  funpow i (fn q => Product(p,q)) (Rational_lt Rat.one)
      end
    val proof = fold1 (fn s => fn t => Sum(s,t))
                           (proof_ne :: proofs_ideal @ proofs_cone) 
    in writeln "Translating proof certificate to HOL";
       translator (eqs,les,lts) proof
    end))
   end
 in mainf end
end

fun C f x y = f y x;
  (* FIXME : This is very bad!!!*)
fun subst_conv eqs t = 
 let 
  val t' = fold (Thm.cabs o Thm.lhs_of) eqs t
 in Conv.fconv_rule (Thm.beta_conversion true) (fold (C combination) eqs (reflexive t'))
 end

(* A wrapper that tries to substitute away variables first.                  *)

local
 open Thm Conv RealArith
  fun simple_cterm_ord t u = TermOrd.fast_term_ord (term_of t, term_of u) = LESS
 val concl = dest_arg o cprop_of
 val shuffle1 = 
   fconv_rule (rewr_conv @{lemma "(a + x == y) == (x == y - (a::real))" by (atomize (full)) (simp add: ring_simps) })
 val shuffle2 =
    fconv_rule (rewr_conv @{lemma "(x + a == y) ==  (x == y - (a::real))" by (atomize (full)) (simp add: ring_simps)})
 fun substitutable_monomial fvs tm = case term_of tm of
    Free(_,@{typ real}) => if not (member (op aconvc) fvs tm) then (Rat.one,tm) 
                           else error "substitutable_monomial"
  | @{term "op * :: real => _"}$c$(t as Free _ ) => 
     if is_ratconst (dest_arg1 tm) andalso not (member (op aconvc) fvs (dest_arg tm))
         then (dest_ratconst (dest_arg1 tm),dest_arg tm) else error "substitutable_monomial"
  | @{term "op + :: real => _"}$s$t => 
       (substitutable_monomial (add_cterm_frees (dest_arg tm) fvs) (dest_arg1 tm)
        handle ERROR _ => substitutable_monomial (add_cterm_frees (dest_arg1 tm) fvs) (dest_arg tm))
  | _ => error "substitutable_monomial"

  fun isolate_variable v th = 
   let val w = dest_arg1 (cprop_of th)
   in if v aconvc w then th
      else case term_of w of
           @{term "op + :: real => _"}$s$t => 
              if dest_arg1 w aconvc v then shuffle2 th 
              else isolate_variable v (shuffle1 th)
          | _ => error "isolate variable : This should not happen?"
   end 
in

fun real_nonlinear_subst_prover ctxt =
 let 
  val {add,mul,neg,pow,sub,main} =  Normalizer.semiring_normalizers_ord_wrapper ctxt
      (valOf (NormalizerData.match ctxt @{cterm "(0::real) + 1"})) 
     simple_cterm_ord

  val (real_poly_add_conv,real_poly_mul_conv,real_poly_neg_conv,
       real_poly_pow_conv,real_poly_sub_conv,real_poly_conv) = (add,mul,neg,pow,sub,main)

  fun make_substitution th =
   let 
    val (c,v) = substitutable_monomial [] (dest_arg1(concl th))
    val th1 = Drule.arg_cong_rule (capply @{cterm "op * :: real => _"} (cterm_of_rat (Rat.inv c))) (mk_meta_eq th)
    val th2 = fconv_rule (binop_conv real_poly_mul_conv) th1
   in fconv_rule (arg_conv real_poly_conv) (isolate_variable v th2)
   end
   fun oprconv cv ct = 
    let val g = Thm.dest_fun2 ct
    in if g aconvc @{cterm "op <= :: real => _"} 
         orelse g aconvc @{cterm "op < :: real => _"} 
       then arg_conv cv ct else arg1_conv cv ct
    end
  fun mainf translator =
   let 
    fun substfirst(eqs,les,lts) =
      ((let 
           val eth = tryfind make_substitution eqs
           val modify = fconv_rule (arg_conv (oprconv(subst_conv [eth] then_conv real_poly_conv)))
       in  substfirst
             (filter_out (fn t => (Thm.dest_arg1 o Thm.dest_arg o cprop_of) t 
                                   aconvc @{cterm "0::real"}) (map modify eqs),
                                   map modify les,map modify lts)
       end)
       handle ERROR  _ => real_nonlinear_prover ctxt translator (rev eqs, rev les, rev lts))
    in substfirst
   end


 in mainf
 end

(* Overall function. *)

fun real_sos ctxt t = gen_prover_real_arith ctxt (real_nonlinear_subst_prover ctxt) t;
end;

end;
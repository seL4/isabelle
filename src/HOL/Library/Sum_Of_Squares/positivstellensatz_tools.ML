(* Title:      positivstellensatz_tools.ML
   Author:     Philipp Meyer, TU Muenchen

Functions for generating a certificate from a positivstellensatz and vice versa
*)

signature POSITIVSTELLENSATZ_TOOLS =
sig
  val pss_tree_to_cert : RealArith.pss_tree -> string

  val cert_to_pss_tree : Proof.context -> string -> RealArith.pss_tree
end


structure PositivstellensatzTools : POSITIVSTELLENSATZ_TOOLS =
struct

(*** certificate generation ***)

fun string_of_rat r =
  let
    val (nom, den) = Rat.quotient_of_rat r
  in
    if den = 1 then string_of_int nom
    else string_of_int nom ^ "/" ^ string_of_int den
  end

(* map polynomials to strings *)

fun string_of_varpow x k =
  let
    val term = term_of x
    val name = case term of
      Free (n, _) => n
    | _ => error "Term in monomial not free variable"
  in
    if k = 1 then name else name ^ "^" ^ string_of_int k 
  end

fun string_of_monomial m = 
 if FuncUtil.Ctermfunc.is_empty m then "1" 
 else 
  let 
   val m' = FuncUtil.dest_monomial m
   val vps = fold_rev (fn (x,k) => cons (string_of_varpow x k)) m' [] 
  in foldr1 (fn (s, t) => s ^ "*" ^ t) vps
  end

fun string_of_cmonomial (m,c) =
  if FuncUtil.Ctermfunc.is_empty m then string_of_rat c
  else if c = Rat.one then string_of_monomial m
  else (string_of_rat c) ^ "*" ^ (string_of_monomial m);

fun string_of_poly p = 
 if FuncUtil.Monomialfunc.is_empty p then "0" 
 else
  let 
   val cms = map string_of_cmonomial
     (sort (prod_ord FuncUtil.monomial_order (K EQUAL)) (FuncUtil.Monomialfunc.dest p))
  in foldr1 (fn (t1, t2) => t1 ^ " + " ^ t2) cms
  end;

fun pss_to_cert (RealArith.Axiom_eq i) = "A=" ^ string_of_int i
  | pss_to_cert (RealArith.Axiom_le i) = "A<=" ^ string_of_int i
  | pss_to_cert (RealArith.Axiom_lt i) = "A<" ^ string_of_int i
  | pss_to_cert (RealArith.Rational_eq r) = "R=" ^ string_of_rat r
  | pss_to_cert (RealArith.Rational_le r) = "R<=" ^ string_of_rat r
  | pss_to_cert (RealArith.Rational_lt r) = "R<" ^ string_of_rat r
  | pss_to_cert (RealArith.Square p) = "[" ^ string_of_poly p ^ "]^2"
  | pss_to_cert (RealArith.Eqmul (p, pss)) = "([" ^ string_of_poly p ^ "] * " ^ pss_to_cert pss ^ ")"
  | pss_to_cert (RealArith.Sum (pss1, pss2)) = "(" ^ pss_to_cert pss1 ^ " + " ^ pss_to_cert pss2 ^ ")"
  | pss_to_cert (RealArith.Product (pss1, pss2)) = "(" ^ pss_to_cert pss1 ^ " * " ^ pss_to_cert pss2 ^ ")"

fun pss_tree_to_cert RealArith.Trivial = "()"
  | pss_tree_to_cert (RealArith.Cert pss) = "(" ^ pss_to_cert pss ^ ")"
  | pss_tree_to_cert (RealArith.Branch (t1, t2)) = "(" ^ pss_tree_to_cert t1 ^ " & " ^ pss_tree_to_cert t2 ^ ")"

(*** certificate parsing ***)

(* basic parser *)

val str = Scan.this_string

val number = Scan.repeat1 (Scan.one Symbol.is_ascii_digit >>
  (fn s => ord s - ord "0")) >>
  foldl1 (fn (n, d) => n * 10 + d)

val nat = number
val int = Scan.optional (str "~" >> K ~1) 1 -- nat >> op *;
val rat = int --| str "/" -- int >> Rat.rat_of_quotient
val rat_int = rat || int >> Rat.rat_of_int

(* polynomial parser *)

fun repeat_sep s f = f ::: Scan.repeat (str s |-- f)

val parse_id = Scan.one Symbol.is_letter ::: Scan.many Symbol.is_letdig >> implode

fun parse_varpow ctxt = parse_id -- Scan.optional (str "^" |-- nat) 1 >>
  (fn (x, k) => (cterm_of (ProofContext.theory_of ctxt) (Free (x, @{typ real})), k)) 

fun parse_monomial ctxt = repeat_sep "*" (parse_varpow ctxt) >>
  List.foldl (uncurry FuncUtil.Ctermfunc.update) FuncUtil.Ctermfunc.empty

fun parse_cmonomial ctxt =
  rat_int --| str "*" -- (parse_monomial ctxt) >> swap ||
  (parse_monomial ctxt) >> (fn m => (m, Rat.one)) ||
  rat_int >> (fn r => (FuncUtil.Ctermfunc.empty, r))

fun parse_poly ctxt = repeat_sep "+" (parse_cmonomial ctxt) >>
  List.foldl (uncurry FuncUtil.Monomialfunc.update) FuncUtil.Monomialfunc.empty

(* positivstellensatz parser *)

val parse_axiom =
  (str "A=" |-- int >> RealArith.Axiom_eq) ||
  (str "A<=" |-- int >> RealArith.Axiom_le) ||
  (str "A<" |-- int >> RealArith.Axiom_lt)

val parse_rational =
  (str "R=" |-- rat_int >> RealArith.Rational_eq) ||
  (str "R<=" |-- rat_int >> RealArith.Rational_le) ||
  (str "R<" |-- rat_int >> RealArith.Rational_lt)

fun parse_cert ctxt input =
  let
    val pc = parse_cert ctxt
    val pp = parse_poly ctxt
  in
  (parse_axiom ||
   parse_rational ||
   str "[" |-- pp --| str "]^2" >> RealArith.Square ||
   str "([" |-- pp --| str "]*" -- pc --| str ")" >> RealArith.Eqmul ||
   str "(" |-- pc --| str "*" -- pc --| str ")" >> RealArith.Product ||
   str "(" |-- pc --| str "+" -- pc --| str ")" >> RealArith.Sum) input
  end

fun parse_cert_tree ctxt input =
  let
    val pc = parse_cert ctxt
    val pt = parse_cert_tree ctxt
  in
  (str "()" >> K RealArith.Trivial ||
   str "(" |-- pc --| str ")" >> RealArith.Cert ||
   str "(" |-- pt --| str "&" -- pt --| str ")" >> RealArith.Branch) input
  end

(* scanner *)

fun cert_to_pss_tree ctxt input_str = Symbol.scanner "bad certificate" (parse_cert_tree ctxt)
  (filter_out Symbol.is_blank (Symbol.explode input_str))

end



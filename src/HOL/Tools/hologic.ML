(*  Title:      HOL/Tools/hologic.ML
    Author:     Lawrence C Paulson and Markus Wenzel

Abstract syntax operations for HOL.
*)

signature HOLOGIC =
sig
  val typeS: sort
  val typeT: typ
  val id_const: typ -> term
  val mk_comp: term * term -> term
  val boolN: string
  val boolT: typ
  val Trueprop: term
  val mk_Trueprop: term -> term
  val dest_Trueprop: term -> term
  val mk_induct_forall: typ -> term
  val mk_setT: typ -> typ
  val dest_setT: typ -> typ
  val Collect_const: typ -> term
  val mk_Collect: string * typ * term -> term
  val mk_mem: term * term -> term
  val dest_mem: term -> term * term
  val mk_set: typ -> term list -> term
  val dest_set: term -> term list
  val mk_UNIV: typ -> term
  val conj_intr: thm -> thm -> thm
  val conj_elim: thm -> thm * thm
  val conj_elims: thm -> thm list
  val conj: term
  val disj: term
  val imp: term
  val Not: term
  val mk_conj: term * term -> term
  val mk_disj: term * term -> term
  val mk_imp: term * term -> term
  val mk_not: term -> term
  val dest_conj: term -> term list
  val dest_disj: term -> term list
  val disjuncts: term -> term list
  val dest_imp: term -> term * term
  val dest_not: term -> term
  val eq_const: typ -> term
  val mk_eq: term * term -> term
  val dest_eq: term -> term * term
  val all_const: typ -> term
  val mk_all: string * typ * term -> term
  val list_all: (string * typ) list * term -> term
  val exists_const: typ -> term
  val mk_exists: string * typ * term -> term
  val choice_const: typ -> term
  val class_equal: string
  val mk_binop: string -> term * term -> term
  val mk_binrel: string -> term * term -> term
  val dest_bin: string -> typ -> term -> term * term
  val unitT: typ
  val is_unitT: typ -> bool
  val unit: term
  val is_unit: term -> bool
  val mk_prodT: typ * typ -> typ
  val dest_prodT: typ -> typ * typ
  val pair_const: typ -> typ -> term
  val mk_prod: term * term -> term
  val dest_prod: term -> term * term
  val mk_fst: term -> term
  val mk_snd: term -> term
  val split_const: typ * typ * typ -> term
  val mk_split: term -> term
  val flatten_tupleT: typ -> typ list
  val tupled_lambda: term -> term -> term
  val mk_tupleT: typ list -> typ
  val strip_tupleT: typ -> typ list
  val mk_tuple: term list -> term
  val strip_tuple: term -> term list
  val mk_ptupleT: int list list -> typ list -> typ
  val strip_ptupleT: int list list -> typ -> typ list
  val flat_tupleT_paths: typ -> int list list
  val mk_ptuple: int list list -> typ -> term list -> term
  val strip_ptuple: int list list -> term -> term list
  val flat_tuple_paths: term -> int list list
  val mk_psplits: int list list -> typ -> typ -> term -> term
  val strip_psplits: term -> term * typ list * int list list
  val natT: typ
  val zero: term
  val is_zero: term -> bool
  val mk_Suc: term -> term
  val dest_Suc: term -> term
  val Suc_zero: term
  val mk_nat: int -> term
  val dest_nat: term -> int
  val class_size: string
  val size_const: typ -> term
  val code_numeralT: typ
  val intT: typ
  val pls_const: term
  val min_const: term
  val bit0_const: term
  val bit1_const: term
  val mk_bit: int -> term
  val dest_bit: term -> int
  val mk_numeral: int -> term
  val dest_numeral: term -> int
  val number_of_const: typ -> term
  val add_numerals: term -> (term * typ) list -> (term * typ) list
  val mk_number: typ -> int -> term
  val dest_number: term -> typ * int
  val realT: typ
  val nibbleT: typ
  val mk_nibble: int -> term
  val dest_nibble: term -> int
  val charT: typ
  val mk_char: int -> term
  val dest_char: term -> int
  val listT: typ -> typ
  val nil_const: typ -> term
  val cons_const: typ -> term
  val mk_list: typ -> term list -> term
  val dest_list: term -> term list
  val stringT: typ
  val mk_string: string -> term
  val dest_string: term -> string
  val literalT: typ
  val mk_literal: string -> term
  val dest_literal: term -> string
  val mk_typerep: typ -> term
  val termT: typ
  val term_of_const: typ -> term
  val mk_term_of: typ -> term -> term
  val reflect_term: term -> term
  val mk_valtermify_app: string -> (string * typ) list -> typ -> term
  val mk_return: typ -> typ -> term -> term
  val mk_ST: ((term * typ) * (string * typ) option)  list -> term -> typ -> typ option * typ -> term
  val mk_random: typ -> term -> term
end;

structure HOLogic: HOLOGIC =
struct

(* HOL syntax *)

val typeS: sort = ["HOL.type"];
val typeT = Type_Infer.anyT typeS;


(* functions *)

fun id_const T = Const ("Fun.id", T --> T);

fun mk_comp (f, g) =
  let
    val fT = fastype_of f;
    val gT = fastype_of g;
    val compT = fT --> gT --> domain_type gT --> range_type fT;
  in Const ("Fun.comp", compT) $ f $ g end;


(* bool and set *)

val boolN = "HOL.bool";
val boolT = Type (boolN, []);

fun mk_induct_forall T = Const ("HOL.induct_forall", (T --> boolT) --> boolT);

fun mk_setT T = Type ("Set.set", [T]);

fun dest_setT (Type ("Set.set", [T])) = T
  | dest_setT T = raise TYPE ("dest_setT: set type expected", [T], []);

fun mk_set T ts =
  let
    val sT = mk_setT T;
    val empty = Const ("Orderings.bot_class.bot", sT);
    fun insert t u = Const ("Set.insert", T --> sT --> sT) $ t $ u;
  in fold_rev insert ts empty end;

fun mk_UNIV T = Const ("Orderings.top_class.top", mk_setT T);

fun dest_set (Const ("Orderings.bot_class.bot", _)) = []
  | dest_set (Const ("Set.insert", _) $ t $ u) = t :: dest_set u
  | dest_set t = raise TERM ("dest_set", [t]);

fun Collect_const T = Const ("Set.Collect", (T --> boolT) --> mk_setT T);
fun mk_Collect (a, T, t) = Collect_const T $ absfree (a, T) t;

fun mk_mem (x, A) =
  let val setT = fastype_of A in
    Const ("Set.member", dest_setT setT --> setT --> boolT) $ x $ A
  end;

fun dest_mem (Const ("Set.member", _) $ x $ A) = (x, A)
  | dest_mem t = raise TERM ("dest_mem", [t]);


(* logic *)

val Trueprop = Const ("HOL.Trueprop", boolT --> propT);

fun mk_Trueprop P = Trueprop $ P;

fun dest_Trueprop (Const ("HOL.Trueprop", _) $ P) = P
  | dest_Trueprop t = raise TERM ("dest_Trueprop", [t]);

fun conj_intr thP thQ =
  let
    val (P, Q) = pairself (Object_Logic.dest_judgment o Thm.cprop_of) (thP, thQ)
      handle CTERM (msg, _) => raise THM (msg, 0, [thP, thQ]);
    val inst = Thm.instantiate ([], [(@{cpat "?P::bool"}, P), (@{cpat "?Q::bool"}, Q)]);
  in Drule.implies_elim_list (inst @{thm conjI}) [thP, thQ] end;

fun conj_elim thPQ =
  let
    val (P, Q) = Thm.dest_binop (Object_Logic.dest_judgment (Thm.cprop_of thPQ))
      handle CTERM (msg, _) => raise THM (msg, 0, [thPQ]);
    val inst = Thm.instantiate ([], [(@{cpat "?P::bool"}, P), (@{cpat "?Q::bool"}, Q)]);
    val thP = Thm.implies_elim (inst @{thm conjunct1}) thPQ;
    val thQ = Thm.implies_elim (inst @{thm conjunct2}) thPQ;
  in (thP, thQ) end;

fun conj_elims th =
  let val (th1, th2) = conj_elim th
  in conj_elims th1 @ conj_elims th2 end handle THM _ => [th];

val conj = @{term HOL.conj}
and disj = @{term HOL.disj}
and imp = @{term implies}
and Not = @{term Not};

fun mk_conj (t1, t2) = conj $ t1 $ t2
and mk_disj (t1, t2) = disj $ t1 $ t2
and mk_imp (t1, t2) = imp $ t1 $ t2
and mk_not t = Not $ t;

fun dest_conj (Const ("HOL.conj", _) $ t $ t') = t :: dest_conj t'
  | dest_conj t = [t];

fun dest_disj (Const ("HOL.disj", _) $ t $ t') = t :: dest_disj t'
  | dest_disj t = [t];

(*Like dest_disj, but flattens disjunctions however nested*)
fun disjuncts_aux (Const ("HOL.disj", _) $ t $ t') disjs = disjuncts_aux t (disjuncts_aux t' disjs)
  | disjuncts_aux t disjs = t::disjs;

fun disjuncts t = disjuncts_aux t [];

fun dest_imp (Const ("HOL.implies", _) $ A $ B) = (A, B)
  | dest_imp  t = raise TERM ("dest_imp", [t]);

fun dest_not (Const ("HOL.Not", _) $ t) = t
  | dest_not t = raise TERM ("dest_not", [t]);

fun eq_const T = Const ("HOL.eq", T --> T --> boolT);
fun mk_eq (t, u) = eq_const (fastype_of t) $ t $ u;

fun dest_eq (Const ("HOL.eq", _) $ lhs $ rhs) = (lhs, rhs)
  | dest_eq t = raise TERM ("dest_eq", [t])

fun all_const T = Const ("HOL.All", [T --> boolT] ---> boolT);
fun mk_all (x, T, P) = all_const T $ absfree (x, T) P;
fun list_all (xs, t) = fold_rev (fn (x, T) => fn P => all_const T $ Abs (x, T, P)) xs t;

fun exists_const T = Const ("HOL.Ex", [T --> boolT] ---> boolT);
fun mk_exists (x, T, P) = exists_const T $ absfree (x, T) P;

fun choice_const T = Const("Hilbert_Choice.Eps", (T --> boolT) --> T);

val class_equal = "HOL.equal";


(* binary operations and relations *)

fun mk_binop c (t, u) =
  let val T = fastype_of t in
    Const (c, [T, T] ---> T) $ t $ u
  end;

fun mk_binrel c (t, u) =
  let val T = fastype_of t in
    Const (c, [T, T] ---> boolT) $ t $ u
  end;

(*destruct the application of a binary operator. The dummyT case is a crude
  way of handling polymorphic operators.*)
fun dest_bin c T (tm as Const (c', Type ("fun", [T', _])) $ t $ u) =
      if c = c' andalso (T=T' orelse T=dummyT) then (t, u)
      else raise TERM ("dest_bin " ^ c, [tm])
  | dest_bin c _ tm = raise TERM ("dest_bin " ^ c, [tm]);


(* unit *)

val unitT = Type ("Product_Type.unit", []);

fun is_unitT (Type ("Product_Type.unit", [])) = true
  | is_unitT _ = false;

val unit = Const ("Product_Type.Unity", unitT);

fun is_unit (Const ("Product_Type.Unity", _)) = true
  | is_unit _ = false;


(* prod *)

fun mk_prodT (T1, T2) = Type ("Product_Type.prod", [T1, T2]);

fun dest_prodT (Type ("Product_Type.prod", [T1, T2])) = (T1, T2)
  | dest_prodT T = raise TYPE ("dest_prodT", [T], []);

fun pair_const T1 T2 = Const ("Product_Type.Pair", [T1, T2] ---> mk_prodT (T1, T2));

fun mk_prod (t1, t2) =
  let val T1 = fastype_of t1 and T2 = fastype_of t2 in
    pair_const T1 T2 $ t1 $ t2
  end;

fun dest_prod (Const ("Product_Type.Pair", _) $ t1 $ t2) = (t1, t2)
  | dest_prod t = raise TERM ("dest_prod", [t]);

fun mk_fst p =
  let val pT = fastype_of p in
    Const ("Product_Type.fst", pT --> fst (dest_prodT pT)) $ p
  end;

fun mk_snd p =
  let val pT = fastype_of p in
    Const ("Product_Type.snd", pT --> snd (dest_prodT pT)) $ p
  end;

fun split_const (A, B, C) =
  Const ("Product_Type.prod.prod_case", (A --> B --> C) --> mk_prodT (A, B) --> C);

fun mk_split t =
  (case Term.fastype_of t of
    T as (Type ("fun", [A, Type ("fun", [B, C])])) =>
      Const ("Product_Type.prod.prod_case", T --> mk_prodT (A, B) --> C) $ t
  | _ => raise TERM ("mk_split: bad body type", [t]));

(*Maps the type T1 * ... * Tn to [T1, ..., Tn], however nested*)
fun flatten_tupleT (Type ("Product_Type.prod", [T1, T2])) = flatten_tupleT T1 @ flatten_tupleT T2
  | flatten_tupleT T = [T];

(*abstraction over nested tuples*)
fun tupled_lambda (x as Free _) b = lambda x b
  | tupled_lambda (x as Var _) b = lambda x b
  | tupled_lambda (Const ("Product_Type.Pair", _) $ u $ v) b =
      mk_split (tupled_lambda u (tupled_lambda v b))
  | tupled_lambda (Const ("Product_Type.Unity", _)) b =
      Abs ("x", unitT, b)
  | tupled_lambda t _ = raise TERM ("tupled_lambda: bad tuple", [t]);


(* tuples with right-fold structure *)

fun mk_tupleT [] = unitT
  | mk_tupleT Ts = foldr1 mk_prodT Ts;

fun strip_tupleT (Type ("Product_Type.unit", [])) = []
  | strip_tupleT (Type ("Product_Type.prod", [T1, T2])) = T1 :: strip_tupleT T2
  | strip_tupleT T = [T];

fun mk_tuple [] = unit
  | mk_tuple ts = foldr1 mk_prod ts;

fun strip_tuple (Const ("Product_Type.Unity", _)) = []
  | strip_tuple (Const ("Product_Type.Pair", _) $ t1 $ t2) = t1 :: strip_tuple t2
  | strip_tuple t = [t];


(* tuples with specific arities

   an "arity" of a tuple is a list of lists of integers,
   denoting paths to subterms that are pairs
*)

fun ptuple_err s = raise TERM (s ^ ": inconsistent use of nested products", []);

fun mk_ptupleT ps =
  let
    fun mk p Ts =
      if member (op =) ps p then
        let
          val (T, Ts') = mk (1::p) Ts;
          val (U, Ts'') = mk (2::p) Ts'
        in (mk_prodT (T, U), Ts'') end
      else (hd Ts, tl Ts)
  in fst o mk [] end;

fun strip_ptupleT ps =
  let
    fun factors p T = if member (op =) ps p then (case T of
        Type ("Product_Type.prod", [T1, T2]) =>
          factors (1::p) T1 @ factors (2::p) T2
      | _ => ptuple_err "strip_ptupleT") else [T]
  in factors [] end;

val flat_tupleT_paths =
  let
    fun factors p (Type ("Product_Type.prod", [T1, T2])) =
          p :: factors (1::p) T1 @ factors (2::p) T2
      | factors p _ = []
  in factors [] end;

fun mk_ptuple ps =
  let
    fun mk p T ts =
      if member (op =) ps p then (case T of
          Type ("Product_Type.prod", [T1, T2]) =>
            let
              val (t, ts') = mk (1::p) T1 ts;
              val (u, ts'') = mk (2::p) T2 ts'
            in (pair_const T1 T2 $ t $ u, ts'') end
        | _ => ptuple_err "mk_ptuple")
      else (hd ts, tl ts)
  in fst oo mk [] end;

fun strip_ptuple ps =
  let
    fun dest p t = if member (op =) ps p then (case t of
        Const ("Product_Type.Pair", _) $ t $ u =>
          dest (1::p) t @ dest (2::p) u
      | _ => ptuple_err "strip_ptuple") else [t]
  in dest [] end;

val flat_tuple_paths =
  let
    fun factors p (Const ("Product_Type.Pair", _) $ t $ u) =
          p :: factors (1::p) t @ factors (2::p) u
      | factors p _ = []
  in factors [] end;

(*In mk_psplits ps S T u, term u expects separate arguments for the factors of S,
  with result type T.  The call creates a new term expecting one argument
  of type S.*)
fun mk_psplits ps T T3 u =
  let
    fun ap ((p, T) :: pTs) =
          if member (op =) ps p then (case T of
              Type ("Product_Type.prod", [T1, T2]) =>
                split_const (T1, T2, map snd pTs ---> T3) $
                  ap ((1::p, T1) :: (2::p, T2) :: pTs)
            | _ => ptuple_err "mk_psplits")
          else Abs ("x", T, ap pTs)
      | ap [] =
          let val k = length ps
          in list_comb (incr_boundvars (k + 1) u, map Bound (k downto 0)) end
  in ap [([], T)] end;

val strip_psplits =
  let
    fun strip [] qs Ts t = (t, rev Ts, qs)
      | strip (p :: ps) qs Ts (Const ("Product_Type.prod.prod_case", _) $ t) =
          strip ((1 :: p) :: (2 :: p) :: ps) (p :: qs) Ts t
      | strip (p :: ps) qs Ts (Abs (s, T, t)) = strip ps qs (T :: Ts) t
      | strip (p :: ps) qs Ts t = strip ps qs
          (hd (binder_types (fastype_of1 (Ts, t))) :: Ts)
          (incr_boundvars 1 t $ Bound 0)
  in strip [[]] [] [] end;


(* nat *)

val natT = Type ("Nat.nat", []);

val zero = Const ("Groups.zero_class.zero", natT);

fun is_zero (Const ("Groups.zero_class.zero", _)) = true
  | is_zero _ = false;

fun mk_Suc t = Const ("Nat.Suc", natT --> natT) $ t;

fun dest_Suc (Const ("Nat.Suc", _) $ t) = t
  | dest_Suc t = raise TERM ("dest_Suc", [t]);

val Suc_zero = mk_Suc zero;

fun mk_nat n =
  let
    fun mk 0 = zero
      | mk n = mk_Suc (mk (n - 1));
  in if n < 0 then raise TERM ("mk_nat: negative number", []) else mk n end;

fun dest_nat (Const ("Groups.zero_class.zero", _)) = 0
  | dest_nat (Const ("Nat.Suc", _) $ t) = dest_nat t + 1
  | dest_nat t = raise TERM ("dest_nat", [t]);

val class_size = "Nat.size";

fun size_const T = Const ("Nat.size_class.size", T --> natT);


(* code numeral *)

val code_numeralT = Type ("Code_Numeral.code_numeral", []);


(* binary numerals and int -- non-unique representation due to leading zeros/ones! *)

val intT = Type ("Int.int", []);

val pls_const = Const ("Int.Pls", intT)
and min_const = Const ("Int.Min", intT)
and bit0_const = Const ("Int.Bit0", intT --> intT)
and bit1_const = Const ("Int.Bit1", intT --> intT);

fun mk_bit 0 = bit0_const
  | mk_bit 1 = bit1_const
  | mk_bit _ = raise TERM ("mk_bit", []);

fun dest_bit (Const ("Int.Bit0", _)) = 0
  | dest_bit (Const ("Int.Bit1", _)) = 1
  | dest_bit t = raise TERM ("dest_bit", [t]);

fun mk_numeral 0 = pls_const
  | mk_numeral ~1 = min_const
  | mk_numeral i =
      let val (q, r) = Integer.div_mod i 2;
      in mk_bit r $ mk_numeral q end;

fun dest_numeral (Const ("Int.Pls", _)) = 0
  | dest_numeral (Const ("Int.Min", _)) = ~1
  | dest_numeral (Const ("Int.Bit0", _) $ bs) = 2 * dest_numeral bs
  | dest_numeral (Const ("Int.Bit1", _) $ bs) = 2 * dest_numeral bs + 1
  | dest_numeral t = raise TERM ("dest_numeral", [t]);

fun number_of_const T = Const ("Int.number_class.number_of", intT --> T);

fun add_numerals (Const ("Int.number_class.number_of", Type (_, [_, T])) $ t) = cons (t, T)
  | add_numerals (t $ u) = add_numerals t #> add_numerals u
  | add_numerals (Abs (_, _, t)) = add_numerals t
  | add_numerals _ = I;

fun mk_number T 0 = Const ("Groups.zero_class.zero", T)
  | mk_number T 1 = Const ("Groups.one_class.one", T)
  | mk_number T i = number_of_const T $ mk_numeral i;

fun dest_number (Const ("Groups.zero_class.zero", T)) = (T, 0)
  | dest_number (Const ("Groups.one_class.one", T)) = (T, 1)
  | dest_number (Const ("Int.number_class.number_of", Type ("fun", [_, T])) $ t) =
      (T, dest_numeral t)
  | dest_number t = raise TERM ("dest_number", [t]);


(* real *)

val realT = Type ("RealDef.real", []);


(* list *)

fun listT T = Type ("List.list", [T]);

fun nil_const T = Const ("List.list.Nil", listT T);

fun cons_const T =
  let val lT = listT T
  in Const ("List.list.Cons", T --> lT --> lT) end;

fun mk_list T ts =
  let
    val lT = listT T;
    val Nil = Const ("List.list.Nil", lT);
    fun Cons t u = Const ("List.list.Cons", T --> lT --> lT) $ t $ u;
  in fold_rev Cons ts Nil end;

fun dest_list (Const ("List.list.Nil", _)) = []
  | dest_list (Const ("List.list.Cons", _) $ t $ u) = t :: dest_list u
  | dest_list t = raise TERM ("dest_list", [t]);


(* nibble *)

val nibbleT = Type ("String.nibble", []);

fun mk_nibble n =
  let val s =
    if 0 <= n andalso n <= 9 then chr (n + ord "0")
    else if 10 <= n andalso n <= 15 then chr (n + ord "A" - 10)
    else raise TERM ("mk_nibble", [])
  in Const ("String.nibble.Nibble" ^ s, nibbleT) end;

fun dest_nibble t =
  let fun err () = raise TERM ("dest_nibble", [t]) in
    (case try (unprefix "String.nibble.Nibble" o fst o Term.dest_Const) t of
      NONE => err ()
    | SOME c =>
        if size c <> 1 then err ()
        else if "0" <= c andalso c <= "9" then ord c - ord "0"
        else if "A" <= c andalso c <= "F" then ord c - ord "A" + 10
        else err ())
  end;


(* char *)

val charT = Type ("String.char", []);

fun mk_char n =
  if 0 <= n andalso n <= 255 then
    Const ("String.char.Char", nibbleT --> nibbleT --> charT) $
      mk_nibble (n div 16) $ mk_nibble (n mod 16)
  else raise TERM ("mk_char", []);

fun dest_char (Const ("String.char.Char", _) $ t $ u) =
      dest_nibble t * 16 + dest_nibble u
  | dest_char t = raise TERM ("dest_char", [t]);


(* string *)

val stringT = listT charT;

val mk_string = mk_list charT o map (mk_char o ord) o raw_explode;
val dest_string = implode o map (chr o dest_char) o dest_list;


(* literal *)

val literalT = Type ("String.literal", []);

fun mk_literal s = Const ("String.STR", stringT --> literalT)
      $ mk_string s;
fun dest_literal (Const ("String.STR", _) $ t) =
      dest_string t
  | dest_literal t = raise TERM ("dest_literal", [t]);


(* typerep and term *)

val typerepT = Type ("Typerep.typerep", []);

fun mk_typerep (Type (tyco, Ts)) = Const ("Typerep.typerep.Typerep",
      literalT --> listT typerepT --> typerepT) $ mk_literal tyco
        $ mk_list typerepT (map mk_typerep Ts)
  | mk_typerep (T as TFree _) = Const ("Typerep.typerep_class.typerep",
      Term.itselfT T --> typerepT) $ Logic.mk_type T;

val termT = Type ("Code_Evaluation.term", []);

fun term_of_const T = Const ("Code_Evaluation.term_of_class.term_of", T --> termT);

fun mk_term_of T t = term_of_const T $ t;

fun reflect_term (Const (c, T)) =
      Const ("Code_Evaluation.Const", literalT --> typerepT --> termT)
        $ mk_literal c $ mk_typerep T
  | reflect_term (t1 $ t2) =
      Const ("Code_Evaluation.App", termT --> termT --> termT)
        $ reflect_term t1 $ reflect_term t2
  | reflect_term (Abs (v, _, t)) = Abs (v, termT, reflect_term t)
  | reflect_term t = t;

fun mk_valtermify_app c vs T =
  let
    fun termifyT T = mk_prodT (T, unitT --> termT);
    fun valapp T T' = Const ("Code_Evaluation.valapp",
      termifyT (T --> T') --> termifyT T --> termifyT T');
    fun mk_fTs [] _ = []
      | mk_fTs (_ :: Ts) T = (Ts ---> T) :: mk_fTs Ts T;
    val Ts = map snd vs;
    val t = Const (c, Ts ---> T);
    val tt = mk_prod (t, Abs ("u", unitT, reflect_term t));
    fun app (fT, (v, T)) t = valapp T fT $ t $ Free (v, termifyT T);
  in fold app (mk_fTs Ts T ~~ vs) tt end;


(* open state monads *)

fun mk_return T U x = pair_const T U $ x;

fun mk_ST clauses t U (someT, V) =
  let
    val R = case someT of SOME T => mk_prodT (T, V) | NONE => V
    fun mk_clause ((t, U), SOME (v, T)) (t', U') =
          (Const ("Product_Type.scomp", (U --> mk_prodT (T, U')) --> (T --> U' --> R) --> U --> R)
            $ t $ lambda (Free (v, T)) t', U)
      | mk_clause ((t, U), NONE) (t', U') =
          (Const ("Product_Type.fcomp", (U --> U') --> (U' --> R) --> U --> R)
            $ t $ t', U)
  in fold_rev mk_clause clauses (t, U) |> fst end;


(* random seeds *)

val random_seedT = mk_prodT (code_numeralT, code_numeralT);

fun mk_random T t = Const ("Quickcheck.random_class.random", code_numeralT
  --> random_seedT --> mk_prodT (mk_prodT (T, unitT --> termT), random_seedT)) $ t;

end;

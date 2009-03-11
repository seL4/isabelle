(*  Title:      HOL/hologic.ML
    Author:     Lawrence C Paulson and Markus Wenzel

Abstract syntax operations for HOL.
*)

signature HOLOGIC =
sig
  val typeS: sort
  val typeT: typ
  val boolN: string
  val boolT: typ
  val Trueprop: term
  val mk_Trueprop: term -> term
  val dest_Trueprop: term -> term
  val true_const: term
  val false_const: term
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
  val class_eq: string
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
  val prodT_factors: typ -> typ list
  val mk_tuple: typ -> term list -> term
  val dest_tuple: term -> term list
  val ap_split: typ -> typ -> term -> term
  val prod_factors: term -> int list list
  val dest_tuple': int list list -> term -> term list
  val prodT_factors': int list list -> typ -> typ list
  val ap_split': int list list -> typ -> typ -> term -> term
  val mk_tuple': int list list -> typ -> term list -> term
  val mk_tupleT: int list list -> typ list -> typ
  val strip_split: term -> term * typ list * int list list
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
  val indexT: typ
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
end;

structure HOLogic: HOLOGIC =
struct

(* HOL syntax *)

val typeS: sort = ["HOL.type"];
val typeT = TypeInfer.anyT typeS;


(* bool and set *)

val boolN = "bool";
val boolT = Type (boolN, []);

val true_const =  Const ("True", boolT);
val false_const = Const ("False", boolT);

fun mk_setT T = T --> boolT;

fun dest_setT (Type ("fun", [T, Type ("bool", [])])) = T
  | dest_setT T = raise TYPE ("dest_setT: set type expected", [T], []);

fun mk_set T ts =
  let
    val sT = mk_setT T;
    val empty = Const ("Set.empty", sT);
    fun insert t u = Const ("insert", T --> sT --> sT) $ t $ u;
  in fold_rev insert ts empty end;

fun mk_UNIV T = Const ("Set.UNIV", mk_setT T);

fun dest_set (Const ("Orderings.bot", _)) = []
  | dest_set (Const ("insert", _) $ t $ u) = t :: dest_set u
  | dest_set t = raise TERM ("dest_set", [t]);

fun Collect_const T = Const ("Collect", (T --> boolT) --> mk_setT T);
fun mk_Collect (a, T, t) = Collect_const T $ absfree (a, T, t);

fun mk_mem (x, A) =
  let val setT = fastype_of A in
    Const ("op :", dest_setT setT --> setT --> boolT) $ x $ A
  end;

fun dest_mem (Const ("op :", _) $ x $ A) = (x, A)
  | dest_mem t = raise TERM ("dest_mem", [t]);


(* logic *)

val Trueprop = Const ("Trueprop", boolT --> propT);

fun mk_Trueprop P = Trueprop $ P;

fun dest_Trueprop (Const ("Trueprop", _) $ P) = P
  | dest_Trueprop t = raise TERM ("dest_Trueprop", [t]);

fun conj_intr thP thQ =
  let
    val (P, Q) = pairself (ObjectLogic.dest_judgment o Thm.cprop_of) (thP, thQ)
      handle CTERM (msg, _) => raise THM (msg, 0, [thP, thQ]);
    val inst = Thm.instantiate ([], [(@{cpat "?P::bool"}, P), (@{cpat "?Q::bool"}, Q)]);
  in Drule.implies_elim_list (inst @{thm conjI}) [thP, thQ] end;

fun conj_elim thPQ =
  let
    val (P, Q) = Thm.dest_binop (ObjectLogic.dest_judgment (Thm.cprop_of thPQ))
      handle CTERM (msg, _) => raise THM (msg, 0, [thPQ]);
    val inst = Thm.instantiate ([], [(@{cpat "?P::bool"}, P), (@{cpat "?Q::bool"}, Q)]);
    val thP = Thm.implies_elim (inst @{thm conjunct1}) thPQ;
    val thQ = Thm.implies_elim (inst @{thm conjunct2}) thPQ;
  in (thP, thQ) end;

fun conj_elims th =
  let val (th1, th2) = conj_elim th
  in conj_elims th1 @ conj_elims th2 end handle THM _ => [th];

val conj = @{term "op &"}
and disj = @{term "op |"}
and imp = @{term "op -->"}
and Not = @{term "Not"};

fun mk_conj (t1, t2) = conj $ t1 $ t2
and mk_disj (t1, t2) = disj $ t1 $ t2
and mk_imp (t1, t2) = imp $ t1 $ t2
and mk_not t = Not $ t;

fun dest_conj (Const ("op &", _) $ t $ t') = t :: dest_conj t'
  | dest_conj t = [t];

fun dest_disj (Const ("op |", _) $ t $ t') = t :: dest_disj t'
  | dest_disj t = [t];

(*Like dest_disj, but flattens disjunctions however nested*)
fun disjuncts_aux (Const ("op |", _) $ t $ t') disjs = disjuncts_aux t (disjuncts_aux t' disjs)
  | disjuncts_aux t disjs = t::disjs;

fun disjuncts t = disjuncts_aux t [];

fun dest_imp (Const("op -->",_) $ A $ B) = (A, B)
  | dest_imp  t = raise TERM ("dest_imp", [t]);

fun dest_not (Const ("Not", _) $ t) = t
  | dest_not t = raise TERM ("dest_not", [t]);

fun eq_const T = Const ("op =", [T, T] ---> boolT);
fun mk_eq (t, u) = eq_const (fastype_of t) $ t $ u;

fun dest_eq (Const ("op =", _) $ lhs $ rhs) = (lhs, rhs)
  | dest_eq t = raise TERM ("dest_eq", [t])

fun all_const T = Const ("All", [T --> boolT] ---> boolT);
fun mk_all (x, T, P) = all_const T $ absfree (x, T, P);
fun list_all (xs, t) = fold_rev (fn (x, T) => fn P => all_const T $ Abs (x, T, P)) xs t;

fun exists_const T = Const ("Ex", [T --> boolT] ---> boolT);
fun mk_exists (x, T, P) = exists_const T $ absfree (x, T, P);

fun choice_const T = Const("Hilbert_Choice.Eps", (T --> boolT) --> T);

val class_eq = "HOL.eq";


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

fun mk_prodT (T1, T2) = Type ("*", [T1, T2]);

fun dest_prodT (Type ("*", [T1, T2])) = (T1, T2)
  | dest_prodT T = raise TYPE ("dest_prodT", [T], []);

fun pair_const T1 T2 = Const ("Pair", [T1, T2] ---> mk_prodT (T1, T2));

fun mk_prod (t1, t2) =
  let val T1 = fastype_of t1 and T2 = fastype_of t2 in
    pair_const T1 T2 $ t1 $ t2
  end;

fun dest_prod (Const ("Pair", _) $ t1 $ t2) = (t1, t2)
  | dest_prod t = raise TERM ("dest_prod", [t]);

fun mk_fst p =
  let val pT = fastype_of p in
    Const ("fst", pT --> fst (dest_prodT pT)) $ p
  end;

fun mk_snd p =
  let val pT = fastype_of p in
    Const ("snd", pT --> snd (dest_prodT pT)) $ p
  end;

fun split_const (A, B, C) =
  Const ("split", (A --> B --> C) --> mk_prodT (A, B) --> C);

fun mk_split t =
  (case Term.fastype_of t of
    T as (Type ("fun", [A, Type ("fun", [B, C])])) =>
      Const ("split", T --> mk_prodT (A, B) --> C) $ t
  | _ => raise TERM ("mk_split: bad body type", [t]));

(*Maps the type T1 * ... * Tn to [T1, ..., Tn], however nested*)
fun prodT_factors (Type ("*", [T1, T2])) = prodT_factors T1 @ prodT_factors T2
  | prodT_factors T = [T];

(*Makes a nested tuple from a list, following the product type structure*)
fun mk_tuple (Type ("*", [T1, T2])) tms =
        mk_prod (mk_tuple T1 tms,
                 mk_tuple T2 (Library.drop (length (prodT_factors T1), tms)))
  | mk_tuple T (t::_) = t;

fun dest_tuple (Const ("Pair", _) $ t $ u) = dest_tuple t @ dest_tuple u
  | dest_tuple t = [t];

(*In ap_split S T u, term u expects separate arguments for the factors of S,
  with result type T.  The call creates a new term expecting one argument
  of type S.*)
fun ap_split T T3 u =
  let
    fun ap (T :: Ts) =
          (case T of
             Type ("*", [T1, T2]) =>
               split_const (T1, T2, Ts ---> T3) $ ap (T1 :: T2 :: Ts)
           | _ => Abs ("x", T, ap Ts))
      | ap [] =
          let val k = length (prodT_factors T)
          in list_comb (incr_boundvars k u, map Bound (k - 1 downto 0)) end
  in ap [T] end;


(* operations on tuples with specific arities *)
(*
  an "arity" of a tuple is a list of lists of integers
  ("factors"), denoting paths to subterms that are pairs
*)

fun prod_err s = raise TERM (s ^ ": inconsistent use of products", []);

fun prod_factors t =
  let
    fun factors p (Const ("Pair", _) $ t $ u) =
          p :: factors (1::p) t @ factors (2::p) u
      | factors p _ = []
  in factors [] t end;

fun dest_tuple' ps =
  let
    fun dest p t = if p mem ps then (case t of
        Const ("Pair", _) $ t $ u =>
          dest (1::p) t @ dest (2::p) u
      | _ => prod_err "dest_tuple'") else [t]
  in dest [] end;

fun prodT_factors' ps =
  let
    fun factors p T = if p mem ps then (case T of
        Type ("*", [T1, T2]) =>
          factors (1::p) T1 @ factors (2::p) T2
      | _ => prod_err "prodT_factors'") else [T]
  in factors [] end;

(*In ap_split' ps S T u, term u expects separate arguments for the factors of S,
  with result type T.  The call creates a new term expecting one argument
  of type S.*)
fun ap_split' ps T T3 u =
  let
    fun ap ((p, T) :: pTs) =
          if p mem ps then (case T of
              Type ("*", [T1, T2]) =>
                split_const (T1, T2, map snd pTs ---> T3) $
                  ap ((1::p, T1) :: (2::p, T2) :: pTs)
            | _ => prod_err "ap_split'")
          else Abs ("x", T, ap pTs)
      | ap [] =
          let val k = length ps
          in list_comb (incr_boundvars (k + 1) u, map Bound (k downto 0)) end
  in ap [([], T)] end;

fun mk_tuple' ps =
  let
    fun mk p T ts =
      if p mem ps then (case T of
          Type ("*", [T1, T2]) =>
            let
              val (t, ts') = mk (1::p) T1 ts;
              val (u, ts'') = mk (2::p) T2 ts'
            in (pair_const T1 T2 $ t $ u, ts'') end
        | _ => prod_err "mk_tuple'")
      else (hd ts, tl ts)
  in fst oo mk [] end;

fun mk_tupleT ps =
  let
    fun mk p Ts =
      if p mem ps then
        let
          val (T, Ts') = mk (1::p) Ts;
          val (U, Ts'') = mk (2::p) Ts'
        in (mk_prodT (T, U), Ts'') end
      else (hd Ts, tl Ts)
  in fst o mk [] end;

fun strip_split t =
  let
    fun strip [] qs Ts t = (t, Ts, qs)
      | strip (p :: ps) qs Ts (Const ("split", _) $ t) =
          strip ((1 :: p) :: (2 :: p) :: ps) (p :: qs) Ts t
      | strip (p :: ps) qs Ts (Abs (s, T, t)) = strip ps qs (T :: Ts) t
      | strip (p :: ps) qs Ts t = strip ps qs
          (hd (binder_types (fastype_of1 (Ts, t))) :: Ts)
          (incr_boundvars 1 t $ Bound 0)
  in strip [[]] [] [] t end;


(* nat *)

val natT = Type ("nat", []);

val zero = Const ("HOL.zero_class.zero", natT);

fun is_zero (Const ("HOL.zero_class.zero", _)) = true
  | is_zero _ = false;

fun mk_Suc t = Const ("Suc", natT --> natT) $ t;

fun dest_Suc (Const ("Suc", _) $ t) = t
  | dest_Suc t = raise TERM ("dest_Suc", [t]);

val Suc_zero = mk_Suc zero;

fun mk_nat n =
  let
    fun mk 0 = zero
      | mk n = mk_Suc (mk (n - 1));
  in if n < 0 then raise TERM ("mk_nat: negative number", []) else mk n end;

fun dest_nat (Const ("HOL.zero_class.zero", _)) = 0
  | dest_nat (Const ("Suc", _) $ t) = dest_nat t + 1
  | dest_nat t = raise TERM ("dest_nat", [t]);

val class_size = "Nat.size";

fun size_const T = Const ("Nat.size_class.size", T --> natT);


(* index *)

val indexT = Type ("Code_Index.index", []);


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

fun mk_number T 0 = Const ("HOL.zero_class.zero", T)
  | mk_number T 1 = Const ("HOL.one_class.one", T)
  | mk_number T i = number_of_const T $ mk_numeral i;

fun dest_number (Const ("HOL.zero_class.zero", T)) = (T, 0)
  | dest_number (Const ("HOL.one_class.one", T)) = (T, 1)
  | dest_number (Const ("Int.number_class.number_of", Type ("fun", [_, T])) $ t) =
      (T, dest_numeral t)
  | dest_number t = raise TERM ("dest_number", [t]);


(* real *)

val realT = Type ("RealDef.real", []);


(* nibble *)

val nibbleT = Type ("List.nibble", []);

fun mk_nibble n =
  let val s =
    if 0 <= n andalso n <= 9 then chr (n + ord "0")
    else if 10 <= n andalso n <= 15 then chr (n + ord "A" - 10)
    else raise TERM ("mk_nibble", [])
  in Const ("List.nibble.Nibble" ^ s, nibbleT) end;

fun dest_nibble t =
  let fun err () = raise TERM ("dest_nibble", [t]) in
    (case try (unprefix "List.nibble.Nibble" o fst o Term.dest_Const) t of
      NONE => err ()
    | SOME c =>
        if size c <> 1 then err ()
        else if "0" <= c andalso c <= "9" then ord c - ord "0"
        else if "A" <= c andalso c <= "F" then ord c - ord "A" + 10
        else err ())
  end;


(* char *)

val charT = Type ("List.char", []);

fun mk_char n =
  if 0 <= n andalso n <= 255 then
    Const ("List.char.Char", nibbleT --> nibbleT --> charT) $
      mk_nibble (n div 16) $ mk_nibble (n mod 16)
  else raise TERM ("mk_char", []);

fun dest_char (Const ("List.char.Char", _) $ t $ u) =
      dest_nibble t * 16 + dest_nibble u
  | dest_char t = raise TERM ("dest_char", [t]);


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


(* string *)

val stringT = Type ("List.string", []);

val mk_string = mk_list charT o map (mk_char o ord) o explode;
val dest_string = implode o map (chr o dest_char) o dest_list;

end;

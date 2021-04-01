structure Order_Procedure : sig
  datatype int = Int_of_integer of IntInf.int
  val integer_of_int : int -> IntInf.int
  datatype 'a fm = Atom of 'a | And of 'a fm * 'a fm | Or of 'a fm * 'a fm |
    Neg of 'a fm
  datatype trm = Const of string | App of trm * trm | Var of int
  datatype prf_trm = PThm of string | Appt of prf_trm * trm |
    AppP of prf_trm * prf_trm | AbsP of trm * prf_trm | Bound of trm |
    Conv of trm * prf_trm * prf_trm
  datatype o_atom = EQ of int * int | LEQ of int * int | LESS of int * int
  val lo_contr_prf : (bool * o_atom) fm -> prf_trm option
  val po_contr_prf : (bool * o_atom) fm -> prf_trm option
end = struct

datatype int = Int_of_integer of IntInf.int;

fun integer_of_int (Int_of_integer k) = k;

fun equal_inta k l = (((integer_of_int k) : IntInf.int) = (integer_of_int l));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_int = {equal = equal_inta} : int equal;

fun less_eq_int k l = IntInf.<= (integer_of_int k, integer_of_int l);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun less_int k l = IntInf.< (integer_of_int k, integer_of_int l);

val ord_int = {less_eq = less_eq_int, less = less_int} : int ord;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_int = {ord_preorder = ord_int} : int preorder;

val order_int = {preorder_order = preorder_int} : int order;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_int = {order_linorder = order_int} : int linorder;

fun eq A_ a b = equal A_ a b;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

fun less_eq_prod A_ B_ (x1, y1) (x2, y2) =
  less A_ x1 x2 orelse less_eq A_ x1 x2 andalso less_eq B_ y1 y2;

fun less_prod A_ B_ (x1, y1) (x2, y2) =
  less A_ x1 x2 orelse less_eq A_ x1 x2 andalso less B_ y1 y2;

fun ord_prod A_ B_ = {less_eq = less_eq_prod A_ B_, less = less_prod A_ B_} :
  ('a * 'b) ord;

fun preorder_prod A_ B_ =
  {ord_preorder = ord_prod (ord_preorder A_) (ord_preorder B_)} :
  ('a * 'b) preorder;

fun order_prod A_ B_ =
  {preorder_order = preorder_prod (preorder_order A_) (preorder_order B_)} :
  ('a * 'b) order;

fun linorder_prod A_ B_ =
  {order_linorder = order_prod (order_linorder A_) (order_linorder B_)} :
  ('a * 'b) linorder;

datatype nat = Zero_nat | Suc of nat;

datatype color = R | B;

datatype ('a, 'b) rbta = Empty |
  Branch of color * ('a, 'b) rbta * 'a * 'b * ('a, 'b) rbta;

datatype ('b, 'a) rbt = RBT of ('b, 'a) rbta;

datatype 'a set = Set of 'a list | Coset of 'a list;

datatype 'a fm = Atom of 'a | And of 'a fm * 'a fm | Or of 'a fm * 'a fm |
  Neg of 'a fm;

datatype trm = Const of string | App of trm * trm | Var of int;

datatype prf_trm = PThm of string | Appt of prf_trm * trm |
  AppP of prf_trm * prf_trm | AbsP of trm * prf_trm | Bound of trm |
  Conv of trm * prf_trm * prf_trm;

datatype ('a, 'b) mapping = Mapping of ('a, 'b) rbt;

datatype o_atom = EQ of int * int | LEQ of int * int | LESS of int * int;

fun id x = (fn xa => xa) x;

fun impl_of B_ (RBT x) = x;

fun folda f (Branch (c, lt, k, v, rt)) x = folda f rt (f k v (folda f lt x))
  | folda f Empty x = x;

fun fold A_ x xc = folda x (impl_of A_ xc);

fun gen_keys kts (Branch (c, l, k, v, r)) = gen_keys ((k, r) :: kts) l
  | gen_keys ((k, t) :: kts) Empty = k :: gen_keys kts t
  | gen_keys [] Empty = [];

fun keysb x = gen_keys [] x;

fun keys A_ x = keysb (impl_of A_ x);

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun empty A_ = RBT Empty;

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

fun foldr f [] = id
  | foldr f (x :: xs) = f x o foldr f xs;

fun balance (Branch (R, a, w, x, b)) s t (Branch (R, c, y, z, d)) =
  Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, d))
  | balance (Branch (R, Branch (R, a, w, x, b), s, t, c)) y z Empty =
    Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, Empty))
  | balance (Branch (R, Branch (R, a, w, x, b), s, t, c)) y z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, Branch (B, a, w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance (Branch (R, Empty, w, x, Branch (R, b, s, t, c))) y z Empty =
    Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
  | balance
    (Branch (R, Branch (B, va, vb, vc, vd), w, x, Branch (R, b, s, t, c))) y z
    Empty =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, Empty))
  | balance (Branch (R, Empty, w, x, Branch (R, b, s, t, c))) y z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, Branch (B, Empty, w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance
    (Branch (R, Branch (B, ve, vf, vg, vh), w, x, Branch (R, b, s, t, c))) y z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, Branch (B, Branch (B, ve, vf, vg, vh), w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance Empty w x (Branch (R, b, s, t, Branch (R, c, y, z, d))) =
    Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, d))
  | balance (Branch (B, va, vb, vc, vd)) w x
    (Branch (R, b, s, t, Branch (R, c, y, z, d))) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, d))
  | balance Empty w x (Branch (R, Branch (R, b, s, t, c), y, z, Empty)) =
    Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
  | balance Empty w x
    (Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, va, vb, vc, vd))) =
    Branch
      (R, Branch (B, Empty, w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance (Branch (B, va, vb, vc, vd)) w x
    (Branch (R, Branch (R, b, s, t, c), y, z, Empty)) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, Empty))
  | balance (Branch (B, va, vb, vc, vd)) w x
    (Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, ve, vf, vg, vh))) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, ve, vf, vg, vh)))
  | balance Empty s t Empty = Branch (B, Empty, s, t, Empty)
  | balance Empty s t (Branch (B, va, vb, vc, vd)) =
    Branch (B, Empty, s, t, Branch (B, va, vb, vc, vd))
  | balance Empty s t (Branch (v, Empty, vb, vc, Empty)) =
    Branch (B, Empty, s, t, Branch (v, Empty, vb, vc, Empty))
  | balance Empty s t (Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty)) =
    Branch
      (B, Empty, s, t, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
  | balance Empty s t (Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi))) =
    Branch
      (B, Empty, s, t, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
  | balance Empty s t
    (Branch (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi)))
    = Branch
        (B, Empty, s, t,
          Branch
            (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi)))
  | balance (Branch (B, va, vb, vc, vd)) s t Empty =
    Branch (B, Branch (B, va, vb, vc, vd), s, t, Empty)
  | balance (Branch (B, va, vb, vc, vd)) s t (Branch (B, ve, vf, vg, vh)) =
    Branch (B, Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh))
  | balance (Branch (B, va, vb, vc, vd)) s t (Branch (v, Empty, vf, vg, Empty))
    = Branch
        (B, Branch (B, va, vb, vc, vd), s, t, Branch (v, Empty, vf, vg, Empty))
  | balance (Branch (B, va, vb, vc, vd)) s t
    (Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty)) =
    Branch
      (B, Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty))
  | balance (Branch (B, va, vb, vc, vd)) s t
    (Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm))) =
    Branch
      (B, Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm)))
  | balance (Branch (B, va, vb, vc, vd)) s t
    (Branch (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm)))
    = Branch
        (B, Branch (B, va, vb, vc, vd), s, t,
          Branch
            (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm)))
  | balance (Branch (v, Empty, vb, vc, Empty)) s t Empty =
    Branch (B, Branch (v, Empty, vb, vc, Empty), s, t, Empty)
  | balance (Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh))) s t Empty =
    Branch
      (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t, Empty)
  | balance (Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty)) s t Empty =
    Branch
      (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t, Empty)
  | balance
    (Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)))
    s t Empty =
    Branch
      (B, Branch
            (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        s, t, Empty)
  | balance (Branch (v, Empty, vf, vg, Empty)) s t (Branch (B, va, vb, vc, vd))
    = Branch
        (B, Branch (v, Empty, vf, vg, Empty), s, t, Branch (B, va, vb, vc, vd))
  | balance (Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl))) s t
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (B, Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
        Branch (B, va, vb, vc, vd))
  | balance (Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty)) s t
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (B, Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
        Branch (B, va, vb, vc, vd))
  | balance
    (Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)))
    s t (Branch (B, va, vb, vc, vd)) =
    Branch
      (B, Branch
            (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)),
        s, t, Branch (B, va, vb, vc, vd));

fun rbt_ins A_ f k v Empty = Branch (R, Empty, k, v, Empty)
  | rbt_ins A_ f k v (Branch (B, l, x, y, r)) =
    (if less A_ k x then balance (rbt_ins A_ f k v l) x y r
      else (if less A_ x k then balance l x y (rbt_ins A_ f k v r)
             else Branch (B, l, x, f k y v, r)))
  | rbt_ins A_ f k v (Branch (R, l, x, y, r)) =
    (if less A_ k x then Branch (R, rbt_ins A_ f k v l, x, y, r)
      else (if less A_ x k then Branch (R, l, x, y, rbt_ins A_ f k v r)
             else Branch (R, l, x, f k y v, r)));

fun paint c Empty = Empty
  | paint c (Branch (uu, l, k, v, r)) = Branch (c, l, k, v, r);

fun rbt_insert_with_key A_ f k v t = paint B (rbt_ins A_ f k v t);

fun rbt_insert A_ = rbt_insert_with_key A_ (fn _ => fn _ => fn nv => nv);

fun insert A_ xc xd xe =
  RBT (rbt_insert ((ord_preorder o preorder_order o order_linorder) A_) xc xd
        (impl_of A_ xe));

fun rbt_lookup A_ Empty k = NONE
  | rbt_lookup A_ (Branch (uu, l, x, y, r)) k =
    (if less A_ k x then rbt_lookup A_ l k
      else (if less A_ x k then rbt_lookup A_ r k else SOME y));

fun lookup A_ x =
  rbt_lookup ((ord_preorder o preorder_order o order_linorder) A_)
    (impl_of A_ x);

fun member A_ [] y = false
  | member A_ (x :: xs) y = eq A_ x y orelse member A_ xs y;

fun hd (x21 :: x22) = x21;

fun tl [] = []
  | tl (x21 :: x22) = x22;

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if member A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun dnf_and_fm (Or (phi_1, phi_2)) psi =
  Or (dnf_and_fm phi_1 psi, dnf_and_fm phi_2 psi)
  | dnf_and_fm (Atom v) (Or (phi_1, phi_2)) =
    Or (dnf_and_fm (Atom v) phi_1, dnf_and_fm (Atom v) phi_2)
  | dnf_and_fm (And (v, va)) (Or (phi_1, phi_2)) =
    Or (dnf_and_fm (And (v, va)) phi_1, dnf_and_fm (And (v, va)) phi_2)
  | dnf_and_fm (Neg v) (Or (phi_1, phi_2)) =
    Or (dnf_and_fm (Neg v) phi_1, dnf_and_fm (Neg v) phi_2)
  | dnf_and_fm (Atom v) (Atom va) = And (Atom v, Atom va)
  | dnf_and_fm (Atom v) (And (va, vb)) = And (Atom v, And (va, vb))
  | dnf_and_fm (Atom v) (Neg va) = And (Atom v, Neg va)
  | dnf_and_fm (And (v, va)) (Atom vb) = And (And (v, va), Atom vb)
  | dnf_and_fm (And (v, va)) (And (vb, vc)) = And (And (v, va), And (vb, vc))
  | dnf_and_fm (And (v, va)) (Neg vb) = And (And (v, va), Neg vb)
  | dnf_and_fm (Neg v) (Atom va) = And (Neg v, Atom va)
  | dnf_and_fm (Neg v) (And (va, vb)) = And (Neg v, And (va, vb))
  | dnf_and_fm (Neg v) (Neg va) = And (Neg v, Neg va);

fun dnf_fm (And (phi_1, phi_2)) = dnf_and_fm (dnf_fm phi_1) (dnf_fm phi_2)
  | dnf_fm (Or (phi_1, phi_2)) = Or (dnf_fm phi_1, dnf_fm phi_2)
  | dnf_fm (Atom v) = Atom v
  | dnf_fm (Neg v) = Neg v;

fun keysa A_ (Mapping t) = Set (keys A_ t);

fun amap_fm h (Atom a) = h a
  | amap_fm h (And (phi_1, phi_2)) = And (amap_fm h phi_1, amap_fm h phi_2)
  | amap_fm h (Or (phi_1, phi_2)) = Or (amap_fm h phi_1, amap_fm h phi_2)
  | amap_fm h (Neg phi) = Neg (amap_fm h phi);

fun emptya A_ = Mapping (empty A_);

fun lookupa A_ (Mapping t) = lookup A_ t;

fun update A_ k v (Mapping t) = Mapping (insert A_ k v t);

fun gen_length n (x :: xs) = gen_length (Suc n) xs
  | gen_length n [] = n;

fun size_list x = gen_length Zero_nat x;

fun card A_ (Set xs) = size_list (remdups A_ xs);

fun conj_list (And (phi_1, phi_2)) = conj_list phi_1 @ conj_list phi_2
  | conj_list (Atom a) = [a];

fun trm_of_fm f (Atom a) = f a
  | trm_of_fm f (And (phi_1, phi_2)) =
    App (App (Const "conj", trm_of_fm f phi_1), trm_of_fm f phi_2)
  | trm_of_fm f (Or (phi_1, phi_2)) =
    App (App (Const "disj", trm_of_fm f phi_1), trm_of_fm f phi_2)
  | trm_of_fm f (Neg phi) = App (Const "Not", trm_of_fm f phi);

fun dnf_and_fm_prf (Or (phi_1, phi_2)) psi =
  foldl (fn a => fn b => AppP (a, b)) (PThm "then_conv")
    [PThm "conj_disj_distribR_conv",
      foldl (fn a => fn b => AppP (a, b)) (PThm "combination_conv")
        [AppP (PThm "arg_conv",
                hd [dnf_and_fm_prf phi_1 psi, dnf_and_fm_prf phi_2 psi]),
          hd (tl [dnf_and_fm_prf phi_1 psi, dnf_and_fm_prf phi_2 psi])]]
  | dnf_and_fm_prf (Atom v) (Or (phi_1, phi_2)) =
    foldl (fn a => fn b => AppP (a, b)) (PThm "then_conv")
      [PThm "conj_disj_distribL_conv",
        foldl (fn a => fn b => AppP (a, b)) (PThm "combination_conv")
          [AppP (PThm "arg_conv",
                  hd [dnf_and_fm_prf (Atom v) phi_1,
                       dnf_and_fm_prf (Atom v) phi_2]),
            hd (tl [dnf_and_fm_prf (Atom v) phi_1,
                     dnf_and_fm_prf (Atom v) phi_2])]]
  | dnf_and_fm_prf (And (v, va)) (Or (phi_1, phi_2)) =
    foldl (fn a => fn b => AppP (a, b)) (PThm "then_conv")
      [PThm "conj_disj_distribL_conv",
        foldl (fn a => fn b => AppP (a, b)) (PThm "combination_conv")
          [AppP (PThm "arg_conv",
                  hd [dnf_and_fm_prf (And (v, va)) phi_1,
                       dnf_and_fm_prf (And (v, va)) phi_2]),
            hd (tl [dnf_and_fm_prf (And (v, va)) phi_1,
                     dnf_and_fm_prf (And (v, va)) phi_2])]]
  | dnf_and_fm_prf (Neg v) (Or (phi_1, phi_2)) =
    foldl (fn a => fn b => AppP (a, b)) (PThm "then_conv")
      [PThm "conj_disj_distribL_conv",
        foldl (fn a => fn b => AppP (a, b)) (PThm "combination_conv")
          [AppP (PThm "arg_conv",
                  hd [dnf_and_fm_prf (Neg v) phi_1,
                       dnf_and_fm_prf (Neg v) phi_2]),
            hd (tl [dnf_and_fm_prf (Neg v) phi_1,
                     dnf_and_fm_prf (Neg v) phi_2])]]
  | dnf_and_fm_prf (Atom v) (Atom va) = PThm "all_conv"
  | dnf_and_fm_prf (Atom v) (And (va, vb)) = PThm "all_conv"
  | dnf_and_fm_prf (Atom v) (Neg va) = PThm "all_conv"
  | dnf_and_fm_prf (And (v, va)) (Atom vb) = PThm "all_conv"
  | dnf_and_fm_prf (And (v, va)) (And (vb, vc)) = PThm "all_conv"
  | dnf_and_fm_prf (And (v, va)) (Neg vb) = PThm "all_conv"
  | dnf_and_fm_prf (Neg v) (Atom va) = PThm "all_conv"
  | dnf_and_fm_prf (Neg v) (And (va, vb)) = PThm "all_conv"
  | dnf_and_fm_prf (Neg v) (Neg va) = PThm "all_conv";

fun dnf_fm_prf (And (phi_1, phi_2)) =
  foldl (fn a => fn b => AppP (a, b)) (PThm "then_conv")
    [foldl (fn a => fn b => AppP (a, b)) (PThm "combination_conv")
       [AppP (PThm "arg_conv", hd [dnf_fm_prf phi_1, dnf_fm_prf phi_2]),
         hd (tl [dnf_fm_prf phi_1, dnf_fm_prf phi_2])],
      dnf_and_fm_prf (dnf_fm phi_1) (dnf_fm phi_2)]
  | dnf_fm_prf (Or (phi_1, phi_2)) =
    foldl (fn a => fn b => AppP (a, b)) (PThm "combination_conv")
      [AppP (PThm "arg_conv", hd [dnf_fm_prf phi_1, dnf_fm_prf phi_2]),
        hd (tl [dnf_fm_prf phi_1, dnf_fm_prf phi_2])]
  | dnf_fm_prf (Atom v) = PThm "all_conv"
  | dnf_fm_prf (Neg v) = PThm "all_conv";

fun of_alist A_ xs = foldr (fn (a, b) => update A_ a b) xs (emptya A_);

fun deneg (true, LESS (x, y)) =
  And (Atom (true, LEQ (x, y)), Atom (false, EQ (x, y)))
  | deneg (false, LESS (x, y)) = Atom (true, LEQ (y, x))
  | deneg (false, LEQ (x, y)) =
    And (Atom (true, LEQ (y, x)), Atom (false, EQ (y, x)))
  | deneg (false, EQ (v, vb)) = Atom (false, EQ (v, vb))
  | deneg (v, EQ (vb, vc)) = Atom (v, EQ (vb, vc))
  | deneg (true, LEQ (vb, vc)) = Atom (true, LEQ (vb, vc));

fun from_conj_prf trm_of_atom p (And (a, b)) =
  foldl (fn aa => fn ba => AppP (aa, ba)) (PThm "conjE")
    [Bound (trm_of_fm trm_of_atom (And (a, b))),
      AbsP (trm_of_fm trm_of_atom a,
             AbsP (trm_of_fm trm_of_atom b,
                    from_conj_prf trm_of_atom (from_conj_prf trm_of_atom p b)
                      a))]
  | from_conj_prf trm_of_atom p (Atom a) = p;

fun contr_fm_prf trm_of_atom contr_atom_prf (Or (c, d)) =
  (case (contr_fm_prf trm_of_atom contr_atom_prf c,
          contr_fm_prf trm_of_atom contr_atom_prf d)
    of (NONE, _) => NONE | (SOME _, NONE) => NONE
    | (SOME p1, SOME p2) =>
      SOME (foldl (fn a => fn b => AppP (a, b)) (PThm "disjE")
             [Bound (trm_of_fm trm_of_atom (Or (c, d))),
               AbsP (trm_of_fm trm_of_atom c, p1),
               AbsP (trm_of_fm trm_of_atom d, p2)]))
  | contr_fm_prf trm_of_atom contr_atom_prf (And (a, b)) =
    (case contr_atom_prf (conj_list (And (a, b))) of NONE => NONE
      | SOME p => SOME (from_conj_prf trm_of_atom p (And (a, b))))
  | contr_fm_prf trm_of_atom contr_atom_prf (Atom a) = contr_atom_prf [a];

fun deless (true, LESS (x, y)) =
  And (Atom (true, LEQ (x, y)), Atom (false, EQ (x, y)))
  | deless (false, LESS (x, y)) =
    Or (Atom (false, LEQ (x, y)), Atom (true, EQ (x, y)))
  | deless (false, EQ (v, vb)) = Atom (false, EQ (v, vb))
  | deless (false, LEQ (v, vb)) = Atom (false, LEQ (v, vb))
  | deless (v, EQ (vb, vc)) = Atom (v, EQ (vb, vc))
  | deless (v, LEQ (vb, vc)) = Atom (v, LEQ (vb, vc));

fun deneg_prf (true, LESS (x, y)) = PThm "less_le"
  | deneg_prf (false, LESS (x, y)) = PThm "nless_le"
  | deneg_prf (false, LEQ (x, y)) = PThm "nle_le"
  | deneg_prf (false, EQ (v, vb)) = PThm "all_conv"
  | deneg_prf (v, EQ (vb, vc)) = PThm "all_conv"
  | deneg_prf (true, LEQ (vb, vc)) = PThm "all_conv";

val one_nat : nat = Suc Zero_nat;

fun map_option f NONE = NONE
  | map_option f (SOME x2) = SOME (f x2);

fun deless_prf (true, LESS (x, y)) = PThm "less_le"
  | deless_prf (false, LESS (x, y)) = PThm "nless_le"
  | deless_prf (false, EQ (v, vb)) = PThm "all_conv"
  | deless_prf (false, LEQ (v, vb)) = PThm "all_conv"
  | deless_prf (v, EQ (vb, vc)) = PThm "all_conv"
  | deless_prf (v, LEQ (vb, vc)) = PThm "all_conv";

fun trm_of_oatom (EQ (x, y)) = App (App (Const "eq", Var x), Var y)
  | trm_of_oatom (LEQ (x, y)) = App (App (Const "le", Var x), Var y)
  | trm_of_oatom (LESS (x, y)) = App (App (Const "lt", Var x), Var y);

fun minus_nat (Suc m) (Suc n) = minus_nat m n
  | minus_nat Zero_nat n = Zero_nat
  | minus_nat m Zero_nat = m;

fun mapping_fold A_ f (Mapping t) a = fold A_ f t a;

fun relcomp1_mapping A_ (B1_, B2_) x y1 pxy pm pma =
  mapping_fold (linorder_prod B2_ B2_)
    (fn (y2, z) => fn pyz => fn pmb =>
      (if eq B1_ y1 y2 andalso not (eq B1_ y2 z)
        then update (linorder_prod A_ B2_) (x, z)
               (foldl (fn a => fn b => AppP (a, b)) (PThm "trans") [pxy, pyz])
               pmb
        else pmb))
    pm pma;

fun relcomp_mapping (A1_, A2_) pm1 pm2 pma =
  mapping_fold (linorder_prod A2_ A2_)
    (fn (x, y) => fn pxy => fn pm =>
      (if eq A1_ x y then pm
        else relcomp1_mapping A2_ (A1_, A2_) x y pxy pm2 pm))
    pm1 pma;

fun ntrancl_mapping (A1_, A2_) Zero_nat m = m
  | ntrancl_mapping (A1_, A2_) (Suc k) m =
    let
      val trclm = ntrancl_mapping (A1_, A2_) k m;
    in
      relcomp_mapping (A1_, A2_) trclm m trclm
    end;

fun trancl_mapping (A1_, A2_) m =
  ntrancl_mapping (A1_, A2_)
    (minus_nat (card (equal_prod A1_ A1_) (keysa (linorder_prod A2_ A2_) m))
      one_nat)
    m;

fun is_in_leq leqm l =
  let
    val (x, y) = l;
  in
    (if equal_inta x y then SOME (Appt (PThm "refl", Var x))
      else lookupa (linorder_prod linorder_int linorder_int) leqm l)
  end;

fun is_in_eq leqm l =
  let
    val (x, y) = l;
  in
    (case (is_in_leq leqm (x, y), is_in_leq leqm (y, x)) of (NONE, _) => NONE
      | (SOME _, NONE) => NONE
      | (SOME p1, SOME p2) =>
        SOME (foldl (fn a => fn b => AppP (a, b)) (PThm "antisym") [p1, p2]))
  end;

fun trm_of_oliteral (true, a) = trm_of_oatom a
  | trm_of_oliteral (false, a) = App (Const "Not", trm_of_oatom a);

fun contr1_list leqm (false, LEQ (x, y)) =
  map_option
    (fn a =>
      AppP (AppP (PThm "contr", Bound (trm_of_oliteral (false, LEQ (x, y)))),
             a))
    (is_in_leq leqm (x, y))
  | contr1_list leqm (false, EQ (x, y)) =
    map_option
      (fn a =>
        AppP (AppP (PThm "contr", Bound (trm_of_oliteral (false, EQ (x, y)))),
               a))
      (is_in_eq leqm (x, y))
  | contr1_list uu (true, va) = NONE
  | contr1_list uu (v, LESS (vb, vc)) = NONE;

fun contr_list_aux leqm [] = NONE
  | contr_list_aux leqm (l :: ls) =
    (case contr1_list leqm l of NONE => contr_list_aux leqm ls
      | SOME a => SOME a);

fun leq1_member_list (true, LEQ (x, y)) =
  [((x, y), Bound (trm_of_oliteral (true, LEQ (x, y))))]
  | leq1_member_list (true, EQ (x, y)) =
    [((x, y), AppP (PThm "eqD1", Bound (trm_of_oliteral (true, EQ (x, y))))),
      ((y, x), AppP (PThm "eqD2", Bound (trm_of_oliteral (true, EQ (x, y)))))]
  | leq1_member_list (false, va) = []
  | leq1_member_list (v, LESS (vb, vc)) = [];

fun leq1_list a = maps leq1_member_list a;

fun leq1_mapping a =
  of_alist (linorder_prod linorder_int linorder_int) (leq1_list a);

fun contr_list a =
  contr_list_aux (trancl_mapping (equal_int, linorder_int) (leq1_mapping a)) a;

fun contr_prf atom_conv phi =
  contr_fm_prf trm_of_oliteral contr_list (dnf_fm (amap_fm atom_conv phi));

fun amap_f_m_prf ap (Atom a) = AppP (PThm "atom_conv", ap a)
  | amap_f_m_prf ap (And (phi_1, phi_2)) =
    foldl (fn a => fn b => AppP (a, b)) (PThm "combination_conv")
      [AppP (PThm "arg_conv",
              hd [amap_f_m_prf ap phi_1, amap_f_m_prf ap phi_2]),
        hd (tl [amap_f_m_prf ap phi_1, amap_f_m_prf ap phi_2])]
  | amap_f_m_prf ap (Or (phi_1, phi_2)) =
    foldl (fn a => fn b => AppP (a, b)) (PThm "combination_conv")
      [AppP (PThm "arg_conv",
              hd [amap_f_m_prf ap phi_1, amap_f_m_prf ap phi_2]),
        hd (tl [amap_f_m_prf ap phi_1, amap_f_m_prf ap phi_2])]
  | amap_f_m_prf ap (Neg phi) = AppP (PThm "arg_conv", amap_f_m_prf ap phi);

fun lo_contr_prf phi =
  map_option
    ((fn a =>
       Conv (trm_of_fm trm_of_oliteral phi, amap_f_m_prf deneg_prf phi, a)) o
      (fn a =>
        Conv (trm_of_fm trm_of_oliteral (amap_fm deneg phi),
               dnf_fm_prf (amap_fm deneg phi), a)))
    (contr_prf deneg phi);

fun po_contr_prf phi =
  map_option
    ((fn a =>
       Conv (trm_of_fm trm_of_oliteral phi, amap_f_m_prf deless_prf phi, a)) o
      (fn a =>
        Conv (trm_of_fm trm_of_oliteral (amap_fm deless phi),
               dnf_fm_prf (amap_fm deless phi), a)))
    (contr_prf deless phi);

end; (*struct Order_Procedure*)

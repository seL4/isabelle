structure GeneratedCooper =
struct
nonfix oo;
fun nat i = if i < 0 then 0 else i;

val one_def0 : int = (0 + 1);

datatype num = C of int | Bound of int | CX of int * num | Neg of num
  | Add of num * num | Sub of num * num | Mul of int * num;

fun snd (a, b) = b;

fun negateSnd x = (fn (q, r) => (q, ~ r)) x;

fun minus_def2 z w = (z + ~ w);

fun adjust b =
  (fn (q, r) =>
    (if (0 <= minus_def2 r b) then (((2 * q) + 1), minus_def2 r b)
      else ((2 * q), r)));

fun negDivAlg a b =
    (if ((0 <= (a + b)) orelse (b <= 0)) then (~1, (a + b))
      else adjust b (negDivAlg a (2 * b)));

fun posDivAlg a b =
    (if ((a < b) orelse (b <= 0)) then (0, a)
      else adjust b (posDivAlg a (2 * b)));

fun divAlg x =
  (fn (a, b) =>
    (if (0 <= a)
      then (if (0 <= b) then posDivAlg a b
             else (if (a = 0) then (0, 0)
                    else negateSnd (negDivAlg (~ a) (~ b))))
      else (if (0 < b) then negDivAlg a b
             else negateSnd (posDivAlg (~ a) (~ b)))))
    x;

fun mod_def1 a b = snd (divAlg (a, b));

fun dvd m n = (mod_def1 n m = 0);

fun abs i = (if (i < 0) then ~ i else i);

fun less_def3 m n = ((m) < (n));

fun less_eq_def3 m n = Bool.not (less_def3 n m);

fun numadd (Add (Mul (c1, Bound n1), r1), Add (Mul (c2, Bound n2), r2)) =
    (if (n1 = n2)
      then let val c = (c1 + c2)
           in (if (c = 0) then numadd (r1, r2)
                else Add (Mul (c, Bound n1), numadd (r1, r2)))
           end
      else (if less_eq_def3 n1 n2
             then Add (Mul (c1, Bound n1),
                        numadd (r1, Add (Mul (c2, Bound n2), r2)))
             else Add (Mul (c2, Bound n2),
                        numadd (Add (Mul (c1, Bound n1), r1), r2))))
  | numadd (Add (Mul (c1, Bound n1), r1), C afq) =
    Add (Mul (c1, Bound n1), numadd (r1, C afq))
  | numadd (Add (Mul (c1, Bound n1), r1), Bound afr) =
    Add (Mul (c1, Bound n1), numadd (r1, Bound afr))
  | numadd (Add (Mul (c1, Bound n1), r1), CX (afs, aft)) =
    Add (Mul (c1, Bound n1), numadd (r1, CX (afs, aft)))
  | numadd (Add (Mul (c1, Bound n1), r1), Neg afu) =
    Add (Mul (c1, Bound n1), numadd (r1, Neg afu))
  | numadd (Add (Mul (c1, Bound n1), r1), Add (C agx, afw)) =
    Add (Mul (c1, Bound n1), numadd (r1, Add (C agx, afw)))
  | numadd (Add (Mul (c1, Bound n1), r1), Add (Bound agy, afw)) =
    Add (Mul (c1, Bound n1), numadd (r1, Add (Bound agy, afw)))
  | numadd (Add (Mul (c1, Bound n1), r1), Add (CX (agz, aha), afw)) =
    Add (Mul (c1, Bound n1), numadd (r1, Add (CX (agz, aha), afw)))
  | numadd (Add (Mul (c1, Bound n1), r1), Add (Neg ahb, afw)) =
    Add (Mul (c1, Bound n1), numadd (r1, Add (Neg ahb, afw)))
  | numadd (Add (Mul (c1, Bound n1), r1), Add (Add (ahc, ahd), afw)) =
    Add (Mul (c1, Bound n1), numadd (r1, Add (Add (ahc, ahd), afw)))
  | numadd (Add (Mul (c1, Bound n1), r1), Add (Sub (ahe, ahf), afw)) =
    Add (Mul (c1, Bound n1), numadd (r1, Add (Sub (ahe, ahf), afw)))
  | numadd (Add (Mul (c1, Bound n1), r1), Add (Mul (ahg, C aie), afw)) =
    Add (Mul (c1, Bound n1), numadd (r1, Add (Mul (ahg, C aie), afw)))
  | numadd (Add (Mul (c1, Bound n1), r1), Add (Mul (ahg, CX (aig, aih)), afw)) =
    Add (Mul (c1, Bound n1), numadd (r1, Add (Mul (ahg, CX (aig, aih)), afw)))
  | numadd (Add (Mul (c1, Bound n1), r1), Add (Mul (ahg, Neg aii), afw)) =
    Add (Mul (c1, Bound n1), numadd (r1, Add (Mul (ahg, Neg aii), afw)))
  | numadd
      (Add (Mul (c1, Bound n1), r1), Add (Mul (ahg, Add (aij, aik)), afw)) =
    Add (Mul (c1, Bound n1), numadd (r1, Add (Mul (ahg, Add (aij, aik)), afw)))
  | numadd
      (Add (Mul (c1, Bound n1), r1), Add (Mul (ahg, Sub (ail, aim)), afw)) =
    Add (Mul (c1, Bound n1), numadd (r1, Add (Mul (ahg, Sub (ail, aim)), afw)))
  | numadd
      (Add (Mul (c1, Bound n1), r1), Add (Mul (ahg, Mul (ain, aio)), afw)) =
    Add (Mul (c1, Bound n1), numadd (r1, Add (Mul (ahg, Mul (ain, aio)), afw)))
  | numadd (Add (Mul (c1, Bound n1), r1), Sub (afx, afy)) =
    Add (Mul (c1, Bound n1), numadd (r1, Sub (afx, afy)))
  | numadd (Add (Mul (c1, Bound n1), r1), Mul (afz, aga)) =
    Add (Mul (c1, Bound n1), numadd (r1, Mul (afz, aga)))
  | numadd (C w, Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (C w, r2))
  | numadd (Bound x, Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Bound x, r2))
  | numadd (CX (y, z), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (CX (y, z), r2))
  | numadd (Neg ab, Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Neg ab, r2))
  | numadd (Add (C li, ad), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Add (C li, ad), r2))
  | numadd (Add (Bound lj, ad), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Add (Bound lj, ad), r2))
  | numadd (Add (CX (lk, ll), ad), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Add (CX (lk, ll), ad), r2))
  | numadd (Add (Neg lm, ad), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Add (Neg lm, ad), r2))
  | numadd (Add (Add (ln, lo), ad), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Add (Add (ln, lo), ad), r2))
  | numadd (Add (Sub (lp, lq), ad), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Add (Sub (lp, lq), ad), r2))
  | numadd (Add (Mul (lr, C abv), ad), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Add (Mul (lr, C abv), ad), r2))
  | numadd (Add (Mul (lr, CX (abx, aby)), ad), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Add (Mul (lr, CX (abx, aby)), ad), r2))
  | numadd (Add (Mul (lr, Neg abz), ad), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Add (Mul (lr, Neg abz), ad), r2))
  | numadd (Add (Mul (lr, Add (aca, acb)), ad), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Add (Mul (lr, Add (aca, acb)), ad), r2))
  | numadd (Add (Mul (lr, Sub (acc, acd)), ad), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Add (Mul (lr, Sub (acc, acd)), ad), r2))
  | numadd (Add (Mul (lr, Mul (ace, acf)), ad), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Add (Mul (lr, Mul (ace, acf)), ad), r2))
  | numadd (Sub (ae, af), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Sub (ae, af), r2))
  | numadd (Mul (ag, ah), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Mul (ag, ah), r2))
  | numadd (C b1, C b2) = C (b1 + b2)
  | numadd (C ai, Bound bf) = Add (C ai, Bound bf)
  | numadd (C ai, CX (bg, bh)) = Add (C ai, CX (bg, bh))
  | numadd (C ai, Neg bi) = Add (C ai, Neg bi)
  | numadd (C ai, Add (C ca, bk)) = Add (C ai, Add (C ca, bk))
  | numadd (C ai, Add (Bound cb, bk)) = Add (C ai, Add (Bound cb, bk))
  | numadd (C ai, Add (CX (cc, cd), bk)) = Add (C ai, Add (CX (cc, cd), bk))
  | numadd (C ai, Add (Neg ce, bk)) = Add (C ai, Add (Neg ce, bk))
  | numadd (C ai, Add (Add (cf, cg), bk)) = Add (C ai, Add (Add (cf, cg), bk))
  | numadd (C ai, Add (Sub (ch, ci), bk)) = Add (C ai, Add (Sub (ch, ci), bk))
  | numadd (C ai, Add (Mul (cj, C cw), bk)) =
    Add (C ai, Add (Mul (cj, C cw), bk))
  | numadd (C ai, Add (Mul (cj, CX (cy, cz)), bk)) =
    Add (C ai, Add (Mul (cj, CX (cy, cz)), bk))
  | numadd (C ai, Add (Mul (cj, Neg da), bk)) =
    Add (C ai, Add (Mul (cj, Neg da), bk))
  | numadd (C ai, Add (Mul (cj, Add (db, dc)), bk)) =
    Add (C ai, Add (Mul (cj, Add (db, dc)), bk))
  | numadd (C ai, Add (Mul (cj, Sub (dd, de)), bk)) =
    Add (C ai, Add (Mul (cj, Sub (dd, de)), bk))
  | numadd (C ai, Add (Mul (cj, Mul (df, dg)), bk)) =
    Add (C ai, Add (Mul (cj, Mul (df, dg)), bk))
  | numadd (C ai, Sub (bl, bm)) = Add (C ai, Sub (bl, bm))
  | numadd (C ai, Mul (bn, bo)) = Add (C ai, Mul (bn, bo))
  | numadd (Bound aj, C ds) = Add (Bound aj, C ds)
  | numadd (Bound aj, Bound dt) = Add (Bound aj, Bound dt)
  | numadd (Bound aj, CX (du, dv)) = Add (Bound aj, CX (du, dv))
  | numadd (Bound aj, Neg dw) = Add (Bound aj, Neg dw)
  | numadd (Bound aj, Add (C eo, dy)) = Add (Bound aj, Add (C eo, dy))
  | numadd (Bound aj, Add (Bound ep, dy)) = Add (Bound aj, Add (Bound ep, dy))
  | numadd (Bound aj, Add (CX (eq, er), dy)) =
    Add (Bound aj, Add (CX (eq, er), dy))
  | numadd (Bound aj, Add (Neg es, dy)) = Add (Bound aj, Add (Neg es, dy))
  | numadd (Bound aj, Add (Add (et, eu), dy)) =
    Add (Bound aj, Add (Add (et, eu), dy))
  | numadd (Bound aj, Add (Sub (ev, ew), dy)) =
    Add (Bound aj, Add (Sub (ev, ew), dy))
  | numadd (Bound aj, Add (Mul (ex, C fk), dy)) =
    Add (Bound aj, Add (Mul (ex, C fk), dy))
  | numadd (Bound aj, Add (Mul (ex, CX (fm, fn')), dy)) =
    Add (Bound aj, Add (Mul (ex, CX (fm, fn')), dy))
  | numadd (Bound aj, Add (Mul (ex, Neg fo), dy)) =
    Add (Bound aj, Add (Mul (ex, Neg fo), dy))
  | numadd (Bound aj, Add (Mul (ex, Add (fp, fq)), dy)) =
    Add (Bound aj, Add (Mul (ex, Add (fp, fq)), dy))
  | numadd (Bound aj, Add (Mul (ex, Sub (fr, fs)), dy)) =
    Add (Bound aj, Add (Mul (ex, Sub (fr, fs)), dy))
  | numadd (Bound aj, Add (Mul (ex, Mul (ft, fu)), dy)) =
    Add (Bound aj, Add (Mul (ex, Mul (ft, fu)), dy))
  | numadd (Bound aj, Sub (dz, ea)) = Add (Bound aj, Sub (dz, ea))
  | numadd (Bound aj, Mul (eb, ec)) = Add (Bound aj, Mul (eb, ec))
  | numadd (CX (ak, al), C gg) = Add (CX (ak, al), C gg)
  | numadd (CX (ak, al), Bound gh) = Add (CX (ak, al), Bound gh)
  | numadd (CX (ak, al), CX (gi, gj)) = Add (CX (ak, al), CX (gi, gj))
  | numadd (CX (ak, al), Neg gk) = Add (CX (ak, al), Neg gk)
  | numadd (CX (ak, al), Add (C hc, gm)) = Add (CX (ak, al), Add (C hc, gm))
  | numadd (CX (ak, al), Add (Bound hd, gm)) =
    Add (CX (ak, al), Add (Bound hd, gm))
  | numadd (CX (ak, al), Add (CX (he, hf), gm)) =
    Add (CX (ak, al), Add (CX (he, hf), gm))
  | numadd (CX (ak, al), Add (Neg hg, gm)) = Add (CX (ak, al), Add (Neg hg, gm))
  | numadd (CX (ak, al), Add (Add (hh, hi), gm)) =
    Add (CX (ak, al), Add (Add (hh, hi), gm))
  | numadd (CX (ak, al), Add (Sub (hj, hk), gm)) =
    Add (CX (ak, al), Add (Sub (hj, hk), gm))
  | numadd (CX (ak, al), Add (Mul (hl, C hy), gm)) =
    Add (CX (ak, al), Add (Mul (hl, C hy), gm))
  | numadd (CX (ak, al), Add (Mul (hl, CX (ia, ib)), gm)) =
    Add (CX (ak, al), Add (Mul (hl, CX (ia, ib)), gm))
  | numadd (CX (ak, al), Add (Mul (hl, Neg ic), gm)) =
    Add (CX (ak, al), Add (Mul (hl, Neg ic), gm))
  | numadd (CX (ak, al), Add (Mul (hl, Add (id, ie)), gm)) =
    Add (CX (ak, al), Add (Mul (hl, Add (id, ie)), gm))
  | numadd (CX (ak, al), Add (Mul (hl, Sub (if', ig)), gm)) =
    Add (CX (ak, al), Add (Mul (hl, Sub (if', ig)), gm))
  | numadd (CX (ak, al), Add (Mul (hl, Mul (ih, ii)), gm)) =
    Add (CX (ak, al), Add (Mul (hl, Mul (ih, ii)), gm))
  | numadd (CX (ak, al), Sub (gn, go)) = Add (CX (ak, al), Sub (gn, go))
  | numadd (CX (ak, al), Mul (gp, gq)) = Add (CX (ak, al), Mul (gp, gq))
  | numadd (Neg am, C iu) = Add (Neg am, C iu)
  | numadd (Neg am, Bound iv) = Add (Neg am, Bound iv)
  | numadd (Neg am, CX (iw, ix)) = Add (Neg am, CX (iw, ix))
  | numadd (Neg am, Neg iy) = Add (Neg am, Neg iy)
  | numadd (Neg am, Add (C jq, ja)) = Add (Neg am, Add (C jq, ja))
  | numadd (Neg am, Add (Bound jr, ja)) = Add (Neg am, Add (Bound jr, ja))
  | numadd (Neg am, Add (CX (js, jt), ja)) = Add (Neg am, Add (CX (js, jt), ja))
  | numadd (Neg am, Add (Neg ju, ja)) = Add (Neg am, Add (Neg ju, ja))
  | numadd (Neg am, Add (Add (jv, jw), ja)) =
    Add (Neg am, Add (Add (jv, jw), ja))
  | numadd (Neg am, Add (Sub (jx, jy), ja)) =
    Add (Neg am, Add (Sub (jx, jy), ja))
  | numadd (Neg am, Add (Mul (jz, C km), ja)) =
    Add (Neg am, Add (Mul (jz, C km), ja))
  | numadd (Neg am, Add (Mul (jz, CX (ko, kp)), ja)) =
    Add (Neg am, Add (Mul (jz, CX (ko, kp)), ja))
  | numadd (Neg am, Add (Mul (jz, Neg kq), ja)) =
    Add (Neg am, Add (Mul (jz, Neg kq), ja))
  | numadd (Neg am, Add (Mul (jz, Add (kr, ks)), ja)) =
    Add (Neg am, Add (Mul (jz, Add (kr, ks)), ja))
  | numadd (Neg am, Add (Mul (jz, Sub (kt, ku)), ja)) =
    Add (Neg am, Add (Mul (jz, Sub (kt, ku)), ja))
  | numadd (Neg am, Add (Mul (jz, Mul (kv, kw)), ja)) =
    Add (Neg am, Add (Mul (jz, Mul (kv, kw)), ja))
  | numadd (Neg am, Sub (jb, jc)) = Add (Neg am, Sub (jb, jc))
  | numadd (Neg am, Mul (jd, je)) = Add (Neg am, Mul (jd, je))
  | numadd (Add (C lt, ao), C mp) = Add (Add (C lt, ao), C mp)
  | numadd (Add (C lt, ao), Bound mq) = Add (Add (C lt, ao), Bound mq)
  | numadd (Add (C lt, ao), CX (mr, ms)) = Add (Add (C lt, ao), CX (mr, ms))
  | numadd (Add (C lt, ao), Neg mt) = Add (Add (C lt, ao), Neg mt)
  | numadd (Add (C lt, ao), Add (C nl, mv)) =
    Add (Add (C lt, ao), Add (C nl, mv))
  | numadd (Add (C lt, ao), Add (Bound nm, mv)) =
    Add (Add (C lt, ao), Add (Bound nm, mv))
  | numadd (Add (C lt, ao), Add (CX (nn, no), mv)) =
    Add (Add (C lt, ao), Add (CX (nn, no), mv))
  | numadd (Add (C lt, ao), Add (Neg np, mv)) =
    Add (Add (C lt, ao), Add (Neg np, mv))
  | numadd (Add (C lt, ao), Add (Add (nq, nr), mv)) =
    Add (Add (C lt, ao), Add (Add (nq, nr), mv))
  | numadd (Add (C lt, ao), Add (Sub (ns, nt), mv)) =
    Add (Add (C lt, ao), Add (Sub (ns, nt), mv))
  | numadd (Add (C lt, ao), Add (Mul (nu, C oh), mv)) =
    Add (Add (C lt, ao), Add (Mul (nu, C oh), mv))
  | numadd (Add (C lt, ao), Add (Mul (nu, CX (oj, ok)), mv)) =
    Add (Add (C lt, ao), Add (Mul (nu, CX (oj, ok)), mv))
  | numadd (Add (C lt, ao), Add (Mul (nu, Neg ol), mv)) =
    Add (Add (C lt, ao), Add (Mul (nu, Neg ol), mv))
  | numadd (Add (C lt, ao), Add (Mul (nu, Add (om, on)), mv)) =
    Add (Add (C lt, ao), Add (Mul (nu, Add (om, on)), mv))
  | numadd (Add (C lt, ao), Add (Mul (nu, Sub (oo, op')), mv)) =
    Add (Add (C lt, ao), Add (Mul (nu, Sub (oo, op')), mv))
  | numadd (Add (C lt, ao), Add (Mul (nu, Mul (oq, or)), mv)) =
    Add (Add (C lt, ao), Add (Mul (nu, Mul (oq, or)), mv))
  | numadd (Add (C lt, ao), Sub (mw, mx)) = Add (Add (C lt, ao), Sub (mw, mx))
  | numadd (Add (C lt, ao), Mul (my, mz)) = Add (Add (C lt, ao), Mul (my, mz))
  | numadd (Add (Bound lu, ao), C pd) = Add (Add (Bound lu, ao), C pd)
  | numadd (Add (Bound lu, ao), Bound pe) = Add (Add (Bound lu, ao), Bound pe)
  | numadd (Add (Bound lu, ao), CX (pf, pg)) =
    Add (Add (Bound lu, ao), CX (pf, pg))
  | numadd (Add (Bound lu, ao), Neg ph) = Add (Add (Bound lu, ao), Neg ph)
  | numadd (Add (Bound lu, ao), Add (C pz, pj)) =
    Add (Add (Bound lu, ao), Add (C pz, pj))
  | numadd (Add (Bound lu, ao), Add (Bound qa, pj)) =
    Add (Add (Bound lu, ao), Add (Bound qa, pj))
  | numadd (Add (Bound lu, ao), Add (CX (qb, qc), pj)) =
    Add (Add (Bound lu, ao), Add (CX (qb, qc), pj))
  | numadd (Add (Bound lu, ao), Add (Neg qd, pj)) =
    Add (Add (Bound lu, ao), Add (Neg qd, pj))
  | numadd (Add (Bound lu, ao), Add (Add (qe, qf), pj)) =
    Add (Add (Bound lu, ao), Add (Add (qe, qf), pj))
  | numadd (Add (Bound lu, ao), Add (Sub (qg, qh), pj)) =
    Add (Add (Bound lu, ao), Add (Sub (qg, qh), pj))
  | numadd (Add (Bound lu, ao), Add (Mul (qi, C qv), pj)) =
    Add (Add (Bound lu, ao), Add (Mul (qi, C qv), pj))
  | numadd (Add (Bound lu, ao), Add (Mul (qi, CX (qx, qy)), pj)) =
    Add (Add (Bound lu, ao), Add (Mul (qi, CX (qx, qy)), pj))
  | numadd (Add (Bound lu, ao), Add (Mul (qi, Neg qz), pj)) =
    Add (Add (Bound lu, ao), Add (Mul (qi, Neg qz), pj))
  | numadd (Add (Bound lu, ao), Add (Mul (qi, Add (ra, rb)), pj)) =
    Add (Add (Bound lu, ao), Add (Mul (qi, Add (ra, rb)), pj))
  | numadd (Add (Bound lu, ao), Add (Mul (qi, Sub (rc, rd)), pj)) =
    Add (Add (Bound lu, ao), Add (Mul (qi, Sub (rc, rd)), pj))
  | numadd (Add (Bound lu, ao), Add (Mul (qi, Mul (re, rf)), pj)) =
    Add (Add (Bound lu, ao), Add (Mul (qi, Mul (re, rf)), pj))
  | numadd (Add (Bound lu, ao), Sub (pk, pl)) =
    Add (Add (Bound lu, ao), Sub (pk, pl))
  | numadd (Add (Bound lu, ao), Mul (pm, pn)) =
    Add (Add (Bound lu, ao), Mul (pm, pn))
  | numadd (Add (CX (lv, lw), ao), C rr) = Add (Add (CX (lv, lw), ao), C rr)
  | numadd (Add (CX (lv, lw), ao), Bound rs) =
    Add (Add (CX (lv, lw), ao), Bound rs)
  | numadd (Add (CX (lv, lw), ao), CX (rt, ru)) =
    Add (Add (CX (lv, lw), ao), CX (rt, ru))
  | numadd (Add (CX (lv, lw), ao), Neg rv) = Add (Add (CX (lv, lw), ao), Neg rv)
  | numadd (Add (CX (lv, lw), ao), Add (C sn, rx)) =
    Add (Add (CX (lv, lw), ao), Add (C sn, rx))
  | numadd (Add (CX (lv, lw), ao), Add (Bound so, rx)) =
    Add (Add (CX (lv, lw), ao), Add (Bound so, rx))
  | numadd (Add (CX (lv, lw), ao), Add (CX (sp, sq), rx)) =
    Add (Add (CX (lv, lw), ao), Add (CX (sp, sq), rx))
  | numadd (Add (CX (lv, lw), ao), Add (Neg sr, rx)) =
    Add (Add (CX (lv, lw), ao), Add (Neg sr, rx))
  | numadd (Add (CX (lv, lw), ao), Add (Add (ss, st), rx)) =
    Add (Add (CX (lv, lw), ao), Add (Add (ss, st), rx))
  | numadd (Add (CX (lv, lw), ao), Add (Sub (su, sv), rx)) =
    Add (Add (CX (lv, lw), ao), Add (Sub (su, sv), rx))
  | numadd (Add (CX (lv, lw), ao), Add (Mul (sw, C tj), rx)) =
    Add (Add (CX (lv, lw), ao), Add (Mul (sw, C tj), rx))
  | numadd (Add (CX (lv, lw), ao), Add (Mul (sw, CX (tl, tm)), rx)) =
    Add (Add (CX (lv, lw), ao), Add (Mul (sw, CX (tl, tm)), rx))
  | numadd (Add (CX (lv, lw), ao), Add (Mul (sw, Neg tn), rx)) =
    Add (Add (CX (lv, lw), ao), Add (Mul (sw, Neg tn), rx))
  | numadd (Add (CX (lv, lw), ao), Add (Mul (sw, Add (to, tp)), rx)) =
    Add (Add (CX (lv, lw), ao), Add (Mul (sw, Add (to, tp)), rx))
  | numadd (Add (CX (lv, lw), ao), Add (Mul (sw, Sub (tq, tr)), rx)) =
    Add (Add (CX (lv, lw), ao), Add (Mul (sw, Sub (tq, tr)), rx))
  | numadd (Add (CX (lv, lw), ao), Add (Mul (sw, Mul (ts, tt)), rx)) =
    Add (Add (CX (lv, lw), ao), Add (Mul (sw, Mul (ts, tt)), rx))
  | numadd (Add (CX (lv, lw), ao), Sub (ry, rz)) =
    Add (Add (CX (lv, lw), ao), Sub (ry, rz))
  | numadd (Add (CX (lv, lw), ao), Mul (sa, sb)) =
    Add (Add (CX (lv, lw), ao), Mul (sa, sb))
  | numadd (Add (Neg lx, ao), C uf) = Add (Add (Neg lx, ao), C uf)
  | numadd (Add (Neg lx, ao), Bound ug) = Add (Add (Neg lx, ao), Bound ug)
  | numadd (Add (Neg lx, ao), CX (uh, ui)) = Add (Add (Neg lx, ao), CX (uh, ui))
  | numadd (Add (Neg lx, ao), Neg uj) = Add (Add (Neg lx, ao), Neg uj)
  | numadd (Add (Neg lx, ao), Add (C vb, ul)) =
    Add (Add (Neg lx, ao), Add (C vb, ul))
  | numadd (Add (Neg lx, ao), Add (Bound vc, ul)) =
    Add (Add (Neg lx, ao), Add (Bound vc, ul))
  | numadd (Add (Neg lx, ao), Add (CX (vd, ve), ul)) =
    Add (Add (Neg lx, ao), Add (CX (vd, ve), ul))
  | numadd (Add (Neg lx, ao), Add (Neg vf, ul)) =
    Add (Add (Neg lx, ao), Add (Neg vf, ul))
  | numadd (Add (Neg lx, ao), Add (Add (vg, vh), ul)) =
    Add (Add (Neg lx, ao), Add (Add (vg, vh), ul))
  | numadd (Add (Neg lx, ao), Add (Sub (vi, vj), ul)) =
    Add (Add (Neg lx, ao), Add (Sub (vi, vj), ul))
  | numadd (Add (Neg lx, ao), Add (Mul (vk, C vx), ul)) =
    Add (Add (Neg lx, ao), Add (Mul (vk, C vx), ul))
  | numadd (Add (Neg lx, ao), Add (Mul (vk, CX (vz, wa)), ul)) =
    Add (Add (Neg lx, ao), Add (Mul (vk, CX (vz, wa)), ul))
  | numadd (Add (Neg lx, ao), Add (Mul (vk, Neg wb), ul)) =
    Add (Add (Neg lx, ao), Add (Mul (vk, Neg wb), ul))
  | numadd (Add (Neg lx, ao), Add (Mul (vk, Add (wc, wd)), ul)) =
    Add (Add (Neg lx, ao), Add (Mul (vk, Add (wc, wd)), ul))
  | numadd (Add (Neg lx, ao), Add (Mul (vk, Sub (we, wf)), ul)) =
    Add (Add (Neg lx, ao), Add (Mul (vk, Sub (we, wf)), ul))
  | numadd (Add (Neg lx, ao), Add (Mul (vk, Mul (wg, wh)), ul)) =
    Add (Add (Neg lx, ao), Add (Mul (vk, Mul (wg, wh)), ul))
  | numadd (Add (Neg lx, ao), Sub (um, un)) =
    Add (Add (Neg lx, ao), Sub (um, un))
  | numadd (Add (Neg lx, ao), Mul (uo, up)) =
    Add (Add (Neg lx, ao), Mul (uo, up))
  | numadd (Add (Add (ly, lz), ao), C wt) = Add (Add (Add (ly, lz), ao), C wt)
  | numadd (Add (Add (ly, lz), ao), Bound wu) =
    Add (Add (Add (ly, lz), ao), Bound wu)
  | numadd (Add (Add (ly, lz), ao), CX (wv, ww)) =
    Add (Add (Add (ly, lz), ao), CX (wv, ww))
  | numadd (Add (Add (ly, lz), ao), Neg wx) =
    Add (Add (Add (ly, lz), ao), Neg wx)
  | numadd (Add (Add (ly, lz), ao), Add (C xp, wz)) =
    Add (Add (Add (ly, lz), ao), Add (C xp, wz))
  | numadd (Add (Add (ly, lz), ao), Add (Bound xq, wz)) =
    Add (Add (Add (ly, lz), ao), Add (Bound xq, wz))
  | numadd (Add (Add (ly, lz), ao), Add (CX (xr, xs), wz)) =
    Add (Add (Add (ly, lz), ao), Add (CX (xr, xs), wz))
  | numadd (Add (Add (ly, lz), ao), Add (Neg xt, wz)) =
    Add (Add (Add (ly, lz), ao), Add (Neg xt, wz))
  | numadd (Add (Add (ly, lz), ao), Add (Add (xu, xv), wz)) =
    Add (Add (Add (ly, lz), ao), Add (Add (xu, xv), wz))
  | numadd (Add (Add (ly, lz), ao), Add (Sub (xw, xx), wz)) =
    Add (Add (Add (ly, lz), ao), Add (Sub (xw, xx), wz))
  | numadd (Add (Add (ly, lz), ao), Add (Mul (xy, C yl), wz)) =
    Add (Add (Add (ly, lz), ao), Add (Mul (xy, C yl), wz))
  | numadd (Add (Add (ly, lz), ao), Add (Mul (xy, CX (yn, yo)), wz)) =
    Add (Add (Add (ly, lz), ao), Add (Mul (xy, CX (yn, yo)), wz))
  | numadd (Add (Add (ly, lz), ao), Add (Mul (xy, Neg yp), wz)) =
    Add (Add (Add (ly, lz), ao), Add (Mul (xy, Neg yp), wz))
  | numadd (Add (Add (ly, lz), ao), Add (Mul (xy, Add (yq, yr)), wz)) =
    Add (Add (Add (ly, lz), ao), Add (Mul (xy, Add (yq, yr)), wz))
  | numadd (Add (Add (ly, lz), ao), Add (Mul (xy, Sub (ys, yt)), wz)) =
    Add (Add (Add (ly, lz), ao), Add (Mul (xy, Sub (ys, yt)), wz))
  | numadd (Add (Add (ly, lz), ao), Add (Mul (xy, Mul (yu, yv)), wz)) =
    Add (Add (Add (ly, lz), ao), Add (Mul (xy, Mul (yu, yv)), wz))
  | numadd (Add (Add (ly, lz), ao), Sub (xa, xb)) =
    Add (Add (Add (ly, lz), ao), Sub (xa, xb))
  | numadd (Add (Add (ly, lz), ao), Mul (xc, xd)) =
    Add (Add (Add (ly, lz), ao), Mul (xc, xd))
  | numadd (Add (Sub (ma, mb), ao), C zh) = Add (Add (Sub (ma, mb), ao), C zh)
  | numadd (Add (Sub (ma, mb), ao), Bound zi) =
    Add (Add (Sub (ma, mb), ao), Bound zi)
  | numadd (Add (Sub (ma, mb), ao), CX (zj, zk)) =
    Add (Add (Sub (ma, mb), ao), CX (zj, zk))
  | numadd (Add (Sub (ma, mb), ao), Neg zl) =
    Add (Add (Sub (ma, mb), ao), Neg zl)
  | numadd (Add (Sub (ma, mb), ao), Add (C aad, zn)) =
    Add (Add (Sub (ma, mb), ao), Add (C aad, zn))
  | numadd (Add (Sub (ma, mb), ao), Add (Bound aae, zn)) =
    Add (Add (Sub (ma, mb), ao), Add (Bound aae, zn))
  | numadd (Add (Sub (ma, mb), ao), Add (CX (aaf, aag), zn)) =
    Add (Add (Sub (ma, mb), ao), Add (CX (aaf, aag), zn))
  | numadd (Add (Sub (ma, mb), ao), Add (Neg aah, zn)) =
    Add (Add (Sub (ma, mb), ao), Add (Neg aah, zn))
  | numadd (Add (Sub (ma, mb), ao), Add (Add (aai, aaj), zn)) =
    Add (Add (Sub (ma, mb), ao), Add (Add (aai, aaj), zn))
  | numadd (Add (Sub (ma, mb), ao), Add (Sub (aak, aal), zn)) =
    Add (Add (Sub (ma, mb), ao), Add (Sub (aak, aal), zn))
  | numadd (Add (Sub (ma, mb), ao), Add (Mul (aam, C aaz), zn)) =
    Add (Add (Sub (ma, mb), ao), Add (Mul (aam, C aaz), zn))
  | numadd (Add (Sub (ma, mb), ao), Add (Mul (aam, CX (abb, abc)), zn)) =
    Add (Add (Sub (ma, mb), ao), Add (Mul (aam, CX (abb, abc)), zn))
  | numadd (Add (Sub (ma, mb), ao), Add (Mul (aam, Neg abd), zn)) =
    Add (Add (Sub (ma, mb), ao), Add (Mul (aam, Neg abd), zn))
  | numadd (Add (Sub (ma, mb), ao), Add (Mul (aam, Add (abe, abf)), zn)) =
    Add (Add (Sub (ma, mb), ao), Add (Mul (aam, Add (abe, abf)), zn))
  | numadd (Add (Sub (ma, mb), ao), Add (Mul (aam, Sub (abg, abh)), zn)) =
    Add (Add (Sub (ma, mb), ao), Add (Mul (aam, Sub (abg, abh)), zn))
  | numadd (Add (Sub (ma, mb), ao), Add (Mul (aam, Mul (abi, abj)), zn)) =
    Add (Add (Sub (ma, mb), ao), Add (Mul (aam, Mul (abi, abj)), zn))
  | numadd (Add (Sub (ma, mb), ao), Sub (zo, zp)) =
    Add (Add (Sub (ma, mb), ao), Sub (zo, zp))
  | numadd (Add (Sub (ma, mb), ao), Mul (zq, zr)) =
    Add (Add (Sub (ma, mb), ao), Mul (zq, zr))
  | numadd (Add (Mul (mc, C acg), ao), C adc) =
    Add (Add (Mul (mc, C acg), ao), C adc)
  | numadd (Add (Mul (mc, C acg), ao), Bound add) =
    Add (Add (Mul (mc, C acg), ao), Bound add)
  | numadd (Add (Mul (mc, C acg), ao), CX (ade, adf)) =
    Add (Add (Mul (mc, C acg), ao), CX (ade, adf))
  | numadd (Add (Mul (mc, C acg), ao), Neg adg) =
    Add (Add (Mul (mc, C acg), ao), Neg adg)
  | numadd (Add (Mul (mc, C acg), ao), Add (C ady, adi)) =
    Add (Add (Mul (mc, C acg), ao), Add (C ady, adi))
  | numadd (Add (Mul (mc, C acg), ao), Add (Bound adz, adi)) =
    Add (Add (Mul (mc, C acg), ao), Add (Bound adz, adi))
  | numadd (Add (Mul (mc, C acg), ao), Add (CX (aea, aeb), adi)) =
    Add (Add (Mul (mc, C acg), ao), Add (CX (aea, aeb), adi))
  | numadd (Add (Mul (mc, C acg), ao), Add (Neg aec, adi)) =
    Add (Add (Mul (mc, C acg), ao), Add (Neg aec, adi))
  | numadd (Add (Mul (mc, C acg), ao), Add (Add (aed, aee), adi)) =
    Add (Add (Mul (mc, C acg), ao), Add (Add (aed, aee), adi))
  | numadd (Add (Mul (mc, C acg), ao), Add (Sub (aef, aeg), adi)) =
    Add (Add (Mul (mc, C acg), ao), Add (Sub (aef, aeg), adi))
  | numadd (Add (Mul (mc, C acg), ao), Add (Mul (aeh, C aeu), adi)) =
    Add (Add (Mul (mc, C acg), ao), Add (Mul (aeh, C aeu), adi))
  | numadd (Add (Mul (mc, C acg), ao), Add (Mul (aeh, CX (aew, aex)), adi)) =
    Add (Add (Mul (mc, C acg), ao), Add (Mul (aeh, CX (aew, aex)), adi))
  | numadd (Add (Mul (mc, C acg), ao), Add (Mul (aeh, Neg aey), adi)) =
    Add (Add (Mul (mc, C acg), ao), Add (Mul (aeh, Neg aey), adi))
  | numadd (Add (Mul (mc, C acg), ao), Add (Mul (aeh, Add (aez, afa)), adi)) =
    Add (Add (Mul (mc, C acg), ao), Add (Mul (aeh, Add (aez, afa)), adi))
  | numadd (Add (Mul (mc, C acg), ao), Add (Mul (aeh, Sub (afb, afc)), adi)) =
    Add (Add (Mul (mc, C acg), ao), Add (Mul (aeh, Sub (afb, afc)), adi))
  | numadd (Add (Mul (mc, C acg), ao), Add (Mul (aeh, Mul (afd, afe)), adi)) =
    Add (Add (Mul (mc, C acg), ao), Add (Mul (aeh, Mul (afd, afe)), adi))
  | numadd (Add (Mul (mc, C acg), ao), Sub (adj, adk)) =
    Add (Add (Mul (mc, C acg), ao), Sub (adj, adk))
  | numadd (Add (Mul (mc, C acg), ao), Mul (adl, adm)) =
    Add (Add (Mul (mc, C acg), ao), Mul (adl, adm))
  | numadd (Add (Mul (mc, CX (aci, acj)), ao), C ajl) =
    Add (Add (Mul (mc, CX (aci, acj)), ao), C ajl)
  | numadd (Add (Mul (mc, CX (aci, acj)), ao), Bound ajm) =
    Add (Add (Mul (mc, CX (aci, acj)), ao), Bound ajm)
  | numadd (Add (Mul (mc, CX (aci, acj)), ao), CX (ajn, ajo)) =
    Add (Add (Mul (mc, CX (aci, acj)), ao), CX (ajn, ajo))
  | numadd (Add (Mul (mc, CX (aci, acj)), ao), Neg ajp) =
    Add (Add (Mul (mc, CX (aci, acj)), ao), Neg ajp)
  | numadd (Add (Mul (mc, CX (aci, acj)), ao), Add (C akh, ajr)) =
    Add (Add (Mul (mc, CX (aci, acj)), ao), Add (C akh, ajr))
  | numadd (Add (Mul (mc, CX (aci, acj)), ao), Add (Bound aki, ajr)) =
    Add (Add (Mul (mc, CX (aci, acj)), ao), Add (Bound aki, ajr))
  | numadd (Add (Mul (mc, CX (aci, acj)), ao), Add (CX (akj, akk), ajr)) =
    Add (Add (Mul (mc, CX (aci, acj)), ao), Add (CX (akj, akk), ajr))
  | numadd (Add (Mul (mc, CX (aci, acj)), ao), Add (Neg akl, ajr)) =
    Add (Add (Mul (mc, CX (aci, acj)), ao), Add (Neg akl, ajr))
  | numadd (Add (Mul (mc, CX (aci, acj)), ao), Add (Add (akm, akn), ajr)) =
    Add (Add (Mul (mc, CX (aci, acj)), ao), Add (Add (akm, akn), ajr))
  | numadd (Add (Mul (mc, CX (aci, acj)), ao), Add (Sub (ako, akp), ajr)) =
    Add (Add (Mul (mc, CX (aci, acj)), ao), Add (Sub (ako, akp), ajr))
  | numadd (Add (Mul (mc, CX (aci, acj)), ao), Add (Mul (akq, C ald), ajr)) =
    Add (Add (Mul (mc, CX (aci, acj)), ao), Add (Mul (akq, C ald), ajr))
  | numadd
      (Add (Mul (mc, CX (aci, acj)), ao), Add (Mul (akq, CX (alf, alg)), ajr)) =
    Add (Add (Mul (mc, CX (aci, acj)), ao), Add (Mul (akq, CX (alf, alg)), ajr))
  | numadd (Add (Mul (mc, CX (aci, acj)), ao), Add (Mul (akq, Neg alh), ajr)) =
    Add (Add (Mul (mc, CX (aci, acj)), ao), Add (Mul (akq, Neg alh), ajr))
  | numadd
      (Add (Mul (mc, CX (aci, acj)), ao),
        Add (Mul (akq, Add (ali, alj)), ajr)) =
    Add (Add (Mul (mc, CX (aci, acj)), ao),
          Add (Mul (akq, Add (ali, alj)), ajr))
  | numadd
      (Add (Mul (mc, CX (aci, acj)), ao),
        Add (Mul (akq, Sub (alk, all)), ajr)) =
    Add (Add (Mul (mc, CX (aci, acj)), ao),
          Add (Mul (akq, Sub (alk, all)), ajr))
  | numadd
      (Add (Mul (mc, CX (aci, acj)), ao),
        Add (Mul (akq, Mul (alm, aln)), ajr)) =
    Add (Add (Mul (mc, CX (aci, acj)), ao),
          Add (Mul (akq, Mul (alm, aln)), ajr))
  | numadd (Add (Mul (mc, CX (aci, acj)), ao), Sub (ajs, ajt)) =
    Add (Add (Mul (mc, CX (aci, acj)), ao), Sub (ajs, ajt))
  | numadd (Add (Mul (mc, CX (aci, acj)), ao), Mul (aju, ajv)) =
    Add (Add (Mul (mc, CX (aci, acj)), ao), Mul (aju, ajv))
  | numadd (Add (Mul (mc, Neg ack), ao), C alz) =
    Add (Add (Mul (mc, Neg ack), ao), C alz)
  | numadd (Add (Mul (mc, Neg ack), ao), Bound ama) =
    Add (Add (Mul (mc, Neg ack), ao), Bound ama)
  | numadd (Add (Mul (mc, Neg ack), ao), CX (amb, amc)) =
    Add (Add (Mul (mc, Neg ack), ao), CX (amb, amc))
  | numadd (Add (Mul (mc, Neg ack), ao), Neg amd) =
    Add (Add (Mul (mc, Neg ack), ao), Neg amd)
  | numadd (Add (Mul (mc, Neg ack), ao), Add (C amv, amf)) =
    Add (Add (Mul (mc, Neg ack), ao), Add (C amv, amf))
  | numadd (Add (Mul (mc, Neg ack), ao), Add (Bound amw, amf)) =
    Add (Add (Mul (mc, Neg ack), ao), Add (Bound amw, amf))
  | numadd (Add (Mul (mc, Neg ack), ao), Add (CX (amx, amy), amf)) =
    Add (Add (Mul (mc, Neg ack), ao), Add (CX (amx, amy), amf))
  | numadd (Add (Mul (mc, Neg ack), ao), Add (Neg amz, amf)) =
    Add (Add (Mul (mc, Neg ack), ao), Add (Neg amz, amf))
  | numadd (Add (Mul (mc, Neg ack), ao), Add (Add (ana, anb), amf)) =
    Add (Add (Mul (mc, Neg ack), ao), Add (Add (ana, anb), amf))
  | numadd (Add (Mul (mc, Neg ack), ao), Add (Sub (anc, and'), amf)) =
    Add (Add (Mul (mc, Neg ack), ao), Add (Sub (anc, and'), amf))
  | numadd (Add (Mul (mc, Neg ack), ao), Add (Mul (ane, C anr), amf)) =
    Add (Add (Mul (mc, Neg ack), ao), Add (Mul (ane, C anr), amf))
  | numadd (Add (Mul (mc, Neg ack), ao), Add (Mul (ane, CX (ant, anu)), amf)) =
    Add (Add (Mul (mc, Neg ack), ao), Add (Mul (ane, CX (ant, anu)), amf))
  | numadd (Add (Mul (mc, Neg ack), ao), Add (Mul (ane, Neg anv), amf)) =
    Add (Add (Mul (mc, Neg ack), ao), Add (Mul (ane, Neg anv), amf))
  | numadd (Add (Mul (mc, Neg ack), ao), Add (Mul (ane, Add (anw, anx)), amf)) =
    Add (Add (Mul (mc, Neg ack), ao), Add (Mul (ane, Add (anw, anx)), amf))
  | numadd (Add (Mul (mc, Neg ack), ao), Add (Mul (ane, Sub (any, anz)), amf)) =
    Add (Add (Mul (mc, Neg ack), ao), Add (Mul (ane, Sub (any, anz)), amf))
  | numadd (Add (Mul (mc, Neg ack), ao), Add (Mul (ane, Mul (aoa, aob)), amf)) =
    Add (Add (Mul (mc, Neg ack), ao), Add (Mul (ane, Mul (aoa, aob)), amf))
  | numadd (Add (Mul (mc, Neg ack), ao), Sub (amg, amh)) =
    Add (Add (Mul (mc, Neg ack), ao), Sub (amg, amh))
  | numadd (Add (Mul (mc, Neg ack), ao), Mul (ami, amj)) =
    Add (Add (Mul (mc, Neg ack), ao), Mul (ami, amj))
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), C aon) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), C aon)
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Bound aoo) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Bound aoo)
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), CX (aop, aoq)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), CX (aop, aoq))
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Neg aor) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Neg aor)
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Add (C apj, aot)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Add (C apj, aot))
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Add (Bound apk, aot)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Add (Bound apk, aot))
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Add (CX (apl, apm), aot)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Add (CX (apl, apm), aot))
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Add (Neg apn, aot)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Add (Neg apn, aot))
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Add (Add (apo, app), aot)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Add (Add (apo, app), aot))
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Add (Sub (apq, apr), aot)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Add (Sub (apq, apr), aot))
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Add (Mul (aps, C aqf), aot)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Add (Mul (aps, C aqf), aot))
  | numadd
      (Add (Mul (mc, Add (acl, acm)), ao),
        Add (Mul (aps, CX (aqh, aqi)), aot)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao),
          Add (Mul (aps, CX (aqh, aqi)), aot))
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Add (Mul (aps, Neg aqj), aot)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Add (Mul (aps, Neg aqj), aot))
  | numadd
      (Add (Mul (mc, Add (acl, acm)), ao),
        Add (Mul (aps, Add (aqk, aql)), aot)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao),
          Add (Mul (aps, Add (aqk, aql)), aot))
  | numadd
      (Add (Mul (mc, Add (acl, acm)), ao),
        Add (Mul (aps, Sub (aqm, aqn)), aot)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao),
          Add (Mul (aps, Sub (aqm, aqn)), aot))
  | numadd
      (Add (Mul (mc, Add (acl, acm)), ao),
        Add (Mul (aps, Mul (aqo, aqp)), aot)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao),
          Add (Mul (aps, Mul (aqo, aqp)), aot))
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Sub (aou, aov)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Sub (aou, aov))
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Mul (aow, aox)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Mul (aow, aox))
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), C arb) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), C arb)
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Bound arc) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Bound arc)
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), CX (ard, are)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), CX (ard, are))
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Neg arf) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Neg arf)
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Add (C arx, arh)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Add (C arx, arh))
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Add (Bound ary, arh)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Add (Bound ary, arh))
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Add (CX (arz, asa), arh)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Add (CX (arz, asa), arh))
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Add (Neg asb, arh)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Add (Neg asb, arh))
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Add (Add (asc, asd), arh)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Add (Add (asc, asd), arh))
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Add (Sub (ase, asf), arh)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Add (Sub (ase, asf), arh))
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Add (Mul (asg, C ast), arh)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Add (Mul (asg, C ast), arh))
  | numadd
      (Add (Mul (mc, Sub (acn, aco)), ao),
        Add (Mul (asg, CX (asv, asw)), arh)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao),
          Add (Mul (asg, CX (asv, asw)), arh))
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Add (Mul (asg, Neg asx), arh)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Add (Mul (asg, Neg asx), arh))
  | numadd
      (Add (Mul (mc, Sub (acn, aco)), ao),
        Add (Mul (asg, Add (asy, asz)), arh)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao),
          Add (Mul (asg, Add (asy, asz)), arh))
  | numadd
      (Add (Mul (mc, Sub (acn, aco)), ao),
        Add (Mul (asg, Sub (ata, atb)), arh)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao),
          Add (Mul (asg, Sub (ata, atb)), arh))
  | numadd
      (Add (Mul (mc, Sub (acn, aco)), ao),
        Add (Mul (asg, Mul (atc, atd)), arh)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao),
          Add (Mul (asg, Mul (atc, atd)), arh))
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Sub (ari, arj)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Sub (ari, arj))
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Mul (ark, arl)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Mul (ark, arl))
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), C atp) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), C atp)
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Bound atq) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Bound atq)
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), CX (atr, ats)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), CX (atr, ats))
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Neg att) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Neg att)
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Add (C aul, atv)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Add (C aul, atv))
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Add (Bound aum, atv)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Add (Bound aum, atv))
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Add (CX (aun, auo), atv)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Add (CX (aun, auo), atv))
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Add (Neg aup, atv)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Add (Neg aup, atv))
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Add (Add (auq, aur), atv)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Add (Add (auq, aur), atv))
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Add (Sub (aus, aut), atv)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Add (Sub (aus, aut), atv))
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Add (Mul (auu, C avh), atv)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Add (Mul (auu, C avh), atv))
  | numadd
      (Add (Mul (mc, Mul (acp, acq)), ao),
        Add (Mul (auu, CX (avj, avk)), atv)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao),
          Add (Mul (auu, CX (avj, avk)), atv))
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Add (Mul (auu, Neg avl), atv)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Add (Mul (auu, Neg avl), atv))
  | numadd
      (Add (Mul (mc, Mul (acp, acq)), ao),
        Add (Mul (auu, Add (avm, avn)), atv)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao),
          Add (Mul (auu, Add (avm, avn)), atv))
  | numadd
      (Add (Mul (mc, Mul (acp, acq)), ao),
        Add (Mul (auu, Sub (avo, avp)), atv)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao),
          Add (Mul (auu, Sub (avo, avp)), atv))
  | numadd
      (Add (Mul (mc, Mul (acp, acq)), ao),
        Add (Mul (auu, Mul (avq, avr)), atv)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao),
          Add (Mul (auu, Mul (avq, avr)), atv))
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Sub (atw, atx)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Sub (atw, atx))
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Mul (aty, atz)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Mul (aty, atz))
  | numadd (Sub (ap, aq), C awd) = Add (Sub (ap, aq), C awd)
  | numadd (Sub (ap, aq), Bound awe) = Add (Sub (ap, aq), Bound awe)
  | numadd (Sub (ap, aq), CX (awf, awg)) = Add (Sub (ap, aq), CX (awf, awg))
  | numadd (Sub (ap, aq), Neg awh) = Add (Sub (ap, aq), Neg awh)
  | numadd (Sub (ap, aq), Add (C awz, awj)) =
    Add (Sub (ap, aq), Add (C awz, awj))
  | numadd (Sub (ap, aq), Add (Bound axa, awj)) =
    Add (Sub (ap, aq), Add (Bound axa, awj))
  | numadd (Sub (ap, aq), Add (CX (axb, axc), awj)) =
    Add (Sub (ap, aq), Add (CX (axb, axc), awj))
  | numadd (Sub (ap, aq), Add (Neg axd, awj)) =
    Add (Sub (ap, aq), Add (Neg axd, awj))
  | numadd (Sub (ap, aq), Add (Add (axe, axf), awj)) =
    Add (Sub (ap, aq), Add (Add (axe, axf), awj))
  | numadd (Sub (ap, aq), Add (Sub (axg, axh), awj)) =
    Add (Sub (ap, aq), Add (Sub (axg, axh), awj))
  | numadd (Sub (ap, aq), Add (Mul (axi, C axv), awj)) =
    Add (Sub (ap, aq), Add (Mul (axi, C axv), awj))
  | numadd (Sub (ap, aq), Add (Mul (axi, CX (axx, axy)), awj)) =
    Add (Sub (ap, aq), Add (Mul (axi, CX (axx, axy)), awj))
  | numadd (Sub (ap, aq), Add (Mul (axi, Neg axz), awj)) =
    Add (Sub (ap, aq), Add (Mul (axi, Neg axz), awj))
  | numadd (Sub (ap, aq), Add (Mul (axi, Add (aya, ayb)), awj)) =
    Add (Sub (ap, aq), Add (Mul (axi, Add (aya, ayb)), awj))
  | numadd (Sub (ap, aq), Add (Mul (axi, Sub (ayc, ayd)), awj)) =
    Add (Sub (ap, aq), Add (Mul (axi, Sub (ayc, ayd)), awj))
  | numadd (Sub (ap, aq), Add (Mul (axi, Mul (aye, ayf)), awj)) =
    Add (Sub (ap, aq), Add (Mul (axi, Mul (aye, ayf)), awj))
  | numadd (Sub (ap, aq), Sub (awk, awl)) = Add (Sub (ap, aq), Sub (awk, awl))
  | numadd (Sub (ap, aq), Mul (awm, awn)) = Add (Sub (ap, aq), Mul (awm, awn))
  | numadd (Mul (ar, as'), C ayr) = Add (Mul (ar, as'), C ayr)
  | numadd (Mul (ar, as'), Bound ays) = Add (Mul (ar, as'), Bound ays)
  | numadd (Mul (ar, as'), CX (ayt, ayu)) = Add (Mul (ar, as'), CX (ayt, ayu))
  | numadd (Mul (ar, as'), Neg ayv) = Add (Mul (ar, as'), Neg ayv)
  | numadd (Mul (ar, as'), Add (C azn, ayx)) =
    Add (Mul (ar, as'), Add (C azn, ayx))
  | numadd (Mul (ar, as'), Add (Bound azo, ayx)) =
    Add (Mul (ar, as'), Add (Bound azo, ayx))
  | numadd (Mul (ar, as'), Add (CX (azp, azq), ayx)) =
    Add (Mul (ar, as'), Add (CX (azp, azq), ayx))
  | numadd (Mul (ar, as'), Add (Neg azr, ayx)) =
    Add (Mul (ar, as'), Add (Neg azr, ayx))
  | numadd (Mul (ar, as'), Add (Add (azs, azt), ayx)) =
    Add (Mul (ar, as'), Add (Add (azs, azt), ayx))
  | numadd (Mul (ar, as'), Add (Sub (azu, azv), ayx)) =
    Add (Mul (ar, as'), Add (Sub (azu, azv), ayx))
  | numadd (Mul (ar, as'), Add (Mul (azw, C baj), ayx)) =
    Add (Mul (ar, as'), Add (Mul (azw, C baj), ayx))
  | numadd (Mul (ar, as'), Add (Mul (azw, CX (bal, bam)), ayx)) =
    Add (Mul (ar, as'), Add (Mul (azw, CX (bal, bam)), ayx))
  | numadd (Mul (ar, as'), Add (Mul (azw, Neg ban), ayx)) =
    Add (Mul (ar, as'), Add (Mul (azw, Neg ban), ayx))
  | numadd (Mul (ar, as'), Add (Mul (azw, Add (bao, bap)), ayx)) =
    Add (Mul (ar, as'), Add (Mul (azw, Add (bao, bap)), ayx))
  | numadd (Mul (ar, as'), Add (Mul (azw, Sub (baq, bar)), ayx)) =
    Add (Mul (ar, as'), Add (Mul (azw, Sub (baq, bar)), ayx))
  | numadd (Mul (ar, as'), Add (Mul (azw, Mul (bas, bat)), ayx)) =
    Add (Mul (ar, as'), Add (Mul (azw, Mul (bas, bat)), ayx))
  | numadd (Mul (ar, as'), Sub (ayy, ayz)) = Add (Mul (ar, as'), Sub (ayy, ayz))
  | numadd (Mul (ar, as'), Mul (aza, azb)) =
    Add (Mul (ar, as'), Mul (aza, azb));

fun nummul (C j) = (fn i => C (i * j))
  | nummul (Add (a, b)) = (fn i => numadd (nummul a i, nummul b i))
  | nummul (Mul (c, t)) = (fn i => nummul t (i * c))
  | nummul (Bound v) = (fn i => Mul (i, Bound v))
  | nummul (CX (w, x)) = (fn i => Mul (i, CX (w, x)))
  | nummul (Neg y) = (fn i => Mul (i, Neg y))
  | nummul (Sub (ac, ad)) = (fn i => Mul (i, Sub (ac, ad)));

fun numneg t = nummul t (~ 1);

fun numsub s t = (if (s = t) then C 0 else numadd (s, numneg t));

fun simpnum (C j) = C j
  | simpnum (Bound n) = Add (Mul (1, Bound n), C 0)
  | simpnum (Neg t) = numneg (simpnum t)
  | simpnum (Add (t, s)) = numadd (simpnum t, simpnum s)
  | simpnum (Sub (t, s)) = numsub (simpnum t) (simpnum s)
  | simpnum (Mul (i, t)) = (if (i = 0) then C 0 else nummul (simpnum t) i)
  | simpnum (CX (w, x)) = CX (w, x);

datatype fm = T | F | Lt of num | Le of num | Gt of num | Ge of num | Eq of num
  | NEq of num | Dvd of int * num | NDvd of int * num | NOT of fm
  | And of fm * fm | Or of fm * fm | Imp of fm * fm | Iff of fm * fm | E of fm
  | A of fm | Closed of int | NClosed of int;

fun not (NOT p) = p
  | not T = F
  | not F = T
  | not (Lt u) = NOT (Lt u)
  | not (Le v) = NOT (Le v)
  | not (Gt w) = NOT (Gt w)
  | not (Ge x) = NOT (Ge x)
  | not (Eq y) = NOT (Eq y)
  | not (NEq z) = NOT (NEq z)
  | not (Dvd (aa, ab)) = NOT (Dvd (aa, ab))
  | not (NDvd (ac, ad)) = NOT (NDvd (ac, ad))
  | not (And (af, ag)) = NOT (And (af, ag))
  | not (Or (ah, ai)) = NOT (Or (ah, ai))
  | not (Imp (aj, ak)) = NOT (Imp (aj, ak))
  | not (Iff (al, am)) = NOT (Iff (al, am))
  | not (E an) = NOT (E an)
  | not (A ao) = NOT (A ao)
  | not (Closed ap) = NOT (Closed ap)
  | not (NClosed aq) = NOT (NClosed aq);

fun iff p q =
  (if (p = q) then T
    else (if ((p = not q) orelse (not p = q)) then F
           else (if (p = F) then not q
                  else (if (q = F) then not p
                         else (if (p = T) then q
                                else (if (q = T) then p else Iff (p, q)))))));

fun imp p q =
  (if ((p = F) orelse (q = T)) then T
    else (if (p = T) then q else (if (q = F) then not p else Imp (p, q))));

fun disj p q =
  (if ((p = T) orelse (q = T)) then T
    else (if (p = F) then q else (if (q = F) then p else Or (p, q))));

fun conj p q =
  (if ((p = F) orelse (q = F)) then F
    else (if (p = T) then q else (if (q = T) then p else And (p, q))));

fun simpfm (And (p, q)) = conj (simpfm p) (simpfm q)
  | simpfm (Or (p, q)) = disj (simpfm p) (simpfm q)
  | simpfm (Imp (p, q)) = imp (simpfm p) (simpfm q)
  | simpfm (Iff (p, q)) = iff (simpfm p) (simpfm q)
  | simpfm (NOT p) = not (simpfm p)
  | simpfm (Lt a) =
    let val a' = simpnum a
    in (case a' of C x => (if (x < 0) then T else F) | Bound x => Lt a'
         | CX (x, xa) => Lt a' | Neg x => Lt a' | Add (x, xa) => Lt a'
         | Sub (x, xa) => Lt a' | Mul (x, xa) => Lt a')
    end
  | simpfm (Le a) =
    let val a' = simpnum a
    in (case a' of C x => (if (x <= 0) then T else F) | Bound x => Le a'
         | CX (x, xa) => Le a' | Neg x => Le a' | Add (x, xa) => Le a'
         | Sub (x, xa) => Le a' | Mul (x, xa) => Le a')
    end
  | simpfm (Gt a) =
    let val a' = simpnum a
    in (case a' of C x => (if (0 < x) then T else F) | Bound x => Gt a'
         | CX (x, xa) => Gt a' | Neg x => Gt a' | Add (x, xa) => Gt a'
         | Sub (x, xa) => Gt a' | Mul (x, xa) => Gt a')
    end
  | simpfm (Ge a) =
    let val a' = simpnum a
    in (case a' of C x => (if (0 <= x) then T else F) | Bound x => Ge a'
         | CX (x, xa) => Ge a' | Neg x => Ge a' | Add (x, xa) => Ge a'
         | Sub (x, xa) => Ge a' | Mul (x, xa) => Ge a')
    end
  | simpfm (Eq a) =
    let val a' = simpnum a
    in (case a' of C x => (if (x = 0) then T else F) | Bound x => Eq a'
         | CX (x, xa) => Eq a' | Neg x => Eq a' | Add (x, xa) => Eq a'
         | Sub (x, xa) => Eq a' | Mul (x, xa) => Eq a')
    end
  | simpfm (NEq a) =
    let val a' = simpnum a
    in (case a' of C x => (if Bool.not (x = 0) then T else F)
         | Bound x => NEq a' | CX (x, xa) => NEq a' | Neg x => NEq a'
         | Add (x, xa) => NEq a' | Sub (x, xa) => NEq a'
         | Mul (x, xa) => NEq a')
    end
  | simpfm (Dvd (i, a)) =
    (if (i = 0) then simpfm (Eq a)
      else (if (abs i = 1) then T
             else let val a' = simpnum a
                  in (case a' of C x => (if dvd i x then T else F)
                       | Bound x => Dvd (i, a') | CX (x, xa) => Dvd (i, a')
                       | Neg x => Dvd (i, a') | Add (x, xa) => Dvd (i, a')
                       | Sub (x, xa) => Dvd (i, a')
                       | Mul (x, xa) => Dvd (i, a'))
                  end))
  | simpfm (NDvd (i, a)) =
    (if (i = 0) then simpfm (NEq a)
      else (if (abs i = 1) then F
             else let val a' = simpnum a
                  in (case a' of C x => (if Bool.not (dvd i x) then T else F)
                       | Bound x => NDvd (i, a') | CX (x, xa) => NDvd (i, a')
                       | Neg x => NDvd (i, a') | Add (x, xa) => NDvd (i, a')
                       | Sub (x, xa) => NDvd (i, a')
                       | Mul (x, xa) => NDvd (i, a'))
                  end))
  | simpfm T = T
  | simpfm F = F
  | simpfm (E ao) = E ao
  | simpfm (A ap) = A ap
  | simpfm (Closed aq) = Closed aq
  | simpfm (NClosed ar) = NClosed ar;

fun foldr f [] a = a
  | foldr f (x :: xs) a = f x (foldr f xs a);

fun djf f p q =
  (if (q = T) then T
    else (if (q = F) then f p
           else let val fp = f p
                in (case fp of T => T | F => q | Lt x => Or (f p, q)
                     | Le x => Or (f p, q) | Gt x => Or (f p, q)
                     | Ge x => Or (f p, q) | Eq x => Or (f p, q)
                     | NEq x => Or (f p, q) | Dvd (x, xa) => Or (f p, q)
                     | NDvd (x, xa) => Or (f p, q) | NOT x => Or (f p, q)
                     | And (x, xa) => Or (f p, q) | Or (x, xa) => Or (f p, q)
                     | Imp (x, xa) => Or (f p, q) | Iff (x, xa) => Or (f p, q)
                     | E x => Or (f p, q) | A x => Or (f p, q)
                     | Closed x => Or (f p, q) | NClosed x => Or (f p, q))
                end));

fun evaldjf f ps = foldr (djf f) ps F;

fun append [] ys = ys
  | append (x :: xs) ys = (x :: append xs ys);

fun disjuncts (Or (p, q)) = append (disjuncts p) (disjuncts q)
  | disjuncts F = []
  | disjuncts T = [T]
  | disjuncts (Lt u) = [Lt u]
  | disjuncts (Le v) = [Le v]
  | disjuncts (Gt w) = [Gt w]
  | disjuncts (Ge x) = [Ge x]
  | disjuncts (Eq y) = [Eq y]
  | disjuncts (NEq z) = [NEq z]
  | disjuncts (Dvd (aa, ab)) = [Dvd (aa, ab)]
  | disjuncts (NDvd (ac, ad)) = [NDvd (ac, ad)]
  | disjuncts (NOT ae) = [NOT ae]
  | disjuncts (And (af, ag)) = [And (af, ag)]
  | disjuncts (Imp (aj, ak)) = [Imp (aj, ak)]
  | disjuncts (Iff (al, am)) = [Iff (al, am)]
  | disjuncts (E an) = [E an]
  | disjuncts (A ao) = [A ao]
  | disjuncts (Closed ap) = [Closed ap]
  | disjuncts (NClosed aq) = [NClosed aq];

fun DJ f p = evaldjf f (disjuncts p);

fun qelim (E p) = (fn qe => DJ qe (qelim p qe))
  | qelim (A p) = (fn qe => not (qe (qelim (NOT p) qe)))
  | qelim (NOT p) = (fn qe => not (qelim p qe))
  | qelim (And (p, q)) = (fn qe => conj (qelim p qe) (qelim q qe))
  | qelim (Or (p, q)) = (fn qe => disj (qelim p qe) (qelim q qe))
  | qelim (Imp (p, q)) = (fn qe => imp (qelim p qe) (qelim q qe))
  | qelim (Iff (p, q)) = (fn qe => iff (qelim p qe) (qelim q qe))
  | qelim T = (fn y => simpfm T)
  | qelim F = (fn y => simpfm F)
  | qelim (Lt u) = (fn y => simpfm (Lt u))
  | qelim (Le v) = (fn y => simpfm (Le v))
  | qelim (Gt w) = (fn y => simpfm (Gt w))
  | qelim (Ge x) = (fn y => simpfm (Ge x))
  | qelim (Eq y) = (fn ya => simpfm (Eq y))
  | qelim (NEq z) = (fn y => simpfm (NEq z))
  | qelim (Dvd (aa, ab)) = (fn y => simpfm (Dvd (aa, ab)))
  | qelim (NDvd (ac, ad)) = (fn y => simpfm (NDvd (ac, ad)))
  | qelim (Closed ap) = (fn y => simpfm (Closed ap))
  | qelim (NClosed aq) = (fn y => simpfm (NClosed aq));

fun minus_def1 m n = nat (minus_def2 (m) (n));

fun decrnum (Bound n) = Bound (minus_def1 n one_def0)
  | decrnum (Neg a) = Neg (decrnum a)
  | decrnum (Add (a, b)) = Add (decrnum a, decrnum b)
  | decrnum (Sub (a, b)) = Sub (decrnum a, decrnum b)
  | decrnum (Mul (c, a)) = Mul (c, decrnum a)
  | decrnum (C u) = C u
  | decrnum (CX (w, x)) = CX (w, x);

fun decr (Lt a) = Lt (decrnum a)
  | decr (Le a) = Le (decrnum a)
  | decr (Gt a) = Gt (decrnum a)
  | decr (Ge a) = Ge (decrnum a)
  | decr (Eq a) = Eq (decrnum a)
  | decr (NEq a) = NEq (decrnum a)
  | decr (Dvd (i, a)) = Dvd (i, decrnum a)
  | decr (NDvd (i, a)) = NDvd (i, decrnum a)
  | decr (NOT p) = NOT (decr p)
  | decr (And (p, q)) = And (decr p, decr q)
  | decr (Or (p, q)) = Or (decr p, decr q)
  | decr (Imp (p, q)) = Imp (decr p, decr q)
  | decr (Iff (p, q)) = Iff (decr p, decr q)
  | decr T = T
  | decr F = F
  | decr (E ao) = E ao
  | decr (A ap) = A ap
  | decr (Closed aq) = Closed aq
  | decr (NClosed ar) = NClosed ar;

fun map f [] = []
  | map f (x :: xs) = (f x :: map f xs);

fun allpairs f [] ys = []
  | allpairs f (x :: xs) ys = append (map (f x) ys) (allpairs f xs ys);

fun numsubst0 t (C c) = C c
  | numsubst0 t (Bound n) = (if (n = 0) then t else Bound n)
  | numsubst0 t (CX (i, a)) = Add (Mul (i, t), numsubst0 t a)
  | numsubst0 t (Neg a) = Neg (numsubst0 t a)
  | numsubst0 t (Add (a, b)) = Add (numsubst0 t a, numsubst0 t b)
  | numsubst0 t (Sub (a, b)) = Sub (numsubst0 t a, numsubst0 t b)
  | numsubst0 t (Mul (i, a)) = Mul (i, numsubst0 t a);

fun subst0 t T = T
  | subst0 t F = F
  | subst0 t (Lt a) = Lt (numsubst0 t a)
  | subst0 t (Le a) = Le (numsubst0 t a)
  | subst0 t (Gt a) = Gt (numsubst0 t a)
  | subst0 t (Ge a) = Ge (numsubst0 t a)
  | subst0 t (Eq a) = Eq (numsubst0 t a)
  | subst0 t (NEq a) = NEq (numsubst0 t a)
  | subst0 t (Dvd (i, a)) = Dvd (i, numsubst0 t a)
  | subst0 t (NDvd (i, a)) = NDvd (i, numsubst0 t a)
  | subst0 t (NOT p) = NOT (subst0 t p)
  | subst0 t (And (p, q)) = And (subst0 t p, subst0 t q)
  | subst0 t (Or (p, q)) = Or (subst0 t p, subst0 t q)
  | subst0 t (Imp (p, q)) = Imp (subst0 t p, subst0 t q)
  | subst0 t (Iff (p, q)) = Iff (subst0 t p, subst0 t q)
  | subst0 t (Closed P) = Closed P
  | subst0 t (NClosed P) = NClosed P;

fun minusinf (And (p, q)) = And (minusinf p, minusinf q)
  | minusinf (Or (p, q)) = Or (minusinf p, minusinf q)
  | minusinf (Eq (CX (c, e))) = F
  | minusinf (NEq (CX (c, e))) = T
  | minusinf (Lt (CX (c, e))) = T
  | minusinf (Le (CX (c, e))) = T
  | minusinf (Gt (CX (c, e))) = F
  | minusinf (Ge (CX (c, e))) = F
  | minusinf T = T
  | minusinf F = F
  | minusinf (Lt (C bo)) = Lt (C bo)
  | minusinf (Lt (Bound bp)) = Lt (Bound bp)
  | minusinf (Lt (Neg bs)) = Lt (Neg bs)
  | minusinf (Lt (Add (bt, bu))) = Lt (Add (bt, bu))
  | minusinf (Lt (Sub (bv, bw))) = Lt (Sub (bv, bw))
  | minusinf (Lt (Mul (bx, by))) = Lt (Mul (bx, by))
  | minusinf (Le (C ck)) = Le (C ck)
  | minusinf (Le (Bound cl)) = Le (Bound cl)
  | minusinf (Le (Neg co)) = Le (Neg co)
  | minusinf (Le (Add (cp, cq))) = Le (Add (cp, cq))
  | minusinf (Le (Sub (cr, cs))) = Le (Sub (cr, cs))
  | minusinf (Le (Mul (ct, cu))) = Le (Mul (ct, cu))
  | minusinf (Gt (C dg)) = Gt (C dg)
  | minusinf (Gt (Bound dh)) = Gt (Bound dh)
  | minusinf (Gt (Neg dk)) = Gt (Neg dk)
  | minusinf (Gt (Add (dl, dm))) = Gt (Add (dl, dm))
  | minusinf (Gt (Sub (dn, do'))) = Gt (Sub (dn, do'))
  | minusinf (Gt (Mul (dp, dq))) = Gt (Mul (dp, dq))
  | minusinf (Ge (C ec)) = Ge (C ec)
  | minusinf (Ge (Bound ed)) = Ge (Bound ed)
  | minusinf (Ge (Neg eg)) = Ge (Neg eg)
  | minusinf (Ge (Add (eh, ei))) = Ge (Add (eh, ei))
  | minusinf (Ge (Sub (ej, ek))) = Ge (Sub (ej, ek))
  | minusinf (Ge (Mul (el, em))) = Ge (Mul (el, em))
  | minusinf (Eq (C ey)) = Eq (C ey)
  | minusinf (Eq (Bound ez)) = Eq (Bound ez)
  | minusinf (Eq (Neg fc)) = Eq (Neg fc)
  | minusinf (Eq (Add (fd, fe))) = Eq (Add (fd, fe))
  | minusinf (Eq (Sub (ff, fg))) = Eq (Sub (ff, fg))
  | minusinf (Eq (Mul (fh, fi))) = Eq (Mul (fh, fi))
  | minusinf (NEq (C fu)) = NEq (C fu)
  | minusinf (NEq (Bound fv)) = NEq (Bound fv)
  | minusinf (NEq (Neg fy)) = NEq (Neg fy)
  | minusinf (NEq (Add (fz, ga))) = NEq (Add (fz, ga))
  | minusinf (NEq (Sub (gb, gc))) = NEq (Sub (gb, gc))
  | minusinf (NEq (Mul (gd, ge))) = NEq (Mul (gd, ge))
  | minusinf (Dvd (aa, ab)) = Dvd (aa, ab)
  | minusinf (NDvd (ac, ad)) = NDvd (ac, ad)
  | minusinf (NOT ae) = NOT ae
  | minusinf (Imp (aj, ak)) = Imp (aj, ak)
  | minusinf (Iff (al, am)) = Iff (al, am)
  | minusinf (E an) = E an
  | minusinf (A ao) = A ao
  | minusinf (Closed ap) = Closed ap
  | minusinf (NClosed aq) = NClosed aq;

fun iupt (i, j) = (if (j < i) then [] else (i :: iupt ((i + 1), j)));

fun mirror (And (p, q)) = And (mirror p, mirror q)
  | mirror (Or (p, q)) = Or (mirror p, mirror q)
  | mirror (Eq (CX (c, e))) = Eq (CX (c, Neg e))
  | mirror (NEq (CX (c, e))) = NEq (CX (c, Neg e))
  | mirror (Lt (CX (c, e))) = Gt (CX (c, Neg e))
  | mirror (Le (CX (c, e))) = Ge (CX (c, Neg e))
  | mirror (Gt (CX (c, e))) = Lt (CX (c, Neg e))
  | mirror (Ge (CX (c, e))) = Le (CX (c, Neg e))
  | mirror (Dvd (i, CX (c, e))) = Dvd (i, CX (c, Neg e))
  | mirror (NDvd (i, CX (c, e))) = NDvd (i, CX (c, Neg e))
  | mirror T = T
  | mirror F = F
  | mirror (Lt (C bo)) = Lt (C bo)
  | mirror (Lt (Bound bp)) = Lt (Bound bp)
  | mirror (Lt (Neg bs)) = Lt (Neg bs)
  | mirror (Lt (Add (bt, bu))) = Lt (Add (bt, bu))
  | mirror (Lt (Sub (bv, bw))) = Lt (Sub (bv, bw))
  | mirror (Lt (Mul (bx, by))) = Lt (Mul (bx, by))
  | mirror (Le (C ck)) = Le (C ck)
  | mirror (Le (Bound cl)) = Le (Bound cl)
  | mirror (Le (Neg co)) = Le (Neg co)
  | mirror (Le (Add (cp, cq))) = Le (Add (cp, cq))
  | mirror (Le (Sub (cr, cs))) = Le (Sub (cr, cs))
  | mirror (Le (Mul (ct, cu))) = Le (Mul (ct, cu))
  | mirror (Gt (C dg)) = Gt (C dg)
  | mirror (Gt (Bound dh)) = Gt (Bound dh)
  | mirror (Gt (Neg dk)) = Gt (Neg dk)
  | mirror (Gt (Add (dl, dm))) = Gt (Add (dl, dm))
  | mirror (Gt (Sub (dn, do'))) = Gt (Sub (dn, do'))
  | mirror (Gt (Mul (dp, dq))) = Gt (Mul (dp, dq))
  | mirror (Ge (C ec)) = Ge (C ec)
  | mirror (Ge (Bound ed)) = Ge (Bound ed)
  | mirror (Ge (Neg eg)) = Ge (Neg eg)
  | mirror (Ge (Add (eh, ei))) = Ge (Add (eh, ei))
  | mirror (Ge (Sub (ej, ek))) = Ge (Sub (ej, ek))
  | mirror (Ge (Mul (el, em))) = Ge (Mul (el, em))
  | mirror (Eq (C ey)) = Eq (C ey)
  | mirror (Eq (Bound ez)) = Eq (Bound ez)
  | mirror (Eq (Neg fc)) = Eq (Neg fc)
  | mirror (Eq (Add (fd, fe))) = Eq (Add (fd, fe))
  | mirror (Eq (Sub (ff, fg))) = Eq (Sub (ff, fg))
  | mirror (Eq (Mul (fh, fi))) = Eq (Mul (fh, fi))
  | mirror (NEq (C fu)) = NEq (C fu)
  | mirror (NEq (Bound fv)) = NEq (Bound fv)
  | mirror (NEq (Neg fy)) = NEq (Neg fy)
  | mirror (NEq (Add (fz, ga))) = NEq (Add (fz, ga))
  | mirror (NEq (Sub (gb, gc))) = NEq (Sub (gb, gc))
  | mirror (NEq (Mul (gd, ge))) = NEq (Mul (gd, ge))
  | mirror (Dvd (aa, C gq)) = Dvd (aa, C gq)
  | mirror (Dvd (aa, Bound gr)) = Dvd (aa, Bound gr)
  | mirror (Dvd (aa, Neg gu)) = Dvd (aa, Neg gu)
  | mirror (Dvd (aa, Add (gv, gw))) = Dvd (aa, Add (gv, gw))
  | mirror (Dvd (aa, Sub (gx, gy))) = Dvd (aa, Sub (gx, gy))
  | mirror (Dvd (aa, Mul (gz, ha))) = Dvd (aa, Mul (gz, ha))
  | mirror (NDvd (ac, C hm)) = NDvd (ac, C hm)
  | mirror (NDvd (ac, Bound hn)) = NDvd (ac, Bound hn)
  | mirror (NDvd (ac, Neg hq)) = NDvd (ac, Neg hq)
  | mirror (NDvd (ac, Add (hr, hs))) = NDvd (ac, Add (hr, hs))
  | mirror (NDvd (ac, Sub (ht, hu))) = NDvd (ac, Sub (ht, hu))
  | mirror (NDvd (ac, Mul (hv, hw))) = NDvd (ac, Mul (hv, hw))
  | mirror (NOT ae) = NOT ae
  | mirror (Imp (aj, ak)) = Imp (aj, ak)
  | mirror (Iff (al, am)) = Iff (al, am)
  | mirror (E an) = E an
  | mirror (A ao) = A ao
  | mirror (Closed ap) = Closed ap
  | mirror (NClosed aq) = NClosed aq;

fun plus_def0 m n = nat ((m) + (n));

fun size_def9 [] = 0
  | size_def9 (a :: list) = plus_def0 (size_def9 list) (0 + 1);

fun alpha (And (p, q)) = append (alpha p) (alpha q)
  | alpha (Or (p, q)) = append (alpha p) (alpha q)
  | alpha (Eq (CX (c, e))) = [Add (C ~1, e)]
  | alpha (NEq (CX (c, e))) = [e]
  | alpha (Lt (CX (c, e))) = [e]
  | alpha (Le (CX (c, e))) = [Add (C ~1, e)]
  | alpha (Gt (CX (c, e))) = []
  | alpha (Ge (CX (c, e))) = []
  | alpha T = []
  | alpha F = []
  | alpha (Lt (C bo)) = []
  | alpha (Lt (Bound bp)) = []
  | alpha (Lt (Neg bs)) = []
  | alpha (Lt (Add (bt, bu))) = []
  | alpha (Lt (Sub (bv, bw))) = []
  | alpha (Lt (Mul (bx, by))) = []
  | alpha (Le (C ck)) = []
  | alpha (Le (Bound cl)) = []
  | alpha (Le (Neg co)) = []
  | alpha (Le (Add (cp, cq))) = []
  | alpha (Le (Sub (cr, cs))) = []
  | alpha (Le (Mul (ct, cu))) = []
  | alpha (Gt (C dg)) = []
  | alpha (Gt (Bound dh)) = []
  | alpha (Gt (Neg dk)) = []
  | alpha (Gt (Add (dl, dm))) = []
  | alpha (Gt (Sub (dn, do'))) = []
  | alpha (Gt (Mul (dp, dq))) = []
  | alpha (Ge (C ec)) = []
  | alpha (Ge (Bound ed)) = []
  | alpha (Ge (Neg eg)) = []
  | alpha (Ge (Add (eh, ei))) = []
  | alpha (Ge (Sub (ej, ek))) = []
  | alpha (Ge (Mul (el, em))) = []
  | alpha (Eq (C ey)) = []
  | alpha (Eq (Bound ez)) = []
  | alpha (Eq (Neg fc)) = []
  | alpha (Eq (Add (fd, fe))) = []
  | alpha (Eq (Sub (ff, fg))) = []
  | alpha (Eq (Mul (fh, fi))) = []
  | alpha (NEq (C fu)) = []
  | alpha (NEq (Bound fv)) = []
  | alpha (NEq (Neg fy)) = []
  | alpha (NEq (Add (fz, ga))) = []
  | alpha (NEq (Sub (gb, gc))) = []
  | alpha (NEq (Mul (gd, ge))) = []
  | alpha (Dvd (aa, ab)) = []
  | alpha (NDvd (ac, ad)) = []
  | alpha (NOT ae) = []
  | alpha (Imp (aj, ak)) = []
  | alpha (Iff (al, am)) = []
  | alpha (E an) = []
  | alpha (A ao) = []
  | alpha (Closed ap) = []
  | alpha (NClosed aq) = [];

fun memberl x [] = false
  | memberl x (y :: ys) = ((x = y) orelse memberl x ys);

fun remdups [] = []
  | remdups (x :: xs) =
    (if memberl x xs then remdups xs else (x :: remdups xs));

fun beta (And (p, q)) = append (beta p) (beta q)
  | beta (Or (p, q)) = append (beta p) (beta q)
  | beta (Eq (CX (c, e))) = [Sub (C ~1, e)]
  | beta (NEq (CX (c, e))) = [Neg e]
  | beta (Lt (CX (c, e))) = []
  | beta (Le (CX (c, e))) = []
  | beta (Gt (CX (c, e))) = [Neg e]
  | beta (Ge (CX (c, e))) = [Sub (C ~1, e)]
  | beta T = []
  | beta F = []
  | beta (Lt (C bo)) = []
  | beta (Lt (Bound bp)) = []
  | beta (Lt (Neg bs)) = []
  | beta (Lt (Add (bt, bu))) = []
  | beta (Lt (Sub (bv, bw))) = []
  | beta (Lt (Mul (bx, by))) = []
  | beta (Le (C ck)) = []
  | beta (Le (Bound cl)) = []
  | beta (Le (Neg co)) = []
  | beta (Le (Add (cp, cq))) = []
  | beta (Le (Sub (cr, cs))) = []
  | beta (Le (Mul (ct, cu))) = []
  | beta (Gt (C dg)) = []
  | beta (Gt (Bound dh)) = []
  | beta (Gt (Neg dk)) = []
  | beta (Gt (Add (dl, dm))) = []
  | beta (Gt (Sub (dn, do'))) = []
  | beta (Gt (Mul (dp, dq))) = []
  | beta (Ge (C ec)) = []
  | beta (Ge (Bound ed)) = []
  | beta (Ge (Neg eg)) = []
  | beta (Ge (Add (eh, ei))) = []
  | beta (Ge (Sub (ej, ek))) = []
  | beta (Ge (Mul (el, em))) = []
  | beta (Eq (C ey)) = []
  | beta (Eq (Bound ez)) = []
  | beta (Eq (Neg fc)) = []
  | beta (Eq (Add (fd, fe))) = []
  | beta (Eq (Sub (ff, fg))) = []
  | beta (Eq (Mul (fh, fi))) = []
  | beta (NEq (C fu)) = []
  | beta (NEq (Bound fv)) = []
  | beta (NEq (Neg fy)) = []
  | beta (NEq (Add (fz, ga))) = []
  | beta (NEq (Sub (gb, gc))) = []
  | beta (NEq (Mul (gd, ge))) = []
  | beta (Dvd (aa, ab)) = []
  | beta (NDvd (ac, ad)) = []
  | beta (NOT ae) = []
  | beta (Imp (aj, ak)) = []
  | beta (Iff (al, am)) = []
  | beta (E an) = []
  | beta (A ao) = []
  | beta (Closed ap) = []
  | beta (NClosed aq) = [];

fun fst (a, b) = a;

fun div_def1 a b = fst (divAlg (a, b));

fun div_def0 m n = nat (div_def1 (m) (n));

fun mod_def0 m n = nat (mod_def1 (m) (n));

fun gcd (m, n) = (if (n = 0) then m else gcd (n, mod_def0 m n));

fun times_def0 m n = nat ((m) * (n));

fun lcm x = (fn (m, n) => div_def0 (times_def0 m n) (gcd (m, n))) x;

fun ilcm x = (fn j => (lcm (nat (abs x), nat (abs j))));

fun delta (And (p, q)) = ilcm (delta p) (delta q)
  | delta (Or (p, q)) = ilcm (delta p) (delta q)
  | delta (Dvd (i, CX (c, e))) = i
  | delta (NDvd (i, CX (c, e))) = i
  | delta T = 1
  | delta F = 1
  | delta (Lt u) = 1
  | delta (Le v) = 1
  | delta (Gt w) = 1
  | delta (Ge x) = 1
  | delta (Eq y) = 1
  | delta (NEq z) = 1
  | delta (Dvd (aa, C bo)) = 1
  | delta (Dvd (aa, Bound bp)) = 1
  | delta (Dvd (aa, Neg bs)) = 1
  | delta (Dvd (aa, Add (bt, bu))) = 1
  | delta (Dvd (aa, Sub (bv, bw))) = 1
  | delta (Dvd (aa, Mul (bx, by))) = 1
  | delta (NDvd (ac, C ck)) = 1
  | delta (NDvd (ac, Bound cl)) = 1
  | delta (NDvd (ac, Neg co)) = 1
  | delta (NDvd (ac, Add (cp, cq))) = 1
  | delta (NDvd (ac, Sub (cr, cs))) = 1
  | delta (NDvd (ac, Mul (ct, cu))) = 1
  | delta (NOT ae) = 1
  | delta (Imp (aj, ak)) = 1
  | delta (Iff (al, am)) = 1
  | delta (E an) = 1
  | delta (A ao) = 1
  | delta (Closed ap) = 1
  | delta (NClosed aq) = 1;

fun a_beta (And (p, q)) = (fn k => And (a_beta p k, a_beta q k))
  | a_beta (Or (p, q)) = (fn k => Or (a_beta p k, a_beta q k))
  | a_beta (Eq (CX (c, e))) = (fn k => Eq (CX (1, Mul (div_def1 k c, e))))
  | a_beta (NEq (CX (c, e))) = (fn k => NEq (CX (1, Mul (div_def1 k c, e))))
  | a_beta (Lt (CX (c, e))) = (fn k => Lt (CX (1, Mul (div_def1 k c, e))))
  | a_beta (Le (CX (c, e))) = (fn k => Le (CX (1, Mul (div_def1 k c, e))))
  | a_beta (Gt (CX (c, e))) = (fn k => Gt (CX (1, Mul (div_def1 k c, e))))
  | a_beta (Ge (CX (c, e))) = (fn k => Ge (CX (1, Mul (div_def1 k c, e))))
  | a_beta (Dvd (i, CX (c, e))) =
    (fn k => Dvd ((div_def1 k c * i), CX (1, Mul (div_def1 k c, e))))
  | a_beta (NDvd (i, CX (c, e))) =
    (fn k => NDvd ((div_def1 k c * i), CX (1, Mul (div_def1 k c, e))))
  | a_beta T = (fn k => T)
  | a_beta F = (fn k => F)
  | a_beta (Lt (C bo)) = (fn k => Lt (C bo))
  | a_beta (Lt (Bound bp)) = (fn k => Lt (Bound bp))
  | a_beta (Lt (Neg bs)) = (fn k => Lt (Neg bs))
  | a_beta (Lt (Add (bt, bu))) = (fn k => Lt (Add (bt, bu)))
  | a_beta (Lt (Sub (bv, bw))) = (fn k => Lt (Sub (bv, bw)))
  | a_beta (Lt (Mul (bx, by))) = (fn k => Lt (Mul (bx, by)))
  | a_beta (Le (C ck)) = (fn k => Le (C ck))
  | a_beta (Le (Bound cl)) = (fn k => Le (Bound cl))
  | a_beta (Le (Neg co)) = (fn k => Le (Neg co))
  | a_beta (Le (Add (cp, cq))) = (fn k => Le (Add (cp, cq)))
  | a_beta (Le (Sub (cr, cs))) = (fn k => Le (Sub (cr, cs)))
  | a_beta (Le (Mul (ct, cu))) = (fn k => Le (Mul (ct, cu)))
  | a_beta (Gt (C dg)) = (fn k => Gt (C dg))
  | a_beta (Gt (Bound dh)) = (fn k => Gt (Bound dh))
  | a_beta (Gt (Neg dk)) = (fn k => Gt (Neg dk))
  | a_beta (Gt (Add (dl, dm))) = (fn k => Gt (Add (dl, dm)))
  | a_beta (Gt (Sub (dn, do'))) = (fn k => Gt (Sub (dn, do')))
  | a_beta (Gt (Mul (dp, dq))) = (fn k => Gt (Mul (dp, dq)))
  | a_beta (Ge (C ec)) = (fn k => Ge (C ec))
  | a_beta (Ge (Bound ed)) = (fn k => Ge (Bound ed))
  | a_beta (Ge (Neg eg)) = (fn k => Ge (Neg eg))
  | a_beta (Ge (Add (eh, ei))) = (fn k => Ge (Add (eh, ei)))
  | a_beta (Ge (Sub (ej, ek))) = (fn k => Ge (Sub (ej, ek)))
  | a_beta (Ge (Mul (el, em))) = (fn k => Ge (Mul (el, em)))
  | a_beta (Eq (C ey)) = (fn k => Eq (C ey))
  | a_beta (Eq (Bound ez)) = (fn k => Eq (Bound ez))
  | a_beta (Eq (Neg fc)) = (fn k => Eq (Neg fc))
  | a_beta (Eq (Add (fd, fe))) = (fn k => Eq (Add (fd, fe)))
  | a_beta (Eq (Sub (ff, fg))) = (fn k => Eq (Sub (ff, fg)))
  | a_beta (Eq (Mul (fh, fi))) = (fn k => Eq (Mul (fh, fi)))
  | a_beta (NEq (C fu)) = (fn k => NEq (C fu))
  | a_beta (NEq (Bound fv)) = (fn k => NEq (Bound fv))
  | a_beta (NEq (Neg fy)) = (fn k => NEq (Neg fy))
  | a_beta (NEq (Add (fz, ga))) = (fn k => NEq (Add (fz, ga)))
  | a_beta (NEq (Sub (gb, gc))) = (fn k => NEq (Sub (gb, gc)))
  | a_beta (NEq (Mul (gd, ge))) = (fn k => NEq (Mul (gd, ge)))
  | a_beta (Dvd (aa, C gq)) = (fn k => Dvd (aa, C gq))
  | a_beta (Dvd (aa, Bound gr)) = (fn k => Dvd (aa, Bound gr))
  | a_beta (Dvd (aa, Neg gu)) = (fn k => Dvd (aa, Neg gu))
  | a_beta (Dvd (aa, Add (gv, gw))) = (fn k => Dvd (aa, Add (gv, gw)))
  | a_beta (Dvd (aa, Sub (gx, gy))) = (fn k => Dvd (aa, Sub (gx, gy)))
  | a_beta (Dvd (aa, Mul (gz, ha))) = (fn k => Dvd (aa, Mul (gz, ha)))
  | a_beta (NDvd (ac, C hm)) = (fn k => NDvd (ac, C hm))
  | a_beta (NDvd (ac, Bound hn)) = (fn k => NDvd (ac, Bound hn))
  | a_beta (NDvd (ac, Neg hq)) = (fn k => NDvd (ac, Neg hq))
  | a_beta (NDvd (ac, Add (hr, hs))) = (fn k => NDvd (ac, Add (hr, hs)))
  | a_beta (NDvd (ac, Sub (ht, hu))) = (fn k => NDvd (ac, Sub (ht, hu)))
  | a_beta (NDvd (ac, Mul (hv, hw))) = (fn k => NDvd (ac, Mul (hv, hw)))
  | a_beta (NOT ae) = (fn k => NOT ae)
  | a_beta (Imp (aj, ak)) = (fn k => Imp (aj, ak))
  | a_beta (Iff (al, am)) = (fn k => Iff (al, am))
  | a_beta (E an) = (fn k => E an)
  | a_beta (A ao) = (fn k => A ao)
  | a_beta (Closed ap) = (fn k => Closed ap)
  | a_beta (NClosed aq) = (fn k => NClosed aq);

fun zeta (And (p, q)) = ilcm (zeta p) (zeta q)
  | zeta (Or (p, q)) = ilcm (zeta p) (zeta q)
  | zeta (Eq (CX (c, e))) = c
  | zeta (NEq (CX (c, e))) = c
  | zeta (Lt (CX (c, e))) = c
  | zeta (Le (CX (c, e))) = c
  | zeta (Gt (CX (c, e))) = c
  | zeta (Ge (CX (c, e))) = c
  | zeta (Dvd (i, CX (c, e))) = c
  | zeta (NDvd (i, CX (c, e))) = c
  | zeta T = 1
  | zeta F = 1
  | zeta (Lt (C bo)) = 1
  | zeta (Lt (Bound bp)) = 1
  | zeta (Lt (Neg bs)) = 1
  | zeta (Lt (Add (bt, bu))) = 1
  | zeta (Lt (Sub (bv, bw))) = 1
  | zeta (Lt (Mul (bx, by))) = 1
  | zeta (Le (C ck)) = 1
  | zeta (Le (Bound cl)) = 1
  | zeta (Le (Neg co)) = 1
  | zeta (Le (Add (cp, cq))) = 1
  | zeta (Le (Sub (cr, cs))) = 1
  | zeta (Le (Mul (ct, cu))) = 1
  | zeta (Gt (C dg)) = 1
  | zeta (Gt (Bound dh)) = 1
  | zeta (Gt (Neg dk)) = 1
  | zeta (Gt (Add (dl, dm))) = 1
  | zeta (Gt (Sub (dn, do'))) = 1
  | zeta (Gt (Mul (dp, dq))) = 1
  | zeta (Ge (C ec)) = 1
  | zeta (Ge (Bound ed)) = 1
  | zeta (Ge (Neg eg)) = 1
  | zeta (Ge (Add (eh, ei))) = 1
  | zeta (Ge (Sub (ej, ek))) = 1
  | zeta (Ge (Mul (el, em))) = 1
  | zeta (Eq (C ey)) = 1
  | zeta (Eq (Bound ez)) = 1
  | zeta (Eq (Neg fc)) = 1
  | zeta (Eq (Add (fd, fe))) = 1
  | zeta (Eq (Sub (ff, fg))) = 1
  | zeta (Eq (Mul (fh, fi))) = 1
  | zeta (NEq (C fu)) = 1
  | zeta (NEq (Bound fv)) = 1
  | zeta (NEq (Neg fy)) = 1
  | zeta (NEq (Add (fz, ga))) = 1
  | zeta (NEq (Sub (gb, gc))) = 1
  | zeta (NEq (Mul (gd, ge))) = 1
  | zeta (Dvd (aa, C gq)) = 1
  | zeta (Dvd (aa, Bound gr)) = 1
  | zeta (Dvd (aa, Neg gu)) = 1
  | zeta (Dvd (aa, Add (gv, gw))) = 1
  | zeta (Dvd (aa, Sub (gx, gy))) = 1
  | zeta (Dvd (aa, Mul (gz, ha))) = 1
  | zeta (NDvd (ac, C hm)) = 1
  | zeta (NDvd (ac, Bound hn)) = 1
  | zeta (NDvd (ac, Neg hq)) = 1
  | zeta (NDvd (ac, Add (hr, hs))) = 1
  | zeta (NDvd (ac, Sub (ht, hu))) = 1
  | zeta (NDvd (ac, Mul (hv, hw))) = 1
  | zeta (NOT ae) = 1
  | zeta (Imp (aj, ak)) = 1
  | zeta (Iff (al, am)) = 1
  | zeta (E an) = 1
  | zeta (A ao) = 1
  | zeta (Closed ap) = 1
  | zeta (NClosed aq) = 1;

fun split x = (fn p => x (fst p) (snd p));

fun zsplit0 (C c) = (0, C c)
  | zsplit0 (Bound n) = (if (n = 0) then (1, C 0) else (0, Bound n))
  | zsplit0 (CX (i, a)) = split (fn i' => (fn x => ((i + i'), x))) (zsplit0 a)
  | zsplit0 (Neg a) = (fn (i', a') => (~ i', Neg a')) (zsplit0 a)
  | zsplit0 (Add (a, b)) =
    (fn (ia, a') => (fn (ib, b') => ((ia + ib), Add (a', b'))) (zsplit0 b))
      (zsplit0 a)
  | zsplit0 (Sub (a, b)) =
    (fn (ia, a') =>
      (fn (ib, b') => (minus_def2 ia ib, Sub (a', b'))) (zsplit0 b))
      (zsplit0 a)
  | zsplit0 (Mul (i, a)) = (fn (i', a') => ((i * i'), Mul (i, a'))) (zsplit0 a);

fun zlfm (And (p, q)) = And (zlfm p, zlfm q)
  | zlfm (Or (p, q)) = Or (zlfm p, zlfm q)
  | zlfm (Imp (p, q)) = Or (zlfm (NOT p), zlfm q)
  | zlfm (Iff (p, q)) =
    Or (And (zlfm p, zlfm q), And (zlfm (NOT p), zlfm (NOT q)))
  | zlfm (Lt a) =
    let val x = zsplit0 a
    in (fn (c, r) =>
         (if (c = 0) then Lt r
           else (if (0 < c) then Lt (CX (c, r)) else Gt (CX (~ c, Neg r)))))
         x
    end
  | zlfm (Le a) =
    let val x = zsplit0 a
    in (fn (c, r) =>
         (if (c = 0) then Le r
           else (if (0 < c) then Le (CX (c, r)) else Ge (CX (~ c, Neg r)))))
         x
    end
  | zlfm (Gt a) =
    let val x = zsplit0 a
    in (fn (c, r) =>
         (if (c = 0) then Gt r
           else (if (0 < c) then Gt (CX (c, r)) else Lt (CX (~ c, Neg r)))))
         x
    end
  | zlfm (Ge a) =
    let val x = zsplit0 a
    in (fn (c, r) =>
         (if (c = 0) then Ge r
           else (if (0 < c) then Ge (CX (c, r)) else Le (CX (~ c, Neg r)))))
         x
    end
  | zlfm (Eq a) =
    let val x = zsplit0 a
    in (fn (c, r) =>
         (if (c = 0) then Eq r
           else (if (0 < c) then Eq (CX (c, r)) else Eq (CX (~ c, Neg r)))))
         x
    end
  | zlfm (NEq a) =
    let val x = zsplit0 a
    in (fn (c, r) =>
         (if (c = 0) then NEq r
           else (if (0 < c) then NEq (CX (c, r)) else NEq (CX (~ c, Neg r)))))
         x
    end
  | zlfm (Dvd (i, a)) =
    (if (i = 0) then zlfm (Eq a)
      else let val x = zsplit0 a
           in (fn (c, r) =>
                (if (c = 0) then Dvd (abs i, r)
                  else (if (0 < c) then Dvd (abs i, CX (c, r))
                         else Dvd (abs i, CX (~ c, Neg r)))))
                x
           end)
  | zlfm (NDvd (i, a)) =
    (if (i = 0) then zlfm (NEq a)
      else let val x = zsplit0 a
           in (fn (c, r) =>
                (if (c = 0) then NDvd (abs i, r)
                  else (if (0 < c) then NDvd (abs i, CX (c, r))
                         else NDvd (abs i, CX (~ c, Neg r)))))
                x
           end)
  | zlfm (NOT (And (p, q))) = Or (zlfm (NOT p), zlfm (NOT q))
  | zlfm (NOT (Or (p, q))) = And (zlfm (NOT p), zlfm (NOT q))
  | zlfm (NOT (Imp (p, q))) = And (zlfm p, zlfm (NOT q))
  | zlfm (NOT (Iff (p, q))) =
    Or (And (zlfm p, zlfm (NOT q)), And (zlfm (NOT p), zlfm q))
  | zlfm (NOT (NOT p)) = zlfm p
  | zlfm (NOT T) = F
  | zlfm (NOT F) = T
  | zlfm (NOT (Lt a)) = zlfm (Ge a)
  | zlfm (NOT (Le a)) = zlfm (Gt a)
  | zlfm (NOT (Gt a)) = zlfm (Le a)
  | zlfm (NOT (Ge a)) = zlfm (Lt a)
  | zlfm (NOT (Eq a)) = zlfm (NEq a)
  | zlfm (NOT (NEq a)) = zlfm (Eq a)
  | zlfm (NOT (Dvd (i, a))) = zlfm (NDvd (i, a))
  | zlfm (NOT (NDvd (i, a))) = zlfm (Dvd (i, a))
  | zlfm (NOT (Closed P)) = NClosed P
  | zlfm (NOT (NClosed P)) = Closed P
  | zlfm T = T
  | zlfm F = F
  | zlfm (NOT (E ci)) = NOT (E ci)
  | zlfm (NOT (A cj)) = NOT (A cj)
  | zlfm (E ao) = E ao
  | zlfm (A ap) = A ap
  | zlfm (Closed aq) = Closed aq
  | zlfm (NClosed ar) = NClosed ar;

fun unit p =
  let val p' = zlfm p; val l = zeta p';
      val q = And (Dvd (l, CX (1, C 0)), a_beta p' l); val d = delta q;
      val B = remdups (map simpnum (beta q));
      val a = remdups (map simpnum (alpha q))
  in (if less_eq_def3 (size_def9 B) (size_def9 a) then (q, (B, d))
       else (mirror q, (a, d)))
  end;

fun cooper p =
  let val (q, (B, d)) = unit p; val js = iupt (1, d);
      val mq = simpfm (minusinf q);
      val md = evaldjf (fn j => simpfm (subst0 (C j) mq)) js
  in (if (md = T) then T
       else let val qd =
                  evaldjf (fn (b, j) => simpfm (subst0 (Add (b, C j)) q))
                    (allpairs (fn x => fn xa => (x, xa)) B js)
            in decr (disj md qd) end)
  end;

fun prep (E T) = T
  | prep (E F) = F
  | prep (E (Or (p, q))) = Or (prep (E p), prep (E q))
  | prep (E (Imp (p, q))) = Or (prep (E (NOT p)), prep (E q))
  | prep (E (Iff (p, q))) =
    Or (prep (E (And (p, q))), prep (E (And (NOT p, NOT q))))
  | prep (E (NOT (And (p, q)))) = Or (prep (E (NOT p)), prep (E (NOT q)))
  | prep (E (NOT (Imp (p, q)))) = prep (E (And (p, NOT q)))
  | prep (E (NOT (Iff (p, q)))) =
    Or (prep (E (And (p, NOT q))), prep (E (And (NOT p, q))))
  | prep (E (Lt ef)) = E (prep (Lt ef))
  | prep (E (Le eg)) = E (prep (Le eg))
  | prep (E (Gt eh)) = E (prep (Gt eh))
  | prep (E (Ge ei)) = E (prep (Ge ei))
  | prep (E (Eq ej)) = E (prep (Eq ej))
  | prep (E (NEq ek)) = E (prep (NEq ek))
  | prep (E (Dvd (el, em))) = E (prep (Dvd (el, em)))
  | prep (E (NDvd (en, eo))) = E (prep (NDvd (en, eo)))
  | prep (E (NOT T)) = E (prep (NOT T))
  | prep (E (NOT F)) = E (prep (NOT F))
  | prep (E (NOT (Lt gw))) = E (prep (NOT (Lt gw)))
  | prep (E (NOT (Le gx))) = E (prep (NOT (Le gx)))
  | prep (E (NOT (Gt gy))) = E (prep (NOT (Gt gy)))
  | prep (E (NOT (Ge gz))) = E (prep (NOT (Ge gz)))
  | prep (E (NOT (Eq ha))) = E (prep (NOT (Eq ha)))
  | prep (E (NOT (NEq hb))) = E (prep (NOT (NEq hb)))
  | prep (E (NOT (Dvd (hc, hd)))) = E (prep (NOT (Dvd (hc, hd))))
  | prep (E (NOT (NDvd (he, hf)))) = E (prep (NOT (NDvd (he, hf))))
  | prep (E (NOT (NOT hg))) = E (prep (NOT (NOT hg)))
  | prep (E (NOT (Or (hj, hk)))) = E (prep (NOT (Or (hj, hk))))
  | prep (E (NOT (E hp))) = E (prep (NOT (E hp)))
  | prep (E (NOT (A hq))) = E (prep (NOT (A hq)))
  | prep (E (NOT (Closed hr))) = E (prep (NOT (Closed hr)))
  | prep (E (NOT (NClosed hs))) = E (prep (NOT (NClosed hs)))
  | prep (E (And (eq, er))) = E (prep (And (eq, er)))
  | prep (E (E ey)) = E (prep (E ey))
  | prep (E (A ez)) = E (prep (A ez))
  | prep (E (Closed fa)) = E (prep (Closed fa))
  | prep (E (NClosed fb)) = E (prep (NClosed fb))
  | prep (A (And (p, q))) = And (prep (A p), prep (A q))
  | prep (A T) = prep (NOT (E (NOT T)))
  | prep (A F) = prep (NOT (E (NOT F)))
  | prep (A (Lt jn)) = prep (NOT (E (NOT (Lt jn))))
  | prep (A (Le jo)) = prep (NOT (E (NOT (Le jo))))
  | prep (A (Gt jp)) = prep (NOT (E (NOT (Gt jp))))
  | prep (A (Ge jq)) = prep (NOT (E (NOT (Ge jq))))
  | prep (A (Eq jr)) = prep (NOT (E (NOT (Eq jr))))
  | prep (A (NEq js)) = prep (NOT (E (NOT (NEq js))))
  | prep (A (Dvd (jt, ju))) = prep (NOT (E (NOT (Dvd (jt, ju)))))
  | prep (A (NDvd (jv, jw))) = prep (NOT (E (NOT (NDvd (jv, jw)))))
  | prep (A (NOT jx)) = prep (NOT (E (NOT (NOT jx))))
  | prep (A (Or (ka, kb))) = prep (NOT (E (NOT (Or (ka, kb)))))
  | prep (A (Imp (kc, kd))) = prep (NOT (E (NOT (Imp (kc, kd)))))
  | prep (A (Iff (ke, kf))) = prep (NOT (E (NOT (Iff (ke, kf)))))
  | prep (A (E kg)) = prep (NOT (E (NOT (E kg))))
  | prep (A (A kh)) = prep (NOT (E (NOT (A kh))))
  | prep (A (Closed ki)) = prep (NOT (E (NOT (Closed ki))))
  | prep (A (NClosed kj)) = prep (NOT (E (NOT (NClosed kj))))
  | prep (NOT (NOT p)) = prep p
  | prep (NOT (And (p, q))) = Or (prep (NOT p), prep (NOT q))
  | prep (NOT (A p)) = prep (E (NOT p))
  | prep (NOT (Or (p, q))) = And (prep (NOT p), prep (NOT q))
  | prep (NOT (Imp (p, q))) = And (prep p, prep (NOT q))
  | prep (NOT (Iff (p, q))) = Or (prep (And (p, NOT q)), prep (And (NOT p, q)))
  | prep (NOT T) = NOT (prep T)
  | prep (NOT F) = NOT (prep F)
  | prep (NOT (Lt bo)) = NOT (prep (Lt bo))
  | prep (NOT (Le bp)) = NOT (prep (Le bp))
  | prep (NOT (Gt bq)) = NOT (prep (Gt bq))
  | prep (NOT (Ge br)) = NOT (prep (Ge br))
  | prep (NOT (Eq bs)) = NOT (prep (Eq bs))
  | prep (NOT (NEq bt)) = NOT (prep (NEq bt))
  | prep (NOT (Dvd (bu, bv))) = NOT (prep (Dvd (bu, bv)))
  | prep (NOT (NDvd (bw, bx))) = NOT (prep (NDvd (bw, bx)))
  | prep (NOT (E ch)) = NOT (prep (E ch))
  | prep (NOT (Closed cj)) = NOT (prep (Closed cj))
  | prep (NOT (NClosed ck)) = NOT (prep (NClosed ck))
  | prep (Or (p, q)) = Or (prep p, prep q)
  | prep (And (p, q)) = And (prep p, prep q)
  | prep (Imp (p, q)) = prep (Or (NOT p, q))
  | prep (Iff (p, q)) = Or (prep (And (p, q)), prep (And (NOT p, NOT q)))
  | prep T = T
  | prep F = F
  | prep (Lt u) = Lt u
  | prep (Le v) = Le v
  | prep (Gt w) = Gt w
  | prep (Ge x) = Ge x
  | prep (Eq y) = Eq y
  | prep (NEq z) = NEq z
  | prep (Dvd (aa, ab)) = Dvd (aa, ab)
  | prep (NDvd (ac, ad)) = NDvd (ac, ad)
  | prep (Closed ap) = Closed ap
  | prep (NClosed aq) = NClosed aq;

fun pa x = qelim (prep x) cooper;

val pa = (fn x => pa x);

val test =
  (fn x =>
    pa (E (A (Imp (Ge (Sub (Bound 0, Bound one_def0)),
                    E (E (Eq (Sub (Add (Mul (3, Bound one_def0),
 Mul (5, Bound 0)),
                                    Bound (nat 2))))))))));

end;

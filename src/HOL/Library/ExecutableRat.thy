ML {*

fun strip_abs_split 0 t = ([], t)
  | strip_abs_split i (Abs (s, T, t)) =
      let
        val s' = Codegen.new_name t s;
        val v = Free (s', T)
      in apfst (cons v) (strip_abs_split (i-1) (subst_bound (v, t))) end
  | strip_abs_split i (u as Const ("split", _) $ t) = (case strip_abs_split (i+1) t of
        (v :: v' :: vs, u) => (HOLogic.mk_prod (v, v') :: vs, u)
      | _ => ([], u))
  | strip_abs_split i t = ([], t);

fun let_codegen thy defs gr dep thyname brack t = (case strip_comb t of
    (t1 as Const ("Let", _), t2 :: t3 :: ts) =>
    let
      fun dest_let (l as Const ("Let", _) $ t $ u) =
          (case strip_abs_split 1 u of
             ([p], u') => apfst (cons (p, t)) (dest_let u')
           | _ => ([], l))
        | dest_let t = ([], t);
      fun mk_code (gr, (l, r)) =
        let
          val (gr1, pl) = Codegen.invoke_codegen thy defs dep thyname false (gr, l);
          val (gr2, pr) = Codegen.invoke_codegen thy defs dep thyname false (gr1, r);
        in (gr2, (pl, pr)) end
    in case dest_let (t1 $ t2 $ t3) of
        ([], _) => NONE
      | (ps, u) =>
          let
            val (gr1, qs) = foldl_map mk_code (gr, ps);
            val (gr2, pu) = Codegen.invoke_codegen thy defs dep thyname false (gr1, u);
            val (gr3, pargs) = foldl_map
              (Codegen.invoke_codegen thy defs dep thyname true) (gr2, ts)
          in
            SOME (gr3, Codegen.mk_app brack
              (Pretty.blk (0, [Pretty.str "let ", Pretty.blk (0, List.concat
                  (separate [Pretty.str ";", Pretty.brk 1] (map (fn (pl, pr) =>
                    [Pretty.block [Pretty.str "val ", pl, Pretty.str " =",
                       Pretty.brk 1, pr]]) qs))),
                Pretty.brk 1, Pretty.str "in ", pu,
                Pretty.brk 1, Pretty.str "end"])) pargs)
          end
    end
  | _ => NONE);

fun split_codegen thy defs gr dep thyname brack t = (case strip_comb t of
    (t1 as Const ("split", _), t2 :: ts) =>
      (case strip_abs_split 1 (t1 $ t2) of
         ([p], u) =>
           let
             val (gr1, q) = Codegen.invoke_codegen thy defs dep thyname false (gr, p);
             val (gr2, pu) = Codegen.invoke_codegen thy defs dep thyname false (gr1, u);
             val (gr3, pargs) = foldl_map
               (Codegen.invoke_codegen thy defs dep thyname true) (gr2, ts)
           in
             SOME (gr2, Codegen.mk_app brack
               (Pretty.block [Pretty.str "(fn ", q, Pretty.str " =>",
                 Pretty.brk 1, pu, Pretty.str ")"]) pargs)
           end
       | _ => NONE)
  | _ => NONE);

val prod_codegen_setup =
  Codegen.add_codegen "let_codegen" let_codegen #>
  Codegen.add_codegen "split_codegen" split_codegen #>
  CodegenPackage.add_appconst
    ("Let", ((2, 2), CodegenPackage.appgen_let strip_abs_split)) #>
  CodegenPackage.add_appconst
    ("split", ((1, 1), CodegenPackage.appgen_split strip_abs_split));

*}

(*  Title:      HOL/Library/ExecutableRat.thy
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Executable implementation of rational numbers in HOL *}

theory ExecutableRat
imports "~~/src/HOL/Real/Rational" "~~/src/HOL/NumberTheory/IntPrimes"
begin

text {*
  Actually nothing is proved about the implementation.
*}

datatype erat = Rat bool int int

instance erat :: zero by intro_classes
instance erat :: one by intro_classes
instance erat :: plus by intro_classes
instance erat :: minus by intro_classes
instance erat :: times by intro_classes
instance erat :: inverse by intro_classes
instance erat :: ord by intro_classes

consts
  norm :: "erat \<Rightarrow> erat"
  common :: "(int * int) * (int * int) \<Rightarrow> (int * int) * int"
  of_quotient :: "int * int \<Rightarrow> erat"
  of_rat :: "rat \<Rightarrow> erat"
  to_rat :: "erat \<Rightarrow> rat"

defs
  norm_def [simp]: "norm r == case r of (Rat a p q) \<Rightarrow>
     if p = 0 then Rat True 0 1
     else
       let
         absp = abs p
       in let
         m = zgcd (absp, q)
       in Rat (a = (0 <= p)) (absp div m) (q div m)"
  common_def [simp]: "common r == case r of ((p1, q1), (p2, q2)) \<Rightarrow>
       let q' = q1 * q2 div int (gcd (nat q1, nat q2))
       in ((p1 * (q' div q1), p2 * (q' div q2)), q')"
  of_quotient_def [simp]: "of_quotient r == case r of (a, b) \<Rightarrow>
       norm (Rat True a b)"
  of_rat_def [simp]: "of_rat r == of_quotient (THE s. s : Rep_Rat r)"
  to_rat_def [simp]: "to_rat r == case r of (Rat a p q) \<Rightarrow>
       if a then Fract p q else Fract (uminus p) q"

consts
  zero :: erat
  one :: erat
  add :: "erat \<Rightarrow> erat \<Rightarrow> erat"
  neg :: "erat \<Rightarrow> erat"
  mult :: "erat \<Rightarrow> erat \<Rightarrow> erat"
  inv :: "erat \<Rightarrow> erat"
  le :: "erat \<Rightarrow> erat \<Rightarrow> bool"

defs (overloaded)
  zero_rat_def [simp]: "0 == Rat False 0 1"
  one_rat_def [simp]: "1 == Rat False 1 1"
  add_rat_def [simp]: "r + s == case r of Rat a1 p1 q1 \<Rightarrow> case s of Rat a2 p2 q2 \<Rightarrow>
        let
          ((r1, r2), den) = common ((p1, q1), (p2, q2))
        in let
          num = (if a1 then r1 else -r1) + (if a2 then r2 else -r2)
        in norm (Rat True num den)"
  uminus_rat_def [simp]: "- r == case r of Rat a p q \<Rightarrow>
        if p = 0 then Rat a p q
        else Rat (\<not> a) p q"
  times_rat_def [simp]: "r * s == case r of Rat a1 p1 q1 \<Rightarrow> case s of Rat a2 p2 q2 \<Rightarrow>
        norm (Rat (a1 = a2) (p1 * p2) (q1 * q2))"
  inverse_rat_def [simp]: "inverse r == case r of Rat a p q \<Rightarrow>
        if p = 0 then arbitrary
        else Rat a q p"
  le_rat_def [simp]: "r <= s == case r of Rat a1 p1 q1 \<Rightarrow> case s of Rat a2 p2 q2 \<Rightarrow>
        (\<not> a1 \<and> a2) \<or>
        (\<not> (a1 \<and> \<not> a2) \<and>
          (let
            ((r1, r2), dummy) = common ((p1, q1), (p2, q2))
          in if a1 then r1 <= r2 else r2 <= r1))"

code_syntax_tyco rat
  ml (target_atom "{*erat*}")
  haskell (target_atom "{*erat*}")

code_alias
  (* an intermediate solution until name resolving of ad-hoc overloaded
     constants is refined *)
  "HOL.inverse" "Rational.inverse"
  "HOL.divide" "Rational.divide"

code_syntax_const
  Fract
    ml ("{*of_quotient*}")
    haskell ("{*of_quotient*}")
  0 :: "rat"
    ml ("{*0::erat*}")
    haskell ("{*1::erat*}")
  1 :: "rat"
    ml ("{*1::erat*}")
    haskell ("{*1::erat*}")
  "op +" :: "rat \<Rightarrow> rat \<Rightarrow> rat"
    ml ("{*op + :: erat \<Rightarrow> erat \<Rightarrow> erat*}")
    haskell ("{*op + :: erat \<Rightarrow> erat \<Rightarrow> erat*}")
  uminus :: "rat \<Rightarrow> rat"
    ml ("{*uminus :: erat \<Rightarrow> erat*}")
    haskell ("{*uminus :: erat \<Rightarrow> erat*}")
  "op *" :: "rat \<Rightarrow> rat \<Rightarrow> rat"
    ml ("{*op * :: erat \<Rightarrow> erat \<Rightarrow> erat*}")
    haskell ("{*op * :: erat \<Rightarrow> erat \<Rightarrow> erat*}")
  inverse :: "rat \<Rightarrow> rat"
    ml ("{*inverse :: erat \<Rightarrow> erat*}")
    haskell ("{*inverse :: erat \<Rightarrow> erat*}")
  divide :: "rat \<Rightarrow> rat \<Rightarrow> rat"
    ml ("{*op * :: erat \<Rightarrow> erat \<Rightarrow> erat*}/ _/ ({*inverse :: erat \<Rightarrow> erat*}/ _)")
    haskell ("{*op * :: erat \<Rightarrow> erat \<Rightarrow> erat*}/ _/ ({*inverse :: erat \<Rightarrow> erat*}/ _)")
  "op <=" :: "rat \<Rightarrow> rat \<Rightarrow> bool"
    ml ("{*op <= :: erat \<Rightarrow> erat \<Rightarrow> bool*}")
    haskell ("{*op <= :: erat \<Rightarrow> erat \<Rightarrow> bool*}")

end


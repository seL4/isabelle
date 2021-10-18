signature EXP_LOG_EXPRESSION = sig

exception DUP

datatype expr = 
    ConstExpr of term
  | X
  | Uminus of expr
  | Add of expr * expr
  | Minus of expr * expr
  | Inverse of expr
  | Mult of expr * expr
  | Div of expr * expr
  | Ln of expr
  | Exp of expr
  | Power of expr * term
  | LnPowr of expr * expr
  | ExpLn of expr
  | Powr of expr * expr
  | Powr_Nat of expr * expr
  | Powr' of expr * term
  | Root of expr * term
  | Absolute of expr
  | Sgn of expr
  | Min of expr * expr
  | Max of expr * expr
  | Floor of expr
  | Ceiling of expr
  | Frac of expr
  | NatMod of expr * expr
  | Sin of expr
  | Cos of expr
  | ArcTan of expr
  | Custom of string * term * expr list

val preproc_term_conv : Proof.context -> conv
val expr_to_term : expr -> term
val reify : Proof.context -> term -> expr * thm
val reify_simple : Proof.context -> term -> expr * thm

type custom_handler = 
  Lazy_Eval.eval_ctxt -> term -> thm list * Asymptotic_Basis.basis -> thm * Asymptotic_Basis.basis

val register_custom : 
  binding -> term -> custom_handler -> local_theory -> local_theory
val register_custom_from_thm : 
  binding -> thm -> custom_handler -> local_theory -> local_theory
val expand_custom : Proof.context -> string -> custom_handler option

val to_mathematica : expr -> string
val to_maple : expr -> string
val to_maxima : expr -> string
val to_sympy : expr -> string
val to_sage : expr -> string

val reify_mathematica : Proof.context -> term -> string
val reify_maple : Proof.context -> term -> string
val reify_maxima : Proof.context -> term -> string
val reify_sympy : Proof.context -> term -> string
val reify_sage : Proof.context -> term -> string

val limit_mathematica : string -> string
val limit_maple : string -> string
val limit_maxima : string -> string
val limit_sympy : string -> string
val limit_sage : string -> string

end

structure Exp_Log_Expression : EXP_LOG_EXPRESSION = struct


datatype expr = 
    ConstExpr of term
  | X 
  | Uminus of expr
  | Add of expr * expr
  | Minus of expr * expr
  | Inverse of expr
  | Mult of expr * expr
  | Div of expr * expr
  | Ln of expr
  | Exp of expr
  | Power of expr * term
  | LnPowr of expr * expr
  | ExpLn of expr
  | Powr of expr * expr
  | Powr_Nat of expr * expr
  | Powr' of expr * term
  | Root of expr * term
  | Absolute of expr
  | Sgn of expr
  | Min of expr * expr
  | Max of expr * expr
  | Floor of expr
  | Ceiling of expr
  | Frac of expr
  | NatMod of expr * expr
  | Sin of expr
  | Cos of expr
  | ArcTan of expr
  | Custom of string * term * expr list

type custom_handler = 
  Lazy_Eval.eval_ctxt -> term -> thm list * Asymptotic_Basis.basis -> thm * Asymptotic_Basis.basis

type entry = {
  name : string, 
  pat : term,
  net_pat : term,
  expand : custom_handler
}

type entry' = {
  pat : term,
  net_pat : term,
  expand : custom_handler
}

exception DUP

structure Custom_Funs = Generic_Data
(
  type T = {
    name_table : entry' Name_Space.table,
    net : entry Item_Net.T
  }
  fun eq_entry ({name = name1, ...}, {name = name2, ...}) = (name1 = name2)
  val empty = 
    {
      name_table = Name_Space.empty_table "exp_log_custom_function",
      net = Item_Net.init eq_entry (fn {net_pat, ...} => [net_pat])
    }
  
  fun merge ({name_table = tbl1, net = net1}, {name_table = tbl2, net = net2}) = 
    {name_table = Name_Space.join_tables (fn _ => raise DUP) (tbl1, tbl2),
     net = Item_Net.merge (net1, net2)}
  val extend = I
)

fun rewrite' ctxt old_prems bounds thms ct =
  let
    val thy = Proof_Context.theory_of ctxt
    fun apply_rule t thm =
      let
        val lhs = thm |> Thm.concl_of |> Logic.dest_equals |> fst
        val _ = Pattern.first_order_match thy (lhs, t) (Vartab.empty, Vartab.empty)
        val insts = (lhs, t) |> apply2 (Thm.cterm_of ctxt) |> Thm.first_order_match
        val thm = Thm.instantiate insts thm
        val prems = Thm.prems_of thm
        val frees = fold Term.add_frees prems []
      in
        if exists (member op = bounds o fst) frees then
          NONE
        else
          let
            val thm' = thm OF (map (Thm.assume o Thm.cterm_of ctxt) prems)
            val prems' = fold (insert op aconv) prems old_prems
            val crhs = thm |> Thm.concl_of |> Logic.dest_equals |> snd |> Thm.cterm_of ctxt
          in                          
            SOME (thm', crhs, prems')
          end
      end
        handle Pattern.MATCH => NONE
    fun rewrite_subterm prems ct (Abs (x, _, _)) =
      let
        val ((v, ct'), ctxt') = Variable.dest_abs_cterm ct ctxt;
        val (thm, prems) = rewrite' ctxt' prems (x :: bounds) thms ct'
      in
        if Thm.is_reflexive thm then
          (Thm.reflexive ct, prems)
        else
          (Thm.abstract_rule x v thm, prems)
      end
    | rewrite_subterm prems ct (_ $ _) =
      let
        val (cs, ct) = Thm.dest_comb ct
        val (thm, prems') = rewrite' ctxt prems bounds thms cs
        val (thm', prems'') = rewrite' ctxt prems' bounds thms ct
      in
        (Thm.combination thm thm', prems'')
      end
    | rewrite_subterm prems ct _ = (Thm.reflexive ct, prems)
    val t = Thm.term_of ct
  in
    case get_first (apply_rule t) thms of
      NONE => rewrite_subterm old_prems ct t
    | SOME (thm, rhs, prems) =>
        case rewrite' ctxt prems bounds thms rhs of
          (thm', prems) => (Thm.transitive thm thm', prems)
  end

fun rewrite ctxt thms ct =
  let
    val thm1 = Thm.eta_long_conversion ct
    val rhs = thm1 |> Thm.cprop_of |> Thm.dest_comb |> snd
    val (thm2, prems) = rewrite' ctxt [] [] thms rhs
    val rhs = thm2 |> Thm.cprop_of |> Thm.dest_comb |> snd
    val thm3 = Thm.eta_conversion rhs
    val thm = Thm.transitive thm1 (Thm.transitive thm2 thm3)
  in
    fold (fn prem => fn thm => Thm.implies_intr (Thm.cterm_of ctxt prem) thm) prems thm
  end

fun preproc_term_conv ctxt = 
  let
    val thms = Named_Theorems.get ctxt \<^named_theorems>\<open>real_asymp_reify_simps\<close>
    val thms = map (fn thm => thm RS @{thm HOL.eq_reflection}) thms
  in
    rewrite ctxt thms
  end

fun register_custom' binding pat expand context =
  let
    val n = pat |> fastype_of |> strip_type |> fst |> length
    val maxidx = Term.maxidx_of_term pat
    val vars = map (fn i => Var ((Name.uu_, maxidx + i), \<^typ>\<open>real\<close>)) (1 upto n)
    val net_pat = Library.foldl betapply (pat, vars)
    val {name_table = tbl, net = net} = Custom_Funs.get context
    val entry' = {pat = pat, net_pat = net_pat, expand = expand}
    val (name, tbl) = Name_Space.define context true (binding, entry') tbl
    val entry = {name = name, pat = pat, net_pat = net_pat, expand = expand}
    val net = Item_Net.update entry net
  in
    Custom_Funs.put {name_table = tbl, net = net} context
  end

fun register_custom binding pat expand = 
  let
    fun decl phi =
      register_custom' binding (Morphism.term phi pat) expand
  in
    Local_Theory.declaration {syntax = false, pervasive = false} decl
  end

fun register_custom_from_thm binding thm expand = 
  let
    val pat = thm |> Thm.concl_of |> HOLogic.dest_Trueprop |> dest_comb |> snd
  in
    register_custom binding pat expand
  end

fun expand_custom ctxt name =
  let
    val {name_table, ...} = Custom_Funs.get (Context.Proof ctxt)
  in
    case Name_Space.lookup name_table name of
      NONE => NONE
    | SOME {expand, ...} => SOME expand
  end

fun expr_to_term e = 
  let
    fun expr_to_term' (ConstExpr c) = c
      | expr_to_term' X = Bound 0
      | expr_to_term' (Add (a, b)) = 
          \<^term>\<open>(+) :: real => _\<close> $ expr_to_term' a $ expr_to_term' b
      | expr_to_term' (Mult (a, b)) = 
          \<^term>\<open>(*) :: real => _\<close> $ expr_to_term' a $ expr_to_term' b
      | expr_to_term' (Minus (a, b)) = 
          \<^term>\<open>(-) :: real => _\<close> $ expr_to_term' a $ expr_to_term' b
      | expr_to_term' (Div (a, b)) = 
          \<^term>\<open>(/) :: real => _\<close> $ expr_to_term' a $ expr_to_term' b
      | expr_to_term' (Uminus a) = 
          \<^term>\<open>uminus :: real => _\<close> $ expr_to_term' a
      | expr_to_term' (Inverse a) = 
          \<^term>\<open>inverse :: real => _\<close> $ expr_to_term' a
      | expr_to_term' (Ln a) = 
          \<^term>\<open>ln :: real => _\<close> $ expr_to_term' a
      | expr_to_term' (Exp a) = 
          \<^term>\<open>exp :: real => _\<close> $ expr_to_term' a
      | expr_to_term' (Powr (a,b)) = 
          \<^term>\<open>(powr) :: real => _\<close> $ expr_to_term' a $ expr_to_term' b
      | expr_to_term' (Powr_Nat (a,b)) = 
          \<^term>\<open>powr_nat :: real => _\<close> $ expr_to_term' a $ expr_to_term' b
      | expr_to_term' (LnPowr (a,b)) = 
          \<^term>\<open>ln :: real => _\<close> $ 
            (\<^term>\<open>(powr) :: real => _\<close> $ expr_to_term' a $ expr_to_term' b)
      | expr_to_term' (ExpLn a) = 
          \<^term>\<open>exp :: real => _\<close> $ (\<^term>\<open>ln :: real => _\<close> $ expr_to_term' a)
      | expr_to_term' (Powr' (a,b)) = 
          \<^term>\<open>(powr) :: real => _\<close> $ expr_to_term' a $ b
      | expr_to_term' (Power (a,b)) = 
          \<^term>\<open>(^) :: real => _\<close> $ expr_to_term' a $ b
      | expr_to_term' (Floor a) =
          \<^term>\<open>Multiseries_Expansion.rfloor\<close> $ expr_to_term' a
      | expr_to_term' (Ceiling a) =
          \<^term>\<open>Multiseries_Expansion.rceil\<close> $ expr_to_term' a
      | expr_to_term' (Frac a) =
          \<^term>\<open>Archimedean_Field.frac :: real \<Rightarrow> real\<close> $ expr_to_term' a
      | expr_to_term' (NatMod (a,b)) = 
          \<^term>\<open>Multiseries_Expansion.rnatmod\<close> $ expr_to_term' a $ expr_to_term' b
      | expr_to_term' (Root (a,b)) = 
          \<^term>\<open>root :: nat \<Rightarrow> real \<Rightarrow> _\<close> $ b $ expr_to_term' a
      | expr_to_term' (Sin a) = 
          \<^term>\<open>sin :: real => _\<close> $ expr_to_term' a
      | expr_to_term' (ArcTan a) = 
          \<^term>\<open>arctan :: real => _\<close> $ expr_to_term' a
      | expr_to_term' (Cos a) = 
          \<^term>\<open>cos :: real => _\<close> $ expr_to_term' a
      | expr_to_term' (Absolute a) = 
          \<^term>\<open>abs :: real => _\<close> $ expr_to_term' a
      | expr_to_term' (Sgn a) =
          \<^term>\<open>sgn :: real => _\<close> $ expr_to_term' a
      | expr_to_term' (Min (a,b)) = 
          \<^term>\<open>min :: real => _\<close> $ expr_to_term' a $ expr_to_term' b
      | expr_to_term' (Max (a,b)) = 
          \<^term>\<open>max :: real => _\<close> $ expr_to_term' a $ expr_to_term' b
      | expr_to_term' (Custom (_, t, args)) = Envir.beta_eta_contract (
          fold (fn e => fn t => betapply (t, expr_to_term' e )) args t)
  in
    Abs ("x", \<^typ>\<open>real\<close>, expr_to_term' e)
  end

fun reify_custom ctxt t =
  let
    val thy = Proof_Context.theory_of ctxt
    val t = Envir.beta_eta_contract t
    val t' = Envir.beta_eta_contract (Term.abs ("x", \<^typ>\<open>real\<close>) t)
    val {net, ...} = Custom_Funs.get (Context.Proof ctxt)
    val entries = Item_Net.retrieve_matching net (Term.subst_bound (Free ("x", \<^typ>\<open>real\<close>), t))
    fun go {pat, name, ...} =
      let
        val n = pat |> fastype_of |> strip_type |> fst |> length
        val maxidx = Term.maxidx_of_term t'
        val vs = map (fn i => (Name.uu_, maxidx + i)) (1 upto n)
        val args = map (fn v => Var (v, \<^typ>\<open>real => real\<close>) $ Bound 0) vs
        val pat' = 
          Envir.beta_eta_contract (Term.abs ("x", \<^typ>\<open>real\<close>) 
            (Library.foldl betapply (pat, args)))
        val (T_insts, insts) = Pattern.match thy (pat', t') (Vartab.empty, Vartab.empty)
        fun map_option _ [] acc = SOME (rev acc)
          | map_option f (x :: xs) acc =
              case f x of
                NONE => NONE
              | SOME y => map_option f xs (y :: acc)
        val t = Envir.subst_term (T_insts, insts) pat
      in
        Option.map (pair (name, t)) (map_option (Option.map snd o Vartab.lookup insts) vs [])
      end
        handle Pattern.MATCH => NONE
  in
    get_first go entries
  end

fun reify_aux ctxt t' t =
  let
    fun is_const t =
      fastype_of (Abs ("x", \<^typ>\<open>real\<close>, t)) = \<^typ>\<open>real \<Rightarrow> real\<close> 
        andalso not (exists_subterm (fn t => t = Bound 0) t)
    fun is_const' t = not (exists_subterm (fn t => t = Bound 0) t)
    fun reify'' (\<^term>\<open>(+) :: real => _\<close> $ s $ t) =
          Add (reify' s, reify' t)
      | reify'' (\<^term>\<open>(-) :: real => _\<close> $ s $ t) =
          Minus (reify' s, reify' t)
      | reify'' (\<^term>\<open>(*) :: real => _\<close> $ s $ t) =
          Mult (reify' s, reify' t)
      | reify'' (\<^term>\<open>(/) :: real => _\<close> $ s $ t) =
          Div (reify' s, reify' t)
      | reify'' (\<^term>\<open>uminus :: real => _\<close> $ s) =
          Uminus (reify' s)
      | reify'' (\<^term>\<open>inverse :: real => _\<close> $ s) =
          Inverse (reify' s)
      | reify'' (\<^term>\<open>ln :: real => _\<close> $ (\<^term>\<open>(powr) :: real => _\<close> $ s $ t)) =
          LnPowr (reify' s, reify' t)
      | reify'' (\<^term>\<open>exp :: real => _\<close> $ (\<^term>\<open>ln :: real => _\<close> $ s)) =
          ExpLn (reify' s)
      | reify'' (\<^term>\<open>ln :: real => _\<close> $ s) =
          Ln (reify' s)
      | reify'' (\<^term>\<open>exp :: real => _\<close> $ s) =
          Exp (reify' s)
      | reify'' (\<^term>\<open>(powr) :: real => _\<close> $ s $ t) =
          (if is_const t then Powr' (reify' s, t) else Powr (reify' s, reify' t))
      | reify'' (\<^term>\<open>powr_nat :: real => _\<close> $ s $ t) =
          Powr_Nat (reify' s, reify' t)
      | reify'' (\<^term>\<open>(^) :: real => _\<close> $ s $ t) =
          (if is_const' t then Power (reify' s, t) else raise TERM ("reify", [t']))
      | reify'' (\<^term>\<open>root\<close> $ s $ t) =
          (if is_const' s then Root (reify' t, s) else raise TERM ("reify", [t']))
      | reify'' (\<^term>\<open>abs :: real => _\<close> $ s) =
          Absolute (reify' s)
      | reify'' (\<^term>\<open>sgn :: real => _\<close> $ s) =
          Sgn (reify' s)
      | reify'' (\<^term>\<open>min :: real => _\<close> $ s $ t) =
          Min (reify' s, reify' t)
      | reify'' (\<^term>\<open>max :: real => _\<close> $ s $ t) =
          Max (reify' s, reify' t)
      | reify'' (\<^term>\<open>Multiseries_Expansion.rfloor\<close> $ s) =
          Floor (reify' s)
      | reify'' (\<^term>\<open>Multiseries_Expansion.rceil\<close> $ s) =
          Ceiling (reify' s)
      | reify'' (\<^term>\<open>Archimedean_Field.frac :: real \<Rightarrow> real\<close> $ s) =
          Frac (reify' s)
      | reify'' (\<^term>\<open>Multiseries_Expansion.rnatmod\<close> $ s $ t) =
          NatMod (reify' s, reify' t)
      | reify'' (\<^term>\<open>sin :: real => _\<close> $ s) =
          Sin (reify' s)
      | reify'' (\<^term>\<open>arctan :: real => _\<close> $ s) =
          ArcTan (reify' s)
      | reify'' (\<^term>\<open>cos :: real => _\<close> $ s) =
          Cos (reify' s)
      | reify'' (Bound 0) = X
      | reify'' t = 
          case reify_custom ctxt t of
            SOME ((name, t), ts) => 
              let
                val args = map (reify_aux ctxt t') ts
              in
                Custom (name, t, args)
              end
          | NONE => raise TERM ("reify", [t'])
    and reify' t = if is_const t then ConstExpr t else reify'' t
  in
    case Envir.eta_long [] t of 
      Abs (_, \<^typ>\<open>real\<close>, t'') => reify' t''
    | _ => raise TERM ("reify", [t])
  end

fun reify ctxt t =
  let
    val thm = preproc_term_conv ctxt (Thm.cterm_of ctxt t)
    val rhs = thm |> Thm.concl_of |> Logic.dest_equals |> snd
  in
    (reify_aux ctxt t rhs, thm)
  end

fun reify_simple_aux ctxt t' t =
  let
    fun is_const t =
      fastype_of (Abs ("x", \<^typ>\<open>real\<close>, t)) = \<^typ>\<open>real \<Rightarrow> real\<close> 
        andalso not (exists_subterm (fn t => t = Bound 0) t)
    fun is_const' t = not (exists_subterm (fn t => t = Bound 0) t)
    fun reify'' (\<^term>\<open>(+) :: real => _\<close> $ s $ t) =
          Add (reify'' s, reify'' t)
      | reify'' (\<^term>\<open>(-) :: real => _\<close> $ s $ t) =
          Minus (reify'' s, reify'' t)
      | reify'' (\<^term>\<open>(*) :: real => _\<close> $ s $ t) =
          Mult (reify'' s, reify'' t)
      | reify'' (\<^term>\<open>(/) :: real => _\<close> $ s $ t) =
          Div (reify'' s, reify'' t)
      | reify'' (\<^term>\<open>uminus :: real => _\<close> $ s) =
          Uminus (reify'' s)
      | reify'' (\<^term>\<open>inverse :: real => _\<close> $ s) =
          Inverse (reify'' s)
      | reify'' (\<^term>\<open>ln :: real => _\<close> $ s) =
          Ln (reify'' s)
      | reify'' (\<^term>\<open>exp :: real => _\<close> $ s) =
          Exp (reify'' s)
      | reify'' (\<^term>\<open>(powr) :: real => _\<close> $ s $ t) =
          Powr (reify'' s, reify'' t)
      | reify'' (\<^term>\<open>powr_nat :: real => _\<close> $ s $ t) =
          Powr_Nat (reify'' s, reify'' t)
      | reify'' (\<^term>\<open>(^) :: real => _\<close> $ s $ t) =
          (if is_const' t then Power (reify'' s, t) else raise TERM ("reify", [t']))
      | reify'' (\<^term>\<open>root\<close> $ s $ t) =
          (if is_const' s then Root (reify'' t, s) else raise TERM ("reify", [t']))
      | reify'' (\<^term>\<open>abs :: real => _\<close> $ s) =
          Absolute (reify'' s)
      | reify'' (\<^term>\<open>sgn :: real => _\<close> $ s) =
          Sgn (reify'' s)
      | reify'' (\<^term>\<open>min :: real => _\<close> $ s $ t) =
          Min (reify'' s, reify'' t)
      | reify'' (\<^term>\<open>max :: real => _\<close> $ s $ t) =
          Max (reify'' s, reify'' t)
      | reify'' (\<^term>\<open>Multiseries_Expansion.rfloor\<close> $ s) =
          Floor (reify'' s)
      | reify'' (\<^term>\<open>Multiseries_Expansion.rceil\<close> $ s) =
          Ceiling (reify'' s)
      | reify'' (\<^term>\<open>Archimedean_Field.frac :: real \<Rightarrow> real\<close> $ s) =
          Frac (reify'' s)
      | reify'' (\<^term>\<open>Multiseries_Expansion.rnatmod\<close> $ s $ t) =
          NatMod (reify'' s, reify'' t)
      | reify'' (\<^term>\<open>sin :: real => _\<close> $ s) =
          Sin (reify'' s)
      | reify'' (\<^term>\<open>cos :: real => _\<close> $ s) =
          Cos (reify'' s)
      | reify'' (Bound 0) = X
      | reify'' t = 
          if is_const t then 
            ConstExpr t 
          else 
            case reify_custom ctxt t of
              SOME ((name, t), ts) => 
                let
                  val args = map (reify_aux ctxt t') ts
                in
                  Custom (name, t, args)
                end
            | NONE => raise TERM ("reify", [t'])
  in
    case Envir.eta_long [] t of 
      Abs (_, \<^typ>\<open>real\<close>, t'') => reify'' t''
    | _ => raise TERM ("reify", [t])
  end

fun reify_simple ctxt t =
  let
    val thm = preproc_term_conv ctxt (Thm.cterm_of ctxt t)
    val rhs = thm |> Thm.concl_of |> Logic.dest_equals |> snd
  in
    (reify_simple_aux ctxt t rhs, thm)
  end

fun simple_print_const (Free (x, _)) = x
  | simple_print_const (\<^term>\<open>uminus :: real => real\<close> $ a) =
      "(-" ^ simple_print_const a ^ ")"
  | simple_print_const (\<^term>\<open>(+) :: real => _\<close> $ a $ b) =
      "(" ^ simple_print_const a ^ "+" ^ simple_print_const b ^ ")"
  | simple_print_const (\<^term>\<open>(-) :: real => _\<close> $ a $ b) =
      "(" ^ simple_print_const a ^ "-" ^ simple_print_const b ^ ")"
  | simple_print_const (\<^term>\<open>(*) :: real => _\<close> $ a $ b) =
      "(" ^ simple_print_const a ^ "*" ^ simple_print_const b ^ ")"
  | simple_print_const (\<^term>\<open>inverse :: real => _\<close> $ a) =
      "(1 / " ^ simple_print_const a ^ ")"
  | simple_print_const (\<^term>\<open>(/) :: real => _\<close> $ a $ b) =
      "(" ^ simple_print_const a ^ "/" ^ simple_print_const b ^ ")"
  | simple_print_const t = Int.toString (snd (HOLogic.dest_number t))

fun to_mathematica (Add (a, b)) = "(" ^ to_mathematica a ^ " + " ^ to_mathematica b ^ ")"
  | to_mathematica (Minus (a, b)) = "(" ^ to_mathematica a ^ " - " ^ to_mathematica b ^ ")"
  | to_mathematica (Mult (a, b)) = "(" ^ to_mathematica a ^ " * " ^ to_mathematica b ^ ")"
  | to_mathematica (Div (a, b)) = "(" ^ to_mathematica a ^ " / " ^ to_mathematica b ^ ")"
  | to_mathematica (Powr (a, b)) = "(" ^ to_mathematica a ^ " ^ " ^ to_mathematica b ^ ")"
  | to_mathematica (Powr_Nat (a, b)) = "(" ^ to_mathematica a ^ " ^ " ^ to_mathematica b ^ ")"
  | to_mathematica (Powr' (a, b)) = "(" ^ to_mathematica a ^ " ^ " ^ 
       to_mathematica (ConstExpr b) ^ ")"
  | to_mathematica (LnPowr (a, b)) = "Log[" ^ to_mathematica a ^ " ^ " ^ to_mathematica b ^ "]"
  | to_mathematica (ExpLn a) = "Exp[Ln[" ^ to_mathematica a ^ "]]"
  | to_mathematica (Power (a, b)) = "(" ^ to_mathematica a ^ " ^ " ^
       to_mathematica (ConstExpr b) ^ ")"
  | to_mathematica (Root (a, \<^term>\<open>2::real\<close>)) = "Sqrt[" ^ to_mathematica a ^ "]"
  | to_mathematica (Root (a, b)) = "Surd[" ^ to_mathematica a ^ ", " ^
       to_mathematica (ConstExpr b) ^ "]"
  | to_mathematica (Uminus a) = "(-" ^ to_mathematica a ^ ")"
  | to_mathematica (Inverse a) = "(1/(" ^ to_mathematica a ^ "))"
  | to_mathematica (Exp a) = "Exp[" ^ to_mathematica a ^ "]"
  | to_mathematica (Ln a) = "Log[" ^ to_mathematica a ^ "]"
  | to_mathematica (Sin a) = "Sin[" ^ to_mathematica a ^ "]"
  | to_mathematica (Cos a) = "Cos[" ^ to_mathematica a ^ "]"
  | to_mathematica (ArcTan a) = "ArcTan[" ^ to_mathematica a ^ "]"
  | to_mathematica (Absolute a) = "Abs[" ^ to_mathematica a ^ "]"
  | to_mathematica (Sgn a) = "Sign[" ^ to_mathematica a ^ "]"
  | to_mathematica (Min (a, b)) = "Min[" ^ to_mathematica a ^ ", " ^ to_mathematica b ^ "]"
  | to_mathematica (Max (a, b)) = "Max[" ^ to_mathematica a ^ ", " ^ to_mathematica b ^ "]"
  | to_mathematica (Floor a) = "Floor[" ^ to_mathematica a ^ "]"
  | to_mathematica (Ceiling a) = "Ceiling[" ^ to_mathematica a ^ "]"
  | to_mathematica (Frac a) = "Mod[" ^ to_mathematica a ^ ", 1]"
  | to_mathematica (ConstExpr t) = simple_print_const t
  | to_mathematica X = "X"

(* TODO: correct translation of frac() for Maple and Sage *)
fun to_maple (Add (a, b)) = "(" ^ to_maple a ^ " + " ^ to_maple b ^ ")"
  | to_maple (Minus (a, b)) = "(" ^ to_maple a ^ " - " ^ to_maple b ^ ")"
  | to_maple (Mult (a, b)) = "(" ^ to_maple a ^ " * " ^ to_maple b ^ ")"
  | to_maple (Div (a, b)) = "(" ^ to_maple a ^ " / " ^ to_maple b ^ ")"
  | to_maple (Powr (a, b)) = "(" ^ to_maple a ^ " ^ " ^ to_maple b ^ ")"
  | to_maple (Powr_Nat (a, b)) = "(" ^ to_maple a ^ " ^ " ^ to_maple b ^ ")"
  | to_maple (Powr' (a, b)) = "(" ^ to_maple a ^ " ^ " ^ 
       to_maple (ConstExpr b) ^ ")"
  | to_maple (LnPowr (a, b)) = "ln(" ^ to_maple a ^ " ^ " ^ to_maple b ^ ")"
  | to_maple (ExpLn a) = "ln(exp(" ^ to_maple a ^ "))"
  | to_maple (Power (a, b)) = "(" ^ to_maple a ^ " ^ " ^
       to_maple (ConstExpr b) ^ ")"
  | to_maple (Root (a, \<^term>\<open>2::real\<close>)) = "sqrt(" ^ to_maple a ^ ")"
  | to_maple (Root (a, b)) = "root(" ^ to_maple a ^ ", " ^
       to_maple (ConstExpr b) ^ ")"
  | to_maple (Uminus a) = "(-" ^ to_maple a ^ ")"
  | to_maple (Inverse a) = "(1/(" ^ to_maple a ^ "))"
  | to_maple (Exp a) = "exp(" ^ to_maple a ^ ")"
  | to_maple (Ln a) = "ln(" ^ to_maple a ^ ")"
  | to_maple (Sin a) = "sin(" ^ to_maple a ^ ")"
  | to_maple (Cos a) = "cos(" ^ to_maple a ^ ")"
  | to_maple (ArcTan a) = "arctan(" ^ to_maple a ^ ")"
  | to_maple (Absolute a) = "abs(" ^ to_maple a ^ ")"
  | to_maple (Sgn a) = "signum(" ^ to_maple a ^ ")"
  | to_maple (Min (a, b)) = "min(" ^ to_maple a ^ ", " ^ to_maple b ^ ")"
  | to_maple (Max (a, b)) = "max(" ^ to_maple a ^ ", " ^ to_maple b ^ ")"
  | to_maple (Floor a) = "floor(" ^ to_maple a ^ ")"
  | to_maple (Ceiling a) = "ceil(" ^ to_maple a ^ ")"
  | to_maple (Frac a) = "frac(" ^ to_maple a ^ ")"
  | to_maple (ConstExpr t) = simple_print_const t
  | to_maple X = "x"

fun to_maxima (Add (a, b)) = "(" ^ to_maxima a ^ " + " ^ to_maxima b ^ ")"
  | to_maxima (Minus (a, b)) = "(" ^ to_maxima a ^ " - " ^ to_maxima b ^ ")"
  | to_maxima (Mult (a, b)) = "(" ^ to_maxima a ^ " * " ^ to_maxima b ^ ")"
  | to_maxima (Div (a, b)) = "(" ^ to_maxima a ^ " / " ^ to_maxima b ^ ")"
  | to_maxima (Powr (a, b)) = "(" ^ to_maxima a ^ " ^ " ^ to_maxima b ^ ")"
  | to_maxima (Powr_Nat (a, b)) = "(" ^ to_maxima a ^ " ^ " ^ to_maxima b ^ ")"
  | to_maxima (Powr' (a, b)) = "(" ^ to_maxima a ^ " ^ " ^ 
       to_maxima (ConstExpr b) ^ ")"
  | to_maxima (ExpLn a) = "exp (log (" ^ to_maxima a ^ "))"
  | to_maxima (LnPowr (a, b)) = "log(" ^ to_maxima a ^ " ^ " ^ to_maxima b ^ ")"
  | to_maxima (Power (a, b)) = "(" ^ to_maxima a ^ " ^ " ^
       to_maxima (ConstExpr b) ^ ")"
  | to_maxima (Root (a, \<^term>\<open>2::real\<close>)) = "sqrt(" ^ to_maxima a ^ ")"
  | to_maxima (Root (a, b)) = to_maxima a ^ "^(1/" ^
       to_maxima (ConstExpr b) ^ ")"
  | to_maxima (Uminus a) = "(-" ^ to_maxima a ^ ")"
  | to_maxima (Inverse a) = "(1/(" ^ to_maxima a ^ "))"
  | to_maxima (Exp a) = "exp(" ^ to_maxima a ^ ")"
  | to_maxima (Ln a) = "log(" ^ to_maxima a ^ ")"
  | to_maxima (Sin a) = "sin(" ^ to_maxima a ^ ")"
  | to_maxima (Cos a) = "cos(" ^ to_maxima a ^ ")"
  | to_maxima (ArcTan a) = "atan(" ^ to_maxima a ^ ")"
  | to_maxima (Absolute a) = "abs(" ^ to_maxima a ^ ")"
  | to_maxima (Sgn a) = "signum(" ^ to_maxima a ^ ")"
  | to_maxima (Min (a, b)) = "min(" ^ to_maxima a ^ ", " ^ to_maxima b ^ ")"
  | to_maxima (Max (a, b)) = "max(" ^ to_maxima a ^ ", " ^ to_maxima b ^ ")"
  | to_maxima (Floor a) = "floor(" ^ to_maxima a ^ ")"
  | to_maxima (Ceiling a) = "ceil(" ^ to_maxima a ^ ")"
  | to_maxima (Frac a) = let val x = to_maxima a in "(" ^ x ^ " - floor(" ^ x ^ "))" end
  | to_maxima (ConstExpr t) = simple_print_const t
  | to_maxima X = "x"

fun to_sympy (Add (a, b)) = "(" ^ to_sympy a ^ " + " ^ to_sympy b ^ ")"
  | to_sympy (Minus (a, b)) = "(" ^ to_sympy a ^ " - " ^ to_sympy b ^ ")"
  | to_sympy (Mult (a, b)) = "(" ^ to_sympy a ^ " * " ^ to_sympy b ^ ")"
  | to_sympy (Div (a, b)) = "(" ^ to_sympy a ^ " / " ^ to_sympy b ^ ")"
  | to_sympy (Powr (a, b)) = "(" ^ to_sympy a ^ " ** " ^ to_sympy b ^ ")"
  | to_sympy (Powr_Nat (a, b)) = "(" ^ to_sympy a ^ " ** " ^ to_sympy b ^ ")"
  | to_sympy (Powr' (a, b)) = "(" ^ to_sympy a ^ " ** " ^ 
       to_sympy (ConstExpr b) ^ ")"
  | to_sympy (ExpLn a) = "exp (log (" ^ to_sympy a ^ "))"
  | to_sympy (LnPowr (a, b)) = "log(" ^ to_sympy a ^ " ** " ^ to_sympy b ^ ")"
  | to_sympy (Power (a, b)) = "(" ^ to_sympy a ^ " ** " ^
       to_sympy (ConstExpr b) ^ ")"
  | to_sympy (Root (a, \<^term>\<open>2::real\<close>)) = "sqrt(" ^ to_sympy a ^ ")"
  | to_sympy (Root (a, b)) = "root(" ^ to_sympy a ^ ", " ^ to_sympy (ConstExpr b) ^ ")"
  | to_sympy (Uminus a) = "(-" ^ to_sympy a ^ ")"
  | to_sympy (Inverse a) = "(1/(" ^ to_sympy a ^ "))"
  | to_sympy (Exp a) = "exp(" ^ to_sympy a ^ ")"
  | to_sympy (Ln a) = "log(" ^ to_sympy a ^ ")"
  | to_sympy (Sin a) = "sin(" ^ to_sympy a ^ ")"
  | to_sympy (Cos a) = "cos(" ^ to_sympy a ^ ")"
  | to_sympy (ArcTan a) = "atan(" ^ to_sympy a ^ ")"
  | to_sympy (Absolute a) = "abs(" ^ to_sympy a ^ ")"
  | to_sympy (Sgn a) = "sign(" ^ to_sympy a ^ ")"
  | to_sympy (Min (a, b)) = "min(" ^ to_sympy a ^ ", " ^ to_sympy b ^ ")"
  | to_sympy (Max (a, b)) = "max(" ^ to_sympy a ^ ", " ^ to_sympy b ^ ")"
  | to_sympy (Floor a) = "floor(" ^ to_sympy a ^ ")"
  | to_sympy (Ceiling a) = "ceiling(" ^ to_sympy a ^ ")"
  | to_sympy (Frac a) = "frac(" ^ to_sympy a ^ ")"
  | to_sympy (ConstExpr t) = simple_print_const t
  | to_sympy X = "x"

fun to_sage (Add (a, b)) = "(" ^ to_sage a ^ " + " ^ to_sage b ^ ")"
  | to_sage (Minus (a, b)) = "(" ^ to_sage a ^ " - " ^ to_sage b ^ ")"
  | to_sage (Mult (a, b)) = "(" ^ to_sage a ^ " * " ^ to_sage b ^ ")"
  | to_sage (Div (a, b)) = "(" ^ to_sage a ^ " / " ^ to_sage b ^ ")"
  | to_sage (Powr (a, b)) = "(" ^ to_sage a ^ " ^ " ^ to_sage b ^ ")"
  | to_sage (Powr_Nat (a, b)) = "(" ^ to_sage a ^ " ^ " ^ to_sage b ^ ")"
  | to_sage (Powr' (a, b)) = "(" ^ to_sage a ^ " ^ " ^ 
       to_sage (ConstExpr b) ^ ")"
  | to_sage (ExpLn a) = "exp (log (" ^ to_sage a ^ "))"
  | to_sage (LnPowr (a, b)) = "log(" ^ to_sage a ^ " ^ " ^ to_sage b ^ ")"
  | to_sage (Power (a, b)) = "(" ^ to_sage a ^ " ^ " ^
       to_sage (ConstExpr b) ^ ")"
  | to_sage (Root (a, \<^term>\<open>2::real\<close>)) = "sqrt(" ^ to_sage a ^ ")"
  | to_sage (Root (a, b)) = to_sage a ^ "^(1/" ^ to_sage (ConstExpr b) ^ ")"
  | to_sage (Uminus a) = "(-" ^ to_sage a ^ ")"
  | to_sage (Inverse a) = "(1/(" ^ to_sage a ^ "))"
  | to_sage (Exp a) = "exp(" ^ to_sage a ^ ")"
  | to_sage (Ln a) = "log(" ^ to_sage a ^ ")"
  | to_sage (Sin a) = "sin(" ^ to_sage a ^ ")"
  | to_sage (Cos a) = "cos(" ^ to_sage a ^ ")"
  | to_sage (ArcTan a) = "atan(" ^ to_sage a ^ ")"
  | to_sage (Absolute a) = "abs(" ^ to_sage a ^ ")"
  | to_sage (Sgn a) = "sign(" ^ to_sage a ^ ")"
  | to_sage (Min (a, b)) = "min(" ^ to_sage a ^ ", " ^ to_sage b ^ ")"
  | to_sage (Max (a, b)) = "max(" ^ to_sage a ^ ", " ^ to_sage b ^ ")"
  | to_sage (Floor a) = "floor(" ^ to_sage a ^ ")"
  | to_sage (Ceiling a) = "ceil(" ^ to_sage a ^ ")"
  | to_sage (Frac a) = "frac(" ^ to_sage a ^ ")"
  | to_sage (ConstExpr t) = simple_print_const t
  | to_sage X = "x"

fun reify_mathematica ctxt = to_mathematica o fst o reify_simple ctxt
fun reify_maple ctxt = to_maple o fst o reify_simple ctxt
fun reify_maxima ctxt = to_maxima o fst o reify_simple ctxt
fun reify_sympy ctxt = to_sympy o fst o reify_simple ctxt
fun reify_sage ctxt = to_sage o fst o reify_simple ctxt

fun limit_mathematica s = "Limit[" ^ s ^ ", X -> Infinity]"
fun limit_maple s = "limit(" ^ s ^ ", x = infinity);"
fun limit_maxima s = "limit(" ^ s ^ ", x, inf);"
fun limit_sympy s = "limit(" ^ s ^ ", x, oo)"
fun limit_sage s = "limit(" ^ s ^ ", x = Infinity)"

end

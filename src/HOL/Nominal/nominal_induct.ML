(* $Id$ *)

local

(* A function that takes a list of Variables and a term t;                    *)
(* it builds up an abstraction of the Variables packaged in a tuple(!)        *)
(* over the term t.                                                           *)
(* E.g  tuple_lambda [] t        produces %x . t where x is a dummy Variable  *) 
(*      tuple_lambda [a] t       produces %a . t                              *) 
(*      tuple_lambda [a,b,c] t   produces %(a,b,c). t                         *)

fun tuple_lambda [] t  = Abs ("x", HOLogic.unitT, t)
  | tuple_lambda [x] t = lambda x t
  | tuple_lambda (x::xs) t =
    let
        val t' = tuple_lambda xs t;
        val Type ("fun", [T,U]) = fastype_of t';
    in
        HOLogic.split_const (fastype_of x,T,U) $ lambda x t'
    end; 

fun find_var frees name =
  (case Library.find_first (equal name o fst o dest_Free) frees of
    NONE => error ("No such Variable in term: " ^ quote name)
  | SOME v => v);

(* - names specifies the variables that are involved in the *)
(*   induction                                              *)
(* - rule is the induction rule to be applied               *)              
fun nominal_induct_tac (names, rule) facts state =
  let
    val sg     = Thm.sign_of_thm state;
    val cert   = Thm.cterm_of sg;
    val goal :: _ = Thm.prems_of state;  (*exception Subscript*)
    val frees  = Term.term_frees goal;
    val frees' = filter_out (fn Free (x, _) => exists (equal x) names) frees;
    val vars = map (find_var frees) names;

    fun inst_rule rule =
      let
        val concl_vars = map Var (rev (Term.add_vars (Thm.concl_of rule) []));
        val (P :: ts, x) = split_last concl_vars
          handle Empty => error "Malformed conclusion of induction rule"
               | Bind  => error "Malformed conclusion of induction rule";
      in
        cterm_instantiate
          ((cert P, cert (fold_rev lambda vars (tuple_lambda frees' (HOLogic.dest_Trueprop goal)))) ::
           (cert x, cert (if null frees' then HOLogic.unit else foldr1 HOLogic.mk_prod frees')) ::
           (map cert ts ~~ map cert vars)) rule
      end;

    val simplify_rule =
      Simplifier.full_simplify (HOL_basic_ss addsimps
        [split_conv, split_paired_All, split_paired_all]);

    val facts1 = Library.take (1, facts);
    val facts2 = Library.drop (1, facts);

  in
    rule
    |> inst_rule
    |> Method.multi_resolve facts1
    |> Seq.map simplify_rule
    |> Seq.map (RuleCases.save rule)
    |> Seq.map RuleCases.add
    |> Seq.map (fn (r, (cases, _)) =>
        HEADGOAL (Method.insert_tac facts2 THEN' Tactic.rtac r) state
        |> Seq.map (rpair (RuleCases.make false NONE (sg, Thm.prop_of r) cases)))
    |> Seq.flat
  end
  handle Subscript => Seq.empty;

val rule_spec = Scan.lift (Args.$$$ "rule" -- Args.colon) |-- Attrib.local_thm;

val nominal_induct_args =
  Scan.repeat (Scan.unless rule_spec (Scan.lift Args.name)) -- rule_spec;

in

val nominal_induct_method =
  Method.RAW_METHOD_CASES o nominal_induct_tac oo (#2 oo Method.syntax nominal_induct_args);

(* nominal_induc_method needs to have the type

   Args.src -> Proof.context -> Proof.method

   CHECK THAT

*)

end;

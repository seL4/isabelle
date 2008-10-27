(*  Title:      Pure/Isar/expression.ML
    ID:         $Id$
    Author:     Clemens Ballarin, TU Muenchen

Locale expressions --- experimental.
*)

signature EXPRESSION =
sig

type map
type 'morph expr

type expression = (string * map) expr * (Name.binding * string option * mixfix) list
type expression_i = Morphism.morphism expr * (Name.binding * typ option * mixfix) list

val parse_expr: OuterParse.token list -> expression * OuterParse.token list
val debug_parameters: expression -> Proof.context -> Proof.context
val debug_context: expression -> Proof.context -> Proof.context

end;


structure Expression: EXPRESSION =
struct

(* Locale expressions *)

datatype map =
  Positional of string option list |
  Named of (string * string) list;

datatype 'morph expr = Expr of (string * 'morph) list;

type expression = (string * map) expr * (Name.binding * string option * mixfix) list;
type expression_i = Morphism.morphism expr * (Name.binding * typ option * mixfix) list;


(** Parsing and printing **)

local

structure P = OuterParse;

val loc_keyword = P.$$$ "fixes" || P.$$$ "constrains" || P.$$$ "assumes" ||
   P.$$$ "defines" || P.$$$ "notes" || P.$$$ "includes";
fun plus1_unless test scan =
  scan ::: Scan.repeat (P.$$$ "+" |-- Scan.unless test (P.!!! scan));

val prefix = P.name --| P.$$$ ":";
val named = P.name -- (P.$$$ "=" |-- P.term);
val position = P.maybe P.term;
val instance = P.$$$ "where" |-- P.and_list1 named >> Named ||
  Scan.repeat1 position >> Positional;

in

val parse_expr =
  let
    fun expr2 x = P.xname x;
    fun expr1 x = (Scan.optional prefix "" -- expr2 --
      Scan.optional instance (Named []) >> (fn ((p, l), i) => (l, (p, i)))) x;
    fun expr0 x = (plus1_unless loc_keyword expr1 >> Expr) x;
  in expr0 -- P.for_fixes end;

end;

(*
fun pretty_expr thy (Locale loc) =
      [Pretty.str "Locale", Pretty.brk 1, Pretty.str (Locale.extern thy loc)]
  | pretty_expr thy (Instance (expr, (prfx, Positional insts))) =
      let
        val insts' = (* chop trailing NONEs *)
      
  | pretty_expr thy (Instance (expr, (prfx, Named insts))) =
*)


(** Processing of locale expression **)

fun intern thy (Expr instances) = Expr (map (apfst (Locale.intern thy)) instances);


(* Parameters of expression (not expression_i).
   Sanity check of instantiations.
   Positional instantiations are extended to match full length of parameter list. *)

fun parameters thy (expr, fixed) =
  let
    fun reject_dups message xs =
      let val dups = duplicates (op =) xs
      in
        if null dups then () else error (message ^ commas dups)
      end;

    fun params2 loc =
          (Locale.parameters_of thy loc |> map (fn ((p, _), mx) => (p, mx)), loc) ;
    fun params1 (loc, (prfx, Positional insts)) =
          let
            val (ps, loc') = params2 loc;
	    val d = length ps - length insts;
	    val insts' =
	      if d < 0 then error ("More arguments than parameters in instantiation.")
(* FIXME print expr *)
	      else insts @ replicate d NONE;
            val ps' = (ps ~~ insts') |>
              map_filter (fn (p, NONE) => SOME p | (_, SOME _) => NONE);
          in
            (ps', (loc', (prfx, Positional insts')))
          end
      | params1 (loc, (prfx, Named insts)) =
          let
            val _ = reject_dups "Duplicate instantiation of the following parameter(s): "
              (map fst insts);
(* FIXME print expr *)

            val (ps, loc') = params2 loc;
            val ps' = fold (fn (p, _) => fn ps =>
              if AList.defined (op =) ps p then AList.delete (op =) p ps
              else error (quote p ^" not a parameter of instantiated expression.")) insts ps;
(* FIXME print expr *)
(* FIXME AList lacks a version of delete that signals the absence of the deleted item *)
          in
            (ps', (loc', (prfx, Named insts)))
          end;
    fun params0 (Expr is) =
          let
            val (is', ps') = fold_map (fn i => fn ps =>
              let
                val (ps', i') = params1 i;
                val ps'' = AList.join (op =) (fn p => fn (mx1, mx2) =>
                  if mx1 = mx2 then mx1
                  else error ("Conflicting syntax for parameter" ^ quote p ^ " in expression.")) (ps, ps')
(* FIXME print Expr is *)
              in (i', ps'') end) is []
          in
            (ps', Expr is')
          end;

    val (parms, expr') = params0 expr;

    val parms' = map fst parms;
    val fixed' = map (#1 #> Name.name_of) fixed;
    val _ = reject_dups "Duplicate fixed parameter(s): " fixed';
    val _ = reject_dups "Parameter(s) declared simultaneously in expression and for clause: " (parms' @ fixed');

  in (expr', (parms, fixed)) end;

fun debug_parameters raw_expr ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val expr = apfst (intern thy) raw_expr;
    val (expr', (parms, fixed)) = parameters thy expr;
  in ctxt end;


fun debug_context (raw_expr, fixed) ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val expr = intern thy raw_expr;
    val (expr', (parms, fixed)) = parameters thy (expr, fixed);

    fun declare_parameters (parms, fixed) ctxt =
      let
      val (parms', ctxt') =
        ProofContext.add_fixes (map (fn (p, mx) => (Name.binding p, NONE, mx)) parms) ctxt;
      val (fixed', ctxt'') =
        ProofContext.add_fixes fixed ctxt';
      in
        (parms' @ fixed', ctxt'')
      end;

    fun rough_inst loc prfx insts ctxt =
      let
        (* locale data *)
        val (parm_names, parm_types) = loc |> Locale.parameters_of thy |>
          map fst |> split_list;

        (* type parameters *)
        val type_parm_names = fold Term.add_tfreesT parm_types [] |> map fst;

        (* parameter instantiations *)
        val insts' = case insts of
          Positional insts => (insts ~~ parm_names) |> map (fn
            (NONE, p) => Syntax.parse_term ctxt p |
            (SOME t, _) => Syntax.parse_term ctxt t) |
          Named insts => parm_names |> map (fn
            p => case AList.lookup (op =) insts p of
              SOME t => Syntax.parse_term ctxt t |
              NONE => Syntax.parse_term ctxt p);

	(* type inference and contexts *)
        val parm_types' = map (TypeInfer.paramify_vars o Logic.varifyT) parm_types;
        val type_parms = fold Term.add_tvarsT parm_types' [] |> map (Logic.mk_type o TVar);
	val arg = type_parms @ map2 TypeInfer.constrain parm_types' insts';
	val res = Syntax.check_terms ctxt arg;
	val ctxt' = ctxt |> fold Variable.auto_fixes res;

	(* instantiation *)
	val (type_parms'', res') = chop (length type_parms) res;
        val insts'' = (parm_names ~~ res') |> map_filter
          (fn (inst as (x, Free (y, _))) => if x = y then NONE else SOME inst |
            inst => SOME inst);
	val instT = Symtab.make (type_parm_names ~~ map Logic.dest_type type_parms'');
	val inst = Symtab.make insts'';
      in
        (Element.inst_morphism thy (instT, inst) $>
          Morphism.name_morphism (Name.qualified prfx), ctxt')
      end;

    fun add_declarations loc morph ctxt =
      let
        (* locale data *)
        val parms = loc |> Locale.parameters_of thy;
        val (typ_decls, term_decls) = Locale.declarations_of thy loc;

        (* declarations from locale *)
	val ctxt'' = ctxt |>
	  fold_rev (fn decl => Context.proof_map (decl morph)) typ_decls |>
	  fold_rev (fn decl => Context.proof_map (decl morph)) term_decls;
      in
        ctxt''
      end;

    val Expr [(loc1, (prfx1, insts1))] = expr';
    val ctxt0 = ProofContext.init thy;
    val (parms, ctxt') = declare_parameters (parms, fixed) ctxt0;
    val (morph1, ctxt'') = rough_inst loc1 prfx1 insts1 ctxt';
    val ctxt'' = add_declarations loc1 morph1 ctxt';
  in ctxt'' end;


end;

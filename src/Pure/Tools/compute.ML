(*  Title:      Pure/Tools/compute.ML
    ID:         $Id$
    Author:     Steven Obua
*)

signature COMPUTE = sig

    type computer

    exception Make of string

    val basic_make : theory -> thm list -> computer
    val make : theory -> thm list -> computer

    val compute : computer -> (int -> string) -> cterm -> term
    val theory_of : computer -> theory

    val rewrite_param : computer -> (int -> string) -> cterm -> thm
    val rewrite : computer -> cterm -> thm

end

structure Compute : COMPUTE = struct

exception Make of string;

fun is_mono_typ (Type (_, list)) = List.all is_mono_typ list
  | is_mono_typ _ = false

fun is_mono_term (Const (_, t)) = is_mono_typ t
  | is_mono_term (Var (_, t)) = is_mono_typ t
  | is_mono_term (Free (_, t)) = is_mono_typ t
  | is_mono_term (Bound _) = true
  | is_mono_term (a $ b) = is_mono_term a andalso is_mono_term b
  | is_mono_term (Abs (_, ty, t)) = is_mono_typ ty andalso is_mono_term t

structure AMTermTab = TableFun (type key = AbstractMachine.term val ord = AM_Util.term_ord)

fun add x y = x + y : int;
fun inc x = x + 1;

exception Mono of term;

val remove_types =
    let
        fun remove_types_var table invtable ccount vcount ldepth t =
            (case Termtab.lookup table t of
                 NONE =>
                 let
                     val a = AbstractMachine.Var vcount
                 in
                     (Termtab.update (t, a) table,
                      AMTermTab.update (a, t) invtable,
                      ccount,
                      inc vcount,
                      AbstractMachine.Var (add vcount ldepth))
                 end
               | SOME (AbstractMachine.Var v) =>
                 (table, invtable, ccount, vcount, AbstractMachine.Var (add v ldepth))
               | SOME _ => sys_error "remove_types_var: lookup should be a var")

        fun remove_types_const table invtable ccount vcount ldepth t =
            (case Termtab.lookup table t of
                 NONE =>
                 let
                     val a = AbstractMachine.Const ccount
                 in
                     (Termtab.update (t, a) table,
                      AMTermTab.update (a, t) invtable,
                      inc ccount,
                      vcount,
                      a)
                 end
               | SOME (c as AbstractMachine.Const _) =>
                 (table, invtable, ccount, vcount, c)
               | SOME _ => sys_error "remove_types_const: lookup should be a const")

        fun remove_types table invtable ccount vcount ldepth t =
            case t of
                Var (_, ty) =>
                  if is_mono_typ ty then remove_types_var table invtable ccount vcount ldepth t
                  else raise (Mono t)
              | Free (_, ty) =>
                  if is_mono_typ ty then remove_types_var table invtable ccount vcount ldepth t
                  else raise (Mono t)
              | Const (_, ty) =>
                  if is_mono_typ ty then remove_types_const table invtable ccount vcount ldepth t
                  else raise (Mono t)
              | Abs (_, ty, t') =>
                if is_mono_typ ty then
                    let
                        val (table, invtable, ccount, vcount, t') =
                            remove_types table invtable ccount vcount (inc ldepth) t'
                    in
                        (table, invtable, ccount, vcount, AbstractMachine.Abs t')
                    end
                else
                    raise (Mono t)
              | a $ b =>
                let
                    val (table, invtable, ccount, vcount, a) =
                        remove_types table invtable ccount vcount ldepth a
                    val (table, invtable, ccount, vcount, b) =
                        remove_types table invtable ccount vcount ldepth b
                in
                    (table, invtable, ccount, vcount, AbstractMachine.App (a,b))
                end
              | Bound b => (table, invtable, ccount, vcount, AbstractMachine.Var b)
    in
     fn (table, invtable, ccount, vcount) => remove_types table invtable ccount vcount 0
    end

fun infer_types naming =
    let
        fun infer_types invtable ldepth bounds ty (AbstractMachine.Var v) =
            if v < ldepth then (Bound v, List.nth (bounds, v)) else
            (case AMTermTab.lookup invtable (AbstractMachine.Var (v-ldepth)) of
                 SOME (t as Var (_, ty)) => (t, ty)
               | SOME (t as Free (_, ty)) => (t, ty)
               | _ => sys_error "infer_types: lookup should deliver Var or Free")
          | infer_types invtable ldepth _ ty (c as AbstractMachine.Const _) =
            (case AMTermTab.lookup invtable c of
                 SOME (c as Const (_, ty)) => (c, ty)
               | _ => sys_error "infer_types: lookup should deliver Const")
          | infer_types invtable ldepth bounds (n,ty) (AbstractMachine.App (a, b)) =
            let
                val (a, aty) = infer_types invtable ldepth bounds (n+1, ty) a
                val (adom, arange) =
                    case aty of
                        Type ("fun", [dom, range]) => (dom, range)
                      | _ => sys_error "infer_types: function type expected"
                val (b, bty) = infer_types invtable ldepth bounds (0, adom) b
            in
                (a $ b, arange)
            end
          | infer_types invtable ldepth bounds (0, ty as Type ("fun", [dom, range]))
              (AbstractMachine.Abs m) =
            let
                val (m, _) = infer_types invtable (ldepth+1) (dom::bounds) (0, range) m
            in
                (Abs (naming ldepth, dom, m), ty)
            end
          | infer_types invtable ldepth bounds ty (AbstractMachine.Abs m) =
            sys_error "infer_types: cannot infer type of abstraction"

        fun infer invtable ty term =
            let
                val (term', _) = infer_types invtable 0 [] (0, ty) term
            in
                term'
            end
    in
        infer
    end

datatype computer =
  Computer of theory_ref *
    (AbstractMachine.term Termtab.table * term AMTermTab.table * int * AbstractMachine.program)

fun basic_make thy raw_ths =
    let
        val ths = map (Thm.transfer thy) raw_ths;

        fun thm2rule table invtable ccount th =
            let
                val prop = Drule.plain_prop_of th
                  handle THM _ => raise (Make "theorems must be plain propositions")
                val (a, b) = Logic.dest_equals prop
                  handle TERM _ => raise (Make "theorems must be meta-level equations")

                val (table, invtable, ccount, vcount, prop) =
                    remove_types (table, invtable, ccount, 0) (a$b)
                    handle Mono _ => raise (Make "no type variables allowed")
                val (left, right) =
                    (case prop of AbstractMachine.App x => x | _ =>
                      sys_error "make: remove_types should deliver application")

                fun make_pattern table invtable n vars (var as AbstractMachine.Var v) =
                    let
                        val var' = valOf (AMTermTab.lookup invtable var)
                        val table = Termtab.delete var' table
                        val invtable = AMTermTab.delete var invtable
                        val vars = Inttab.update_new (v, n) vars handle Inttab.DUP _ =>
                          raise (Make "no duplicate variable in pattern allowed")
                    in
                        (table, invtable, n+1, vars, AbstractMachine.PVar)
                    end
                  | make_pattern table invtable n vars (AbstractMachine.Abs _) =
                      raise (Make "no lambda abstractions allowed in pattern")
                  | make_pattern table invtable n vars (AbstractMachine.Const c) =
                    (table, invtable, n, vars, AbstractMachine.PConst (c, []))
                  | make_pattern table invtable n vars (AbstractMachine.App (a, b)) =
                    let
                        val (table, invtable, n, vars, pa) =
                            make_pattern table invtable n vars a
                        val (table, invtable, n, vars, pb) =
                            make_pattern table invtable n vars b
                    in
                        case pa of
                            AbstractMachine.PVar =>
                              raise (Make "patterns may not start with a variable")
                          | AbstractMachine.PConst (c, args) =>
                              (table, invtable, n, vars, AbstractMachine.PConst (c, args@[pb]))
                    end

                val (table, invtable, vcount, vars, pattern) =
                    make_pattern table invtable 0 Inttab.empty left
                val _ = (case pattern of
                           AbstractMachine.PVar =>
                             raise (Make "patterns may not start with a variable")
                         | _ => ())

                (* at this point, there shouldn't be any variables
                  left in table or invtable, only constants *)

                (* finally, provide a function for renaming the
                  pattern bound variables on the right hand side *)

                fun rename ldepth vars (var as AbstractMachine.Var v) =
                    if v < ldepth then var
                    else (case Inttab.lookup vars (v - ldepth) of
                              NONE => raise (Make "new variable on right hand side")
                            | SOME n => AbstractMachine.Var ((vcount-n-1)+ldepth))
                  | rename ldepth vars (c as AbstractMachine.Const _) = c
                  | rename ldepth vars (AbstractMachine.App (a, b)) =
                    AbstractMachine.App (rename ldepth vars a, rename ldepth vars b)
                  | rename ldepth vars (AbstractMachine.Abs m) =
                    AbstractMachine.Abs (rename (ldepth+1) vars m)

            in
                (table, invtable, ccount, (pattern, rename 0 vars right))
            end

        val (table, invtable, ccount, rules) =
          fold_rev (fn th => fn (table, invtable, ccount, rules) =>
            let
              val (table, invtable, ccount, rule) =
                  thm2rule table invtable ccount th
            in (table, invtable, ccount, rule::rules) end)
          ths (Termtab.empty, AMTermTab.empty, 0, [])

        val prog = AbstractMachine.compile rules

    in Computer (Theory.self_ref thy, (table, invtable, ccount, prog)) end

fun make thy ths =
    let
      val (_, {mk_rews={mk=mk,mk_eq_True=emk, ...},...}) = rep_ss (simpset_of thy)
      fun mk_eq_True th = (case emk th of NONE => [th] | SOME th' => [th, th'])
      fun app f l = List.concat (map f l)
    in
      basic_make thy (app mk (app mk_eq_True ths))
    end

fun compute (Computer r) naming ct =
    let
        val {t=t, T=ty, thy=ctthy, ...} = rep_cterm ct
        val (rthy, (table, invtable, ccount, prog)) = r
        val thy = Theory.merge (Theory.deref rthy, ctthy)
        val (table, invtable, ccount, vcount, t) = remove_types (table, invtable, ccount, 0) t
        val t = AbstractMachine.run prog t
        val t = infer_types naming invtable ty t
    in
        t
    end

fun theory_of (Computer (rthy, _)) = Theory.deref rthy

fun default_naming i = "v_" ^ Int.toString i

exception Param of computer * (int -> string) * cterm;

fun rewrite_param r n ct =
    let val thy = theory_of_cterm ct in
      invoke_oracle_i thy "Pure.compute" (thy, Param (r, n, ct))
    end

fun rewrite r ct = rewrite_param r default_naming ct


(* theory setup *)

fun compute_oracle (thy, Param (r, naming, ct)) =
    let
        val _ = Theory.assert_super (theory_of r) thy
        val t' = compute r naming ct
    in
        Logic.mk_equals (term_of ct, t')
    end

val _ = Context.add_setup (Theory.add_oracle ("compute", compute_oracle))

end

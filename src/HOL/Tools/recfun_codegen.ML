(*  Title:      HOL/Tools/recfun_codegen.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen

Code generator for recursive functions.
*)

signature RECFUN_CODEGEN =
sig
  val add: string option -> attribute
  val add_default: attribute
  val del: attribute
  val setup: theory -> theory
end;

structure RecfunCodegen : RECFUN_CODEGEN =
struct

open Codegen;

structure RecCodegenData = TheoryDataFun
(
  type T = (thm * string option) list Symtab.table;
  val empty = Symtab.empty;
  val copy = I;
  val extend = I;
  fun merge _ = Symtab.merge_list (Thm.eq_thm_prop o pairself fst);
);

val dest_eqn = HOLogic.dest_eq o HOLogic.dest_Trueprop;
val lhs_of = fst o dest_eqn o prop_of;
val const_of = dest_Const o head_of o fst o dest_eqn;

fun warn thm = warning ("RecfunCodegen: Not a proper equation:\n" ^
  Display.string_of_thm thm);

fun add_thm opt_module thm =
  (if Pattern.pattern (lhs_of thm) then
    RecCodegenData.map
      (Symtab.cons_list ((fst o const_of o prop_of) thm, (thm, opt_module)))
  else tap (fn _ => warn thm))
  handle TERM _ => tap (fn _ => warn thm);

fun add opt_module = Thm.declaration_attribute (fn thm => Context.mapping
  (add_thm opt_module thm #> Code.add_liberal_func thm) I);

val add_default = Thm.declaration_attribute (fn thm => Context.mapping
  (add_thm NONE thm #> Code.add_default_func thm) I);

fun del_thm thm = case try const_of (prop_of thm)
 of SOME (s, _) => RecCodegenData.map
      (Symtab.map_entry s (remove (Thm.eq_thm o apsnd fst) thm))
  | NONE => tap (fn _ => warn thm);

val del = Thm.declaration_attribute
  (fn thm => Context.mapping (del_thm thm #> Code.del_func thm) I)

fun del_redundant thy eqs [] = eqs
  | del_redundant thy eqs (eq :: eqs') =
    let
      val matches = curry
        (Pattern.matches thy o pairself (lhs_of o fst))
    in del_redundant thy (eq :: eqs) (filter_out (matches eq) eqs') end;

fun get_equations thy defs (s, T) =
  (case Symtab.lookup (RecCodegenData.get thy) s of
     NONE => ([], "")
   | SOME thms => 
       let val thms' = del_redundant thy []
         (filter (fn (thm, _) => is_instance T
           (snd (const_of (prop_of thm)))) thms)
       in if null thms' then ([], "")
         else (preprocess thy (map fst thms'),
           case snd (snd (split_last thms')) of
               NONE => (case get_defn thy defs s T of
                   NONE => Codegen.thyname_of_const thy s
                 | SOME ((_, (thyname, _)), _) => thyname)
             | SOME thyname => thyname)
       end);

fun mk_suffix thy defs (s, T) = (case get_defn thy defs s T of
  SOME (_, SOME i) => " def" ^ string_of_int i | _ => "");

exception EQN of string * typ * string;

fun cycle g (xs, x : string) =
  if member (op =) xs x then xs
  else Library.foldl (cycle g) (x :: xs, flat (Graph.all_paths (fst g) (x, x)));

fun add_rec_funs thy defs gr dep eqs module =
  let
    fun dest_eq t = (fst (const_of t) ^ mk_suffix thy defs (const_of t),
      dest_eqn (rename_term t));
    val eqs' = map dest_eq eqs;
    val (dname, _) :: _ = eqs';
    val (s, T) = const_of (hd eqs);

    fun mk_fundef module fname first gr [] = (gr, [])
      | mk_fundef module fname first gr ((fname' : string, (lhs, rhs)) :: xs) =
      let
        val prfx = if first then
            (case strip_comb lhs of (_, []) => "val " | _ => "fun ")
          else "and ";
        val (gr1, pl) = invoke_codegen thy defs dname module false (gr, lhs);
        val (gr2, pr) = invoke_codegen thy defs dname module false (gr1, rhs);
        val (gr3, rest) = mk_fundef module fname' false gr2 xs
      in
        (gr3, Pretty.blk (4, [str (if fname = fname' then "  | " else prfx),
           pl, str " =", Pretty.brk 1, pr]) :: rest)
      end;

    fun put_code module fundef = map_node dname
      (K (SOME (EQN ("", dummyT, dname)), module, string_of (Pretty.blk (0,
      separate Pretty.fbrk fundef @ [str ";"])) ^ "\n\n"));

  in
    (case try (get_node gr) dname of
       NONE =>
         let
           val gr1 = add_edge (dname, dep)
             (new_node (dname, (SOME (EQN (s, T, "")), module, "")) gr);
           val (gr2, fundef) = mk_fundef module "" true gr1 eqs';
           val xs = cycle gr2 ([], dname);
           val cs = map (fn x => case get_node gr2 x of
               (SOME (EQN (s, T, _)), _, _) => (s, T)
             | _ => error ("RecfunCodegen: illegal cyclic dependencies:\n" ^
                implode (separate ", " xs))) xs
         in (case xs of
             [_] => (put_code module fundef gr2, module)
           | _ =>
             if not (dep mem xs) then
               let
                 val thmss as (_, thyname) :: _ = map (get_equations thy defs) cs;
                 val module' = if_library thyname module;
                 val eqs'' = map (dest_eq o prop_of) (List.concat (map fst thmss));
                 val (gr3, fundef') = mk_fundef module' "" true
                   (add_edge (dname, dep)
                     (foldr (uncurry new_node) (del_nodes xs gr2)
                       (map (fn k =>
                         (k, (SOME (EQN ("", dummyT, dname)), module', ""))) xs))) eqs''
               in (put_code module' fundef' gr3, module') end
             else (gr2, module))
         end
     | SOME (SOME (EQN (_, _, s)), module', _) =>
         (if s = "" then
            if dname = dep then gr else add_edge (dname, dep) gr
          else if s = dep then gr else add_edge (s, dep) gr,
          module'))
  end;

fun recfun_codegen thy defs gr dep module brack t = (case strip_comb t of
    (Const (p as (s, T)), ts) => (case (get_equations thy defs p, get_assoc_code thy (s, T)) of
       (([], _), _) => NONE
     | (_, SOME _) => NONE
     | ((eqns, thyname), NONE) =>
        let
          val module' = if_library thyname module;
          val (gr', ps) = foldl_map
            (invoke_codegen thy defs dep module true) (gr, ts);
          val suffix = mk_suffix thy defs p;
          val (gr'', module'') =
            add_rec_funs thy defs gr' dep (map prop_of eqns) module';
          val (gr''', fname) = mk_const_id module'' (s ^ suffix) gr''
        in
          SOME (gr''', mk_app brack (str (mk_qual_id module fname)) ps)
        end)
  | _ => NONE);


val setup =
  add_codegen "recfun" recfun_codegen
  #> Code.add_attribute ("", Args.del |-- Scan.succeed del
     || Scan.option (Args.$$$ "target" |-- Args.colon |-- Args.name) >> add);

end;

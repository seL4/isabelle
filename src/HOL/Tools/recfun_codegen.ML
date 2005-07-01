(*  Title:      HOL/recfun_codegen.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen

Code generator for recursive functions.
*)

signature RECFUN_CODEGEN =
sig
  val add: string option -> theory attribute
  val del: theory attribute
  val setup: (theory -> theory) list
end;

structure RecfunCodegen : RECFUN_CODEGEN =
struct

open Codegen;

structure CodegenData = TheoryDataFun
(struct
  val name = "HOL/recfun_codegen";
  type T = (thm * string option) list Symtab.table;
  val empty = Symtab.empty;
  val copy = I;
  val extend = I;
  fun merge _ = Symtab.merge_multi' (Drule.eq_thm_prop o pairself fst);
  fun print _ _ = ();
end);


val dest_eqn = HOLogic.dest_eq o HOLogic.dest_Trueprop;
val lhs_of = fst o dest_eqn o prop_of;
val const_of = dest_Const o head_of o fst o dest_eqn;

fun warn thm = warning ("RecfunCodegen: Not a proper equation:\n" ^
  string_of_thm thm);

fun add optmod (p as (thy, thm)) =
  let
    val tab = CodegenData.get thy;
    val (s, _) = const_of (prop_of thm);
  in
    if Pattern.pattern (lhs_of thm) then
      (CodegenData.put (Symtab.update ((s,
        (thm, optmod) :: getOpt (Symtab.lookup (tab, s), [])), tab)) thy, thm)
    else (warn thm; p)
  end handle TERM _ => (warn thm; p);

fun del (p as (thy, thm)) =
  let
    val tab = CodegenData.get thy;
    val (s, _) = const_of (prop_of thm);
  in case Symtab.lookup (tab, s) of
      NONE => p
    | SOME thms => (CodegenData.put (Symtab.update ((s,
        gen_rem (eq_thm o apfst fst) (thms, thm)), tab)) thy, thm)
  end handle TERM _ => (warn thm; p);

fun del_redundant thy eqs [] = eqs
  | del_redundant thy eqs (eq :: eqs') =
    let
      val tsig = Sign.tsig_of (sign_of thy);
      val matches = curry
        (Pattern.matches tsig o pairself (lhs_of o fst))
    in del_redundant thy (eq :: eqs) (filter_out (matches eq) eqs') end;

fun get_equations thy defs (s, T) =
  (case Symtab.lookup (CodegenData.get thy, s) of
     NONE => ([], "")
   | SOME thms => 
       let val thms' = del_redundant thy []
         (List.filter (fn (thm, _) => is_instance thy T
           (snd (const_of (prop_of thm)))) thms)
       in if null thms' then ([], "")
         else (preprocess thy (map fst thms'),
           case snd (snd (split_last thms')) of
               NONE => (case get_defn thy defs s T of
                   NONE => thyname_of_const s thy
                 | SOME ((_, (thyname, _)), _) => thyname)
             | SOME thyname => thyname)
       end);

fun mk_suffix thy defs (s, T) = (case get_defn thy defs s T of
  SOME (_, SOME i) => "_def" ^ string_of_int i | _ => "");

exception EQN of string * typ * string;

fun cycle g (xs, x) =
  if x mem xs then xs
  else Library.foldl (cycle g) (x :: xs, List.concat (Graph.find_paths g (x, x)));

fun add_rec_funs thy defs gr dep eqs thyname =
  let
    fun dest_eq t = (fst (const_of t) ^ mk_suffix thy defs (const_of t),
      dest_eqn (rename_term t));
    val eqs' = map dest_eq eqs;
    val (dname, _) :: _ = eqs';
    val (s, T) = const_of (hd eqs);

    fun mk_fundef thyname fname prfx gr [] = (gr, [])
      | mk_fundef thyname fname prfx gr ((fname', (lhs, rhs)) :: xs) =
      let
        val (gr1, pl) = invoke_codegen thy defs dname thyname false (gr, lhs);
        val (gr2, pr) = invoke_codegen thy defs dname thyname false (gr1, rhs);
        val (gr3, rest) = mk_fundef thyname fname' "and " gr2 xs
      in
        (gr3, Pretty.blk (4, [Pretty.str (if fname = fname' then "  | " else prfx),
           pl, Pretty.str " =", Pretty.brk 1, pr]) :: rest)
      end;

    fun put_code thyname fundef = Graph.map_node dname
      (K (SOME (EQN ("", dummyT, dname)), thyname, Pretty.string_of (Pretty.blk (0,
      separate Pretty.fbrk fundef @ [Pretty.str ";"])) ^ "\n\n"));

  in
    (case try (Graph.get_node gr) dname of
       NONE =>
         let
           val gr1 = Graph.add_edge (dname, dep)
             (Graph.new_node (dname, (SOME (EQN (s, T, "")), "", "")) gr);
           val (gr2, fundef) = mk_fundef thyname "" "fun " gr1 eqs';
           val xs = cycle gr2 ([], dname);
           val cs = map (fn x => case Graph.get_node gr2 x of
               (SOME (EQN (s, T, _)), _, _) => (s, T)
             | _ => error ("RecfunCodegen: illegal cyclic dependencies:\n" ^
                implode (separate ", " xs))) xs
         in (case xs of
             [_] => put_code thyname fundef gr2
           | _ =>
             if not (dep mem xs) then
               let
                 val thmss as (_, thyname) :: _ = map (get_equations thy defs) cs;
                 val eqs'' = map (dest_eq o prop_of) (List.concat (map fst thmss));
                 val (gr3, fundef') = mk_fundef thyname "" "fun "
                   (Graph.add_edge (dname, dep)
                     (foldr (uncurry Graph.new_node) (Graph.del_nodes xs gr2)
                       (map (fn k =>
                         (k, (SOME (EQN ("", dummyT, dname)), thyname, ""))) xs))) eqs''
               in put_code thyname fundef' gr3 end
             else gr2)
         end
     | SOME (SOME (EQN (_, _, s)), _, _) =>
         if s = "" then
           if dname = dep then gr else Graph.add_edge (dname, dep) gr
         else if s = dep then gr else Graph.add_edge (s, dep) gr)
  end;

fun recfun_codegen thy defs gr dep thyname brack t = (case strip_comb t of
    (Const (p as (s, T)), ts) => (case (get_equations thy defs p, get_assoc_code thy s T) of
       (([], _), _) => NONE
     | (_, SOME _) => NONE
     | ((eqns, thyname'), NONE) =>
        let
          val (gr', ps) = foldl_map
            (invoke_codegen thy defs dep thyname true) (gr, ts);
          val suffix = mk_suffix thy defs p
        in
          SOME (add_rec_funs thy defs gr' dep (map prop_of eqns) thyname',
            mk_app brack (Pretty.str
              (mk_const_id (sign_of thy) thyname thyname' s ^ suffix)) ps)
        end)
  | _ => NONE);


val setup =
  [CodegenData.init,
   add_codegen "recfun" recfun_codegen,
   add_attribute ""
     (   Args.del |-- Scan.succeed del
      || Scan.option (Args.$$$ "target" |-- Args.colon |-- Args.name) >> add)];

end;

(*  Title:      HOL/recfun_codegen.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Code generator for recursive functions.
*)

signature RECFUN_CODEGEN =
sig
  val add: theory attribute
  val setup: (theory -> theory) list
end;

structure RecfunCodegen : RECFUN_CODEGEN =
struct

open Codegen;

structure RecfunArgs =
struct
  val name = "HOL/recfun_codegen";
  type T = thm list Symtab.table;
  val empty = Symtab.empty;
  val copy = I;
  val prep_ext = I;
  val merge = Symtab.merge_multi eq_thm;
  fun print _ _ = ();
end;

structure RecfunData = TheoryDataFun(RecfunArgs);

val prop_of = #prop o rep_thm;
val dest_eqn = HOLogic.dest_eq o HOLogic.dest_Trueprop;
val const_of = dest_Const o head_of o fst o dest_eqn;

fun warn thm = warning ("RecfunCodegen: Not a proper equation:\n" ^
  string_of_thm thm);

fun add (p as (thy, thm)) =
  let
    val tsig = Sign.tsig_of (sign_of thy);
    val tab = RecfunData.get thy;
    val (s, _) = const_of (prop_of thm);

    val matches = curry
      (Pattern.matches tsig o pairself (fst o dest_eqn o prop_of));

  in (RecfunData.put (Symtab.update ((s,
    filter_out (matches thm) (if_none (Symtab.lookup (tab, s)) []) @ [thm]),
      tab)) thy, thm)
  end handle TERM _ => (warn thm; p) | Pattern.Pattern => (warn thm; p);

fun get_equations thy (s, T) =
  (case Symtab.lookup (RecfunData.get thy, s) of
     None => []
   | Some thms => filter (fn thm => is_instance thy T
       (snd (const_of (prop_of thm)))) thms);

fun mk_poly_id thy (s, T) = mk_const_id (sign_of thy) s ^
  (case get_defn thy s T of
     Some (_, Some i) => "_def" ^ string_of_int i
   | _ => "");

exception EQN of string * typ * string;

fun cycle g (xs, x) =
  if x mem xs then xs
  else foldl (cycle g) (x :: xs, flat (Graph.find_paths g (x, x)));

fun add_rec_funs thy gr dep eqs =
  let
    fun dest_eq t =
      (mk_poly_id thy (const_of t), dest_eqn (rename_term t));
    val eqs' = map dest_eq eqs;
    val (dname, _) :: _ = eqs';
    val (s, T) = const_of (hd eqs);

    fun mk_fundef fname prfx gr [] = (gr, [])
      | mk_fundef fname prfx gr ((fname', (lhs, rhs)) :: xs) =
      let
        val (gr1, pl) = invoke_codegen thy dname false (gr, lhs);
        val (gr2, pr) = invoke_codegen thy dname false (gr1, rhs);
        val (gr3, rest) = mk_fundef fname' "and " gr2 xs
      in
        (gr3, Pretty.blk (4, [Pretty.str (if fname = fname' then "  | " else prfx),
           pl, Pretty.str " =", Pretty.brk 1, pr]) :: rest)
      end;

    fun put_code fundef = Graph.map_node dname
      (K (Some (EQN ("", dummyT, dname)), Pretty.string_of (Pretty.blk (0,
      separate Pretty.fbrk fundef @ [Pretty.str ";"])) ^ "\n\n"));

  in
    (case try (Graph.get_node gr) dname of
       None =>
         let
           val gr1 = Graph.add_edge (dname, dep)
             (Graph.new_node (dname, (Some (EQN (s, T, "")), "")) gr);
           val (gr2, fundef) = mk_fundef "" "fun " gr1 eqs';
           val xs = cycle gr2 ([], dname);
           val cs = map (fn x => case Graph.get_node gr2 x of
               (Some (EQN (s, T, _)), _) => (s, T)
             | _ => error ("RecfunCodegen: illegal cyclic dependencies:\n" ^
                implode (separate ", " xs))) xs
         in (case xs of
             [_] => put_code fundef gr2
           | _ =>
             if not (dep mem xs) then
               let
                 val eqs'' = map (dest_eq o prop_of)
                   (flat (map (get_equations thy) cs));
                 val (gr3, fundef') = mk_fundef "" "fun "
                   (Graph.add_edge (dname, dep)
                     (foldr (uncurry Graph.new_node) (map (fn k =>
                       (k, (Some (EQN ("", dummyT, dname)), ""))) xs,
                         Graph.del_nodes xs gr2))) eqs''
               in put_code fundef' gr3 end
             else gr2)
         end
     | Some (Some (EQN (_, _, s)), _) =>
         if s = "" then
           if dname = dep then gr else Graph.add_edge (dname, dep) gr
         else if s = dep then gr else Graph.add_edge (s, dep) gr)
  end;

fun recfun_codegen thy gr dep brack t = (case strip_comb t of
    (Const p, ts) => (case get_equations thy p of
       [] => None
     | eqns =>
        let val (gr', ps) = foldl_map (invoke_codegen thy dep true) (gr, ts)
        in
          Some (add_rec_funs thy gr' dep (map prop_of eqns),
            mk_app brack (Pretty.str (mk_poly_id thy p)) ps)
        end)
  | _ => None);


val setup =
  [RecfunData.init,
   add_codegen "recfun" recfun_codegen,
   Attrib.add_attributes [("code",
     (Attrib.no_args add, Attrib.no_args Attrib.undef_local_attribute),
     "declare equations to be used for code generation")]];

end;

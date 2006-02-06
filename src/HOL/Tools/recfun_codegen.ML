(*  Title:      HOL/recfun_codegen.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen

Code generator for recursive functions.
*)

signature RECFUN_CODEGEN =
sig
  val add: string option -> attribute
  val del: attribute
  val get_rec_equations: theory -> string * typ -> (term list * term) list * typ
  val get_thm_equations: theory -> string * typ -> (thm list * typ) option
  val setup: theory -> theory
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
  fun merge _ = Symtab.merge_list (Drule.eq_thm_prop o pairself fst);
  fun print _ _ = ();
end);


val dest_eqn = HOLogic.dest_eq o HOLogic.dest_Trueprop;
val lhs_of = fst o dest_eqn o prop_of;
val const_of = dest_Const o head_of o fst o dest_eqn;

fun warn thm = warning ("RecfunCodegen: Not a proper equation:\n" ^
  string_of_thm thm);

fun add optmod = Thm.declaration_attribute (fn thm => Context.map_theory (fn thy =>
  let
    val tab = CodegenData.get thy;
    val (s, _) = const_of (prop_of thm);
  in
    if Pattern.pattern (lhs_of thm) then
      CodegenData.put (Symtab.update_list (s, (thm, optmod)) tab) thy
    else (warn thm; thy)
  end handle TERM _ => (warn thm; thy)));

val del = Thm.declaration_attribute (fn thm => Context.map_theory (fn thy =>
  let
    val tab = CodegenData.get thy;
    val (s, _) = const_of (prop_of thm);
  in case Symtab.lookup tab s of
      NONE => thy
    | SOME thms =>
        CodegenData.put (Symtab.update (s, gen_rem (eq_thm o apfst fst) (thms, thm)) tab) thy
  end handle TERM _ => (warn thm; thy)));

fun del_redundant thy eqs [] = eqs
  | del_redundant thy eqs (eq :: eqs') =
    let
      val matches = curry
        (Pattern.matches thy o pairself (lhs_of o fst))
    in del_redundant thy (eq :: eqs) (filter_out (matches eq) eqs') end;

fun get_equations thy defs (s, T) =
  (case Symtab.lookup (CodegenData.get thy) s of
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

fun get_rec_equations thy (s, T) =
  Symtab.lookup (CodegenData.get thy) s
  |> Option.map (fn thms => 
       List.filter (fn (thm, _) => is_instance thy T ((snd o const_of o prop_of) thm)) thms
       |> del_redundant thy [])
  |> Option.mapPartial (fn thms => if null thms then NONE else SOME thms)
  |> Option.map (fn thms =>
       (preprocess thy (map fst thms),
          (snd o const_of o prop_of o fst o hd) thms))
  |> the_default ([], dummyT)
  |> apfst (map prop_of)
  |> apfst (map (Codegen.rename_term #> HOLogic.dest_Trueprop #> HOLogic.dest_eq #> apfst (strip_comb #> snd)))

fun get_thm_equations thy (c, ty) =
  Symtab.lookup (CodegenData.get thy) c
  |> Option.map (fn thms => 
       List.filter (fn (thm, _) => is_instance thy ty ((snd o const_of o prop_of) thm)) thms
       |> del_redundant thy [])
  |> Option.mapPartial (fn thms => if null thms then NONE else SOME thms)
  |> Option.map (fn thms =>
       (preprocess thy (map fst thms),
          (snd o const_of o prop_of o fst o hd) thms))
  |> (Option.map o apfst o map) (fn thm => thm RS HOL.eq_reflection);

fun mk_suffix thy defs (s, T) = (case get_defn thy defs s T of
  SOME (_, SOME i) => " def" ^ string_of_int i | _ => "");

exception EQN of string * typ * string;

fun cycle g (xs, x) =
  if x mem xs then xs
  else Library.foldl (cycle g) (x :: xs, List.concat (Graph.find_paths (fst g) (x, x)));

fun add_rec_funs thy defs gr dep eqs module =
  let
    fun dest_eq t = (fst (const_of t) ^ mk_suffix thy defs (const_of t),
      dest_eqn (rename_term t));
    val eqs' = map dest_eq eqs;
    val (dname, _) :: _ = eqs';
    val (s, T) = const_of (hd eqs);

    fun mk_fundef module fname prfx gr [] = (gr, [])
      | mk_fundef module fname prfx gr ((fname', (lhs, rhs)) :: xs) =
      let
        val (gr1, pl) = invoke_codegen thy defs dname module false (gr, lhs);
        val (gr2, pr) = invoke_codegen thy defs dname module false (gr1, rhs);
        val (gr3, rest) = mk_fundef module fname' "and " gr2 xs
      in
        (gr3, Pretty.blk (4, [Pretty.str (if fname = fname' then "  | " else prfx),
           pl, Pretty.str " =", Pretty.brk 1, pr]) :: rest)
      end;

    fun put_code module fundef = map_node dname
      (K (SOME (EQN ("", dummyT, dname)), module, Pretty.string_of (Pretty.blk (0,
      separate Pretty.fbrk fundef @ [Pretty.str ";"])) ^ "\n\n"));

  in
    (case try (get_node gr) dname of
       NONE =>
         let
           val gr1 = add_edge (dname, dep)
             (new_node (dname, (SOME (EQN (s, T, "")), module, "")) gr);
           val (gr2, fundef) = mk_fundef module "" "fun " gr1 eqs';
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
                 val (gr3, fundef') = mk_fundef module' "" "fun "
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
    (Const (p as (s, T)), ts) => (case (get_equations thy defs p, get_assoc_code thy s T) of
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
          SOME (gr''', mk_app brack (Pretty.str (mk_qual_id module fname)) ps)
        end)
  | _ => NONE);


val setup =
  CodegenData.init #>
  add_codegen "recfun" recfun_codegen #>
  add_attribute ""
    (   Args.del |-- Scan.succeed del
     || Scan.option (Args.$$$ "target" |-- Args.colon |-- Args.name) >> add) #>
  CodegenPackage.add_eqextr
    ("rec", fn thy => fn _ => get_thm_equations thy);

end;

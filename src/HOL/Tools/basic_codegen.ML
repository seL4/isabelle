(*  Title:      Pure/HOL/basic_codegen.ML
    ID:         $Id$
    Author:     Stefan Berghofer
    Copyright   2000  TU Muenchen

Code generator for inductive datatypes and recursive functions
*)

signature BASIC_CODEGEN =
sig
  val setup: (theory -> theory) list
end;

structure BasicCodegen : BASIC_CODEGEN =
struct

open Codegen;

fun mk_poly_id thy (s, T) = mk_const_id (sign_of thy) s ^
  (case get_defn thy s T of
     Some (_, Some i) => "_def" ^ string_of_int i
   | _ => "");

fun mk_tuple [p] = p
  | mk_tuple ps = Pretty.block (Pretty.str "(" ::
      flat (separate [Pretty.str ",", Pretty.brk 1] (map single ps)) @
        [Pretty.str ")"]);

fun add_rec_funs thy dep (gr, eqs) =
  let
    fun dest_eq t =
      let val (lhs, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop
            (Logic.strip_imp_concl (rename_term t)))
      in
        (mk_poly_id thy (dest_Const (head_of lhs)), (lhs, rhs))
      end;
    val eqs' = sort (string_ord o pairself fst) (map dest_eq eqs);
    val (dname, _) :: _ = eqs';

    fun mk_fundef fname prfx gr [] = (gr, [])
      | mk_fundef fname prfx gr ((fname', (lhs, rhs))::xs) =
      let
        val (gr1, pl) = invoke_codegen thy gr dname false lhs;
        val (gr2, pr) = invoke_codegen thy gr1 dname false rhs;
        val (gr3, rest) = mk_fundef fname' "and " gr2 xs
      in
        (gr3, Pretty.blk (4, [Pretty.str (if fname=fname' then "  | " else prfx),
           pl, Pretty.str " =", Pretty.brk 1, pr]) :: rest)
      end

  in
    (Graph.add_edge (dname, dep) gr handle Graph.UNDEF _ =>
       let
         val gr1 = Graph.add_edge (dname, dep)
           (Graph.new_node (dname, (None, "")) gr);
         val (gr2, fundef) = mk_fundef "" "fun " gr1 eqs'
       in
         Graph.map_node dname (K (None, Pretty.string_of (Pretty.blk (0,
           separate Pretty.fbrk fundef @ [Pretty.str ";"])) ^ "\n\n")) gr2
       end)
  end;


(**** generate functions for datatypes specified by descr ****)
(**** (i.e. constructors and case combinators)            ****)

fun mk_typ _ _ (TVar ((s, i), _)) =
     Pretty.str (s ^ (if i=0 then "" else string_of_int i))
  | mk_typ _ _ (TFree (s, _)) = Pretty.str s
  | mk_typ sg types (Type ("fun", [T, U])) = Pretty.block [Pretty.str "(",
     mk_typ sg types T, Pretty.str " ->", Pretty.brk 1,
     mk_typ sg types U, Pretty.str ")"]
  | mk_typ sg types (Type (s, Ts)) = Pretty.block ((if null Ts then [] else
      [mk_tuple (map (mk_typ sg types) Ts), Pretty.str " "]) @
      [Pretty.str (if_none (assoc (types, s)) (mk_type_id sg s))]);

fun add_dt_defs thy dep (gr, descr) =
  let
    val sg = sign_of thy;
    val tab = DatatypePackage.get_datatypes thy;

    val descr' = filter (can (map DatatypeAux.dest_DtTFree o #2 o snd)) descr;

    val (_, (_, _, (cname, _) :: _)) :: _ = descr';
    val dname = mk_const_id sg cname;

    fun mk_dtdef gr prfx [] = (gr, [])
      | mk_dtdef gr prfx ((_, (tname, dts, cs))::xs) =
          let
            val types = get_assoc_types thy;
            val tvs = map DatatypeAux.dest_DtTFree dts;
            val sorts = map (rpair []) tvs;
            val cs' = map (apsnd (map (DatatypeAux.typ_of_dtyp descr sorts))) cs;
            val tycons = foldr add_typ_tycons (flat (map snd cs'), []) \\
              ("fun" :: map fst types);
            val descrs = map (fn s => case Symtab.lookup (tab, s) of
                None => error ("Not a datatype: " ^ s ^ "\nrequired by:\n" ^
                  commas (Graph.all_succs gr [dep]))
              | Some info => #descr info) tycons;
            val gr' = foldl (add_dt_defs thy dname) (gr, descrs);
            val (gr'', rest) = mk_dtdef gr' "and " xs
          in
            (gr'',
             Pretty.block (Pretty.str prfx ::
               (if null tvs then [] else
                  [mk_tuple (map Pretty.str tvs), Pretty.str " "]) @
               [Pretty.str (mk_type_id sg tname ^ " ="), Pretty.brk 1] @
               flat (separate [Pretty.brk 1, Pretty.str "| "]
                 (map (fn (cname, cargs) => [Pretty.block
                   (Pretty.str (mk_const_id sg cname) ::
                    (if null cargs then [] else
                     flat ([Pretty.str " of", Pretty.brk 1] ::
                       separate [Pretty.str " *", Pretty.brk 1]
                         (map (single o mk_typ sg types) cargs))))]) cs'))) :: rest)
          end
  in
    ((Graph.add_edge_acyclic (dname, dep) gr
        handle Graph.CYCLES _ => gr) handle Graph.UNDEF _ =>
         let
           val gr1 = Graph.add_edge (dname, dep)
             (Graph.new_node (dname, (None, "")) gr);
           val (gr2, dtdef) = mk_dtdef gr1 "datatype " descr';
         in
           Graph.map_node dname (K (None,
             Pretty.string_of (Pretty.blk (0, separate Pretty.fbrk dtdef @
               [Pretty.str ";"])) ^ "\n\n")) gr2
         end)
  end;


(**** generate code for applications of constructors and case ****)
(**** combinators for datatypes                               ****)

fun pretty_case thy gr dep brack constrs (c as Const (_, T)) ts =
  let val i = length constrs
  in if length ts <= i then
       invoke_codegen thy gr dep brack (eta_expand c ts (i+1))
    else
      let
        val ts1 = take (i, ts);
        val t :: ts2 = drop (i, ts);
        val names = foldr add_term_names (ts1,
          map (fst o fst o dest_Var) (foldr add_term_vars (ts1, [])));
        val (Ts, dT) = split_last (take (i+1, fst (strip_type T)));

        fun pcase gr [] [] [] = ([], gr)
          | pcase gr ((cname, cargs)::cs) (t::ts) (U::Us) =
              let
                val j = length cargs;
                val (Ts, _) = strip_type (fastype_of t);
                val xs = variantlist (replicate j "x", names);
                val Us' = take (j, fst (strip_type U));
                val frees = map Free (xs ~~ Us');
                val (gr0, cp) = invoke_codegen thy gr dep false
                  (list_comb (Const (cname, Us' ---> dT), frees));
                val t' = Envir.beta_norm (list_comb (t, frees));
                val (gr1, p) = invoke_codegen thy gr0 dep false t';
                val (ps, gr2) = pcase gr1 cs ts Us;
              in
                ([Pretty.block [cp, Pretty.str " =>", Pretty.brk 1, p]] :: ps, gr2)
              end;

        val (ps1, gr1) = pcase gr constrs ts1 Ts;
        val ps = flat (separate [Pretty.brk 1, Pretty.str "| "] ps1);
        val (gr2, p) = invoke_codegen thy gr1 dep false t;
        val (gr3, ps2) = foldl_map
         (fn (gr, t) => invoke_codegen thy gr dep true t) (gr2, ts2)
      in (gr3, (if not (null ts2) andalso brack then parens else I)
        (Pretty.block (separate (Pretty.brk 1)
          (Pretty.block ([Pretty.str "(case ", p, Pretty.str " of",
             Pretty.brk 1] @ ps @ [Pretty.str ")"]) :: ps2))))
      end
  end;


fun pretty_constr thy gr dep brack args (c as Const (s, _)) ts =
  let val i = length args
  in if length ts < i then
      invoke_codegen thy gr dep brack (eta_expand c ts i)
     else
       let
         val id = mk_const_id (sign_of thy) s;
         val (gr', ps) = foldl_map
           (fn (gr, t) => invoke_codegen thy gr dep (i = 1) t) (gr, ts);
       in (case args of
          [] => (gr', Pretty.str id)
        | [_] => (gr', mk_app brack (Pretty.str id) ps)
        | _ => (gr', (if brack then parens else I) (Pretty.block
            ([Pretty.str id, Pretty.brk 1, Pretty.str "("] @
             flat (separate [Pretty.str ",", Pretty.brk 1] (map single ps)) @
             [Pretty.str ")"]))))
       end
  end;


fun mk_recfun thy gr dep brack s T ts eqns =
  let val (gr', ps) = foldl_map
    (fn (gr, t) => invoke_codegen thy gr dep true t) (gr, ts)
  in
    Some (add_rec_funs thy dep (gr', map (#prop o rep_thm) eqns),
      mk_app brack (Pretty.str (mk_poly_id thy (s, T))) ps)
  end;


fun datatype_codegen thy gr dep brack t = (case strip_comb t of
   (c as Const (s, T), ts) =>
       (case find_first (fn (_, {index, descr, case_name, rec_names, ...}) =>
         s = case_name orelse s mem rec_names orelse
           is_some (assoc (#3 (the (assoc (descr, index))), s)))
             (Symtab.dest (DatatypePackage.get_datatypes thy)) of
          None => None
        | Some (tname, {index, descr, case_name, rec_names, rec_rewrites, ...}) =>
           if is_some (get_assoc_code thy s T) then None else
           let
             val Some (_, _, constrs) = assoc (descr, index);
             val gr1 =
              if exists (equal tname o fst) (get_assoc_types thy) then gr
              else add_dt_defs thy dep (gr, descr);
           in
             (case assoc (constrs, s) of
                None => if s mem rec_names then
                    mk_recfun thy gr1 dep brack s T ts rec_rewrites
                  else Some (pretty_case thy gr1 dep brack constrs c ts)
              | Some args => Some (pretty_constr thy gr1 dep brack args c ts))
           end)
 |  _ => None);


(**** generate code for primrec and recdef ****)

fun recfun_codegen thy gr dep brack t = (case strip_comb t of
    (Const (s, T), ts) =>
      (case PrimrecPackage.get_primrec thy s of
         Some ps => (case find_first (fn (_, thm::_) =>
               is_instance thy T (snd (dest_Const (head_of
                 (fst (HOLogic.dest_eq
                   (HOLogic.dest_Trueprop (#prop (rep_thm thm))))))))) ps of
             Some (_, thms) => mk_recfun thy gr dep brack s T ts thms
           | None => None)
       | None => case RecdefPackage.get_recdef thy s of
            Some {simps, ...} => mk_recfun thy gr dep brack s T ts simps
          | None => None)
  | _ => None);


val setup = [add_codegen "datatype" datatype_codegen,
             add_codegen "primrec+recdef" recfun_codegen];

end;

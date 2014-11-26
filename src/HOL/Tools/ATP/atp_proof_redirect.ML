(*  Title:      HOL/Tools/ATP/atp_proof_redirect.ML
    Author:     Jasmin Blanchette, TU Muenchen

Transformation of a proof by contradiction into a direct proof.
*)

signature ATP_ATOM =
sig
  type key
  val ord : key * key -> order
  val string_of : key -> string
end;

signature ATP_PROOF_REDIRECT =
sig
  type atom

  structure Atom_Graph : GRAPH

  type refute_sequent = atom list * atom
  type refute_graph = unit Atom_Graph.T

  type clause = atom list
  type direct_sequent = atom * (atom list * clause)
  type direct_graph = unit Atom_Graph.T

  type rich_sequent = atom * (clause list * clause)

  datatype direct_inference =
    Have of rich_sequent |
    Cases of (clause * direct_inference list) list

  type direct_proof = direct_inference list

  val make_refute_graph : atom -> (atom list * atom) list -> refute_graph
  val axioms_of_refute_graph : refute_graph -> atom list -> atom list
  val tainted_atoms_of_refute_graph : refute_graph -> atom list -> atom list
  val sequents_of_refute_graph : refute_graph -> refute_sequent list
  val string_of_refute_graph : refute_graph -> string
  val redirect_sequent : atom list -> atom -> refute_sequent -> direct_sequent
  val direct_graph : direct_sequent list -> direct_graph
  val redirect_graph : atom list -> atom list -> atom -> refute_graph -> direct_proof
  val succedent_of_cases : (clause * direct_inference list) list -> clause
  val string_of_direct_proof : direct_proof -> string
end;

functor ATP_Proof_Redirect(Atom : ATP_ATOM): ATP_PROOF_REDIRECT =
struct

type atom = Atom.key

structure Atom_Graph = Graph(Atom)

type refute_sequent = atom list * atom
type refute_graph = unit Atom_Graph.T

type clause = atom list
type direct_sequent = atom * (atom list * clause)
type direct_graph = unit Atom_Graph.T

type rich_sequent = atom * (clause list * clause)

datatype direct_inference =
  Have of rich_sequent |
  Cases of (clause * direct_inference list) list

type direct_proof = direct_inference list

val atom_eq = is_equal o Atom.ord
val clause_ord = dict_ord Atom.ord
fun direct_sequent_ord seqp = prod_ord clause_ord clause_ord (apply2 snd seqp)
fun direct_sequent_eq seqp = is_equal (direct_sequent_ord seqp)

fun make_refute_graph bot infers =
  let
    fun add_edge to from =
      Atom_Graph.default_node (from, ())
      #> Atom_Graph.add_edge_acyclic (from, to)
    fun add_infer (froms, to) =
      Atom_Graph.default_node (to, ())
      #> fold (add_edge to) froms

    val graph = fold add_infer infers Atom_Graph.empty
    val reachable = Atom_Graph.all_preds graph [bot]
  in
    graph |> Atom_Graph.restrict (member (is_equal o Atom.ord) reachable)
  end

fun axioms_of_refute_graph refute_graph conjs =
  subtract atom_eq conjs (Atom_Graph.minimals refute_graph)

fun tainted_atoms_of_refute_graph refute_graph = Atom_Graph.all_succs refute_graph

fun sequents_of_refute_graph refute_graph =
  Atom_Graph.keys refute_graph
  |> filter_out (Atom_Graph.is_minimal refute_graph)
  |> map (`(Atom_Graph.immediate_preds refute_graph))

val string_of_context = map Atom.string_of #> space_implode ", "

fun string_of_sequent (gamma, c) =
  string_of_context gamma ^ " \<turnstile> " ^ Atom.string_of c

fun string_of_refute_graph refute_graph =
  refute_graph |> sequents_of_refute_graph |> map string_of_sequent |> cat_lines

fun redirect_sequent tainted bot (gamma, c) =
  (c,
   if member atom_eq tainted c then
     gamma |> List.partition (not o member atom_eq tainted)
           |>> not (atom_eq (c, bot)) ? cons c
   else
     (gamma, [c]))

fun direct_graph seqs =
  let
    fun add_edge from to =
      Atom_Graph.default_node (from, ())
      #> Atom_Graph.default_node (to, ())
      #> Atom_Graph.add_edge_acyclic (from, to)
    fun add_seq (_, (gamma, c)) = fold (fn l => fold (add_edge l) c) gamma
  in
    fold add_seq seqs Atom_Graph.empty
  end

fun disj cs = fold (union atom_eq) cs [] |> sort Atom.ord

fun succedent_of_inference (Have (_, (_, c))) = c
  | succedent_of_inference (Cases cases) = succedent_of_cases cases
and succedent_of_case (c, []) = c
  | succedent_of_case (_, infs) = succedent_of_inference (List.last infs)
and succedent_of_cases cases = disj (map succedent_of_case cases)

fun descendants direct_graph = these o try (Atom_Graph.all_succs direct_graph) o single

fun zones_of 0 _ = []
  | zones_of n (bs :: bss) = (fold (subtract atom_eq) bss) bs :: zones_of (n - 1) (bss @ [bs])

fun redirect_graph axioms tainted bot refute_graph =
  let
    val seqs = map (redirect_sequent tainted bot) (sequents_of_refute_graph refute_graph)
    val direct_graph = direct_graph seqs

    fun redirect c proved seqs =
      if null seqs then
        []
      else if length c < 2 then
        let
          val proved = c @ proved
          val provable = filter (fn (_, (gamma, _)) => subset atom_eq (gamma, proved)) seqs
          val horn_provable = filter (fn (_, (_, [_])) => true | _ => false) provable
          val seq as (id, (gamma, c)) =
            (case horn_provable @ provable of
              [] => raise Fail "ill-formed refutation graph"
            | next :: _ => next)
        in
          Have (id, (map single gamma, c)) ::
          redirect c proved (filter (curry (not o direct_sequent_eq) seq) seqs)
        end
      else
        let
          fun subsequents seqs zone =
            filter (fn (_, (gamma, _)) => subset atom_eq (gamma, zone @ proved)) seqs
          val zones = zones_of (length c) (map (descendants direct_graph) c)
          val subseqss = map (subsequents seqs) zones
          val seqs = fold (subtract direct_sequent_eq) subseqss seqs
          val cases = map2 (fn l => fn subseqs => ([l], redirect [l] proved subseqs)) c subseqss
        in
          Cases cases :: redirect (succedent_of_cases cases) proved seqs
        end
  in
    redirect [] axioms seqs
  end

fun indent 0 = ""
  | indent n = "  " ^ indent (n - 1)

fun string_of_clause [] = "\<bottom>"
  | string_of_clause ls = space_implode " \<or> " (map Atom.string_of ls)

fun string_of_rich_sequent ch (id, (cs, c)) =
  (if null cs then "" else commas (map string_of_clause cs) ^ " ") ^ ch ^ " " ^ string_of_clause c ^
  " (* " ^ Atom.string_of id ^ " *)"

fun string_of_case depth (c, proof) =
  indent (depth + 1) ^ "[" ^ string_of_clause c ^ "]"
  |> not (null proof) ? suffix ("\n" ^ string_of_subproof (depth + 1) proof)

and string_of_inference depth (Have seq) =
    indent depth ^ string_of_rich_sequent "\<triangleright>" seq
  | string_of_inference depth (Cases cases) =
    indent depth ^ "[\n" ^
    space_implode ("\n" ^ indent depth ^ "|\n") (map (string_of_case depth) cases) ^ "\n" ^
    indent depth ^ "]"

and string_of_subproof depth = cat_lines o map (string_of_inference depth)

val string_of_direct_proof = string_of_subproof 0

end;

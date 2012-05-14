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

  type ref_sequent = atom list * atom
  type ref_graph = unit Atom_Graph.T

  type clause = atom list
  type direct_sequent = atom list * clause
  type direct_graph = unit Atom_Graph.T

  type rich_sequent = clause list * clause

  datatype direct_inference =
    Have of rich_sequent |
    Hence of rich_sequent |
    Cases of (clause * direct_inference list) list

  type direct_proof = direct_inference list

  val make_ref_graph : (atom list * atom) list -> ref_graph
  val axioms_of_ref_graph : ref_graph -> atom list -> atom list
  val tainted_atoms_of_ref_graph : ref_graph -> atom list -> atom list
  val sequents_of_ref_graph : ref_graph -> ref_sequent list
  val string_of_ref_graph : ref_graph -> string
  val redirect_sequent : atom list -> atom -> ref_sequent -> direct_sequent
  val direct_graph : direct_sequent list -> direct_graph
  val redirect_graph : atom list -> atom list -> ref_graph -> direct_proof
  val succedent_of_cases : (clause * direct_inference list) list -> clause
  val chain_direct_proof : direct_proof -> direct_proof
  val string_of_direct_proof : direct_proof -> string
end;

functor ATP_Proof_Redirect(Atom : ATP_ATOM): ATP_PROOF_REDIRECT =
struct

type atom = Atom.key

structure Atom_Graph = Graph(Atom)

type ref_sequent = atom list * atom
type ref_graph = unit Atom_Graph.T

type clause = atom list
type direct_sequent = atom list * clause
type direct_graph = unit Atom_Graph.T

type rich_sequent = clause list * clause

datatype direct_inference =
  Have of rich_sequent |
  Hence of rich_sequent |
  Cases of (clause * direct_inference list) list

type direct_proof = direct_inference list

fun atom_eq p = (Atom.ord p = EQUAL)
fun clause_eq (c, d) = (length c = length d andalso forall atom_eq (c ~~ d))
fun direct_sequent_eq ((gamma, c), (delta, d)) =
  clause_eq (gamma, delta) andalso clause_eq (c, d)

fun make_ref_graph infers =
  let
    fun add_edge to from =
      Atom_Graph.default_node (from, ())
      #> Atom_Graph.default_node (to, ())
      #> Atom_Graph.add_edge_acyclic (from, to)
    fun add_infer (froms, to) = fold (add_edge to) froms
  in Atom_Graph.empty |> fold add_infer infers end

fun axioms_of_ref_graph ref_graph conjs =
  subtract atom_eq conjs (Atom_Graph.minimals ref_graph)
fun tainted_atoms_of_ref_graph ref_graph = Atom_Graph.all_succs ref_graph

fun sequents_of_ref_graph ref_graph =
  map (`(Atom_Graph.immediate_preds ref_graph))
      (filter_out (Atom_Graph.is_minimal ref_graph) (Atom_Graph.keys ref_graph))

val string_of_context = map Atom.string_of #> space_implode ", "

fun string_of_sequent (gamma, c) =
  string_of_context gamma ^ " \<turnstile> " ^ Atom.string_of c

val string_of_ref_graph =
  sequents_of_ref_graph #> map string_of_sequent #> implode

fun redirect_sequent tainted bot (gamma, c) =
  if member atom_eq tainted c then
    gamma |> List.partition (not o member atom_eq tainted)
          |>> not (atom_eq (c, bot)) ? cons c
  else
    (gamma, [c])

fun direct_graph seqs =
  let
    fun add_edge from to =
      Atom_Graph.default_node (from, ())
      #> Atom_Graph.default_node (to, ())
      #> Atom_Graph.add_edge_acyclic (from, to)
    fun add_seq (gamma, c) = fold (fn l => fold (add_edge l) c) gamma
  in Atom_Graph.empty |> fold add_seq seqs end

fun disj cs = fold (union atom_eq) cs [] |> sort Atom.ord

fun succedent_of_inference (Have (_, c)) = c
  | succedent_of_inference (Hence (_, c)) = c
  | succedent_of_inference (Cases cases) = succedent_of_cases cases
and succedent_of_case (c, []) = c
  | succedent_of_case (_, infs) = succedent_of_inference (List.last infs)
and succedent_of_cases cases = disj (map succedent_of_case cases)

fun dest_Have (Have z) = z
  | dest_Have _ = raise Fail "non-Have"

fun enrich_Have nontrivs trivs (cs, c) =
  (cs |> map (fn c => if member clause_eq nontrivs c then disj (c :: trivs)
                      else c),
   disj (c :: trivs))
  |> Have

fun s_cases cases =
  case cases |> List.partition (null o snd) of
    (trivs, nontrivs as [(nontriv0, proof)]) =>
    if forall (can dest_Have) proof then
      let val seqs = proof |> map dest_Have in
        seqs |> map (enrich_Have (nontriv0 :: map snd seqs) (map fst trivs))
      end
    else
      [Cases nontrivs]
  | (_, nontrivs) => [Cases nontrivs]

fun descendants direct_graph =
  these o try (Atom_Graph.all_succs direct_graph) o single

fun zones_of 0 _ = []
  | zones_of n (bs :: bss) =
    (fold (subtract atom_eq) bss) bs :: zones_of (n - 1) (bss @ [bs])

fun redirect_graph axioms tainted ref_graph =
  let
    val [bot] = Atom_Graph.maximals ref_graph
    val seqs =
      map (redirect_sequent tainted bot) (sequents_of_ref_graph ref_graph)
    val direct_graph = direct_graph seqs

    fun redirect c proved seqs =
      if null seqs then
        []
      else if length c < 2 then
        let
          val proved = c @ proved
          val provable =
            filter (fn (gamma, _) => subset atom_eq (gamma, proved)) seqs
          val horn_provable = filter (fn (_, [_]) => true | _ => false) provable
          val seq as (gamma, c) = hd (horn_provable @ provable)
        in
          Have (map single gamma, c) ::
          redirect c proved (filter (curry (not o direct_sequent_eq) seq) seqs)
        end
      else
        let
          fun subsequents seqs zone =
            filter (fn (gamma, _) => subset atom_eq (gamma, zone @ proved)) seqs
          val zones = zones_of (length c) (map (descendants direct_graph) c)
          val subseqss = map (subsequents seqs) zones
          val seqs = fold (subtract direct_sequent_eq) subseqss seqs
          val cases =
            map2 (fn l => fn subseqs => ([l], redirect [l] proved subseqs))
                 c subseqss
        in s_cases cases @ redirect (succedent_of_cases cases) proved seqs end
  in redirect [] axioms seqs end

val chain_direct_proof =
  let
    fun chain_inf cl0 (seq as Have (cs, c)) =
        if member clause_eq cs cl0 then
          Hence (filter_out (curry clause_eq cl0) cs, c)
        else
          seq
      | chain_inf _ (Cases cases) = Cases (map chain_case cases)
    and chain_case (c, is) = (c, chain_proof (SOME c) is)
    and chain_proof _ [] = []
      | chain_proof (SOME prev) (i :: is) =
        chain_inf prev i :: chain_proof (SOME (succedent_of_inference i)) is
      | chain_proof _ (i :: is) =
        i :: chain_proof (SOME (succedent_of_inference i)) is
  in chain_proof NONE end

fun indent 0 = ""
  | indent n = "  " ^ indent (n - 1)

fun string_of_clause [] = "\<bottom>"
  | string_of_clause ls = space_implode " \<or> " (map Atom.string_of ls)

fun string_of_rich_sequent ch ([], c) = ch ^ " " ^ string_of_clause c
  | string_of_rich_sequent ch (cs, c) =
    commas (map string_of_clause cs) ^ " " ^ ch ^ " " ^ string_of_clause c

fun string_of_case depth (c, proof) =
  indent (depth + 1) ^ "[" ^ string_of_clause c ^ "]"
  |> not (null proof) ? suffix ("\n" ^ string_of_subproof (depth + 1) proof)

and string_of_inference depth (Have seq) =
    indent depth ^ string_of_rich_sequent "\<triangleright>" seq
  | string_of_inference depth (Hence seq) =
    indent depth ^ string_of_rich_sequent "\<guillemotright>" seq
  | string_of_inference depth (Cases cases) =
    indent depth ^ "[\n" ^
    space_implode ("\n" ^ indent depth ^ "|\n")
                  (map (string_of_case depth) cases) ^ "\n" ^
    indent depth ^ "]"

and string_of_subproof depth = cat_lines o map (string_of_inference depth)

val string_of_direct_proof = string_of_subproof 0

end;

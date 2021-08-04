(*  Title:      Pure/facts.ML
    Author:     Makarius

Environment of named facts, optionally indexed by proposition.
*)

signature FACTS =
sig
  val err_selection: string * Position.T -> int -> thm list -> 'a
  val err_single: string * Position.T -> thm list -> 'a
  val the_single: string * Position.T -> thm list -> thm
  datatype interval = FromTo of int * int | From of int | Single of int
  datatype ref =
    Named of (string * Position.T) * interval list option |
    Fact of string
  val named: string -> ref
  val ref_name: ref -> string
  val ref_pos: ref -> Position.T
  val map_ref_name: (string -> string) -> ref -> ref
  val string_of_selection: interval list option -> string
  val string_of_ref: ref -> string
  val select: ref -> thm list -> thm list
  val selections: string * thm list -> (ref * thm) list
  type T
  val empty: T
  val space_of: T -> Name_Space.T
  val alias: Name_Space.naming -> binding -> string -> T -> T
  val is_concealed: T -> string -> bool
  val check: Context.generic -> T -> xstring * Position.T -> string
  val intern: T -> xstring -> string
  val extern: Proof.context -> T -> string -> xstring
  val markup_extern: Proof.context -> T -> string -> Markup.T * xstring
  val defined: T -> string -> bool
  val is_dynamic: T -> string -> bool
  val lookup: Context.generic -> T -> string -> {dynamic: bool, thms: thm list} option
  val retrieve: Context.generic -> T -> xstring * Position.T ->
    {name: string, dynamic: bool, thms: thm list}
  val fold_static: (string * thm list -> 'a -> 'a) -> T -> 'a -> 'a
  val dest_static: bool -> T list -> T -> (string * thm list) list
  val dest_all: Context.generic -> bool -> T list -> T -> (string * thm list) list
  val props: T -> (thm * Position.T) list
  val could_unify: T -> term -> (thm * Position.T) list
  val merge: T * T -> T
  val add_static: Context.generic -> {strict: bool, index: bool} ->
    binding * thm list lazy -> T -> string * T
  val add_dynamic: Context.generic -> binding * (Context.generic -> thm list) -> T -> string * T
  val del: string -> T -> T
  val hide: bool -> string -> T -> T
end;

structure Facts: FACTS =
struct

(** fact references **)

fun length_msg (thms: thm list) pos =
  " (length " ^ string_of_int (length thms) ^ ")" ^ Position.here pos;

fun err_selection (name, pos) i thms =
  error ("Bad fact selection " ^ quote (name ^ enclose "(" ")" (string_of_int i)) ^
    length_msg thms pos);

fun err_single (name, pos) thms =
  error ("Expected singleton fact " ^ quote name ^ length_msg thms pos);

fun the_single _ [thm] = thm
  | the_single name_pos thms = err_single name_pos thms;


(* datatype interval *)

datatype interval =
  FromTo of int * int |
  From of int |
  Single of int;

fun string_of_interval (FromTo (i, j)) = string_of_int i ^ "-" ^ string_of_int j
  | string_of_interval (From i) = string_of_int i ^ "-"
  | string_of_interval (Single i) = string_of_int i;

fun interval n iv =
  let fun err () = raise Fail ("Bad interval specification " ^ string_of_interval iv) in
    (case iv of
      FromTo (i, j) => if i <= j then i upto j else err ()
    | From i => if i <= n then i upto n else err ()
    | Single i => [i])
  end;


(* datatype ref *)

datatype ref =
  Named of (string * Position.T) * interval list option |
  Fact of string;

fun named name = Named ((name, Position.none), NONE);

fun ref_name (Named ((name, _), _)) = name
  | ref_name (Fact _) = raise Fail "Illegal literal fact";

fun ref_pos (Named ((_, pos), _)) = pos
  | ref_pos (Fact _) = Position.none;

fun map_ref_name f (Named ((name, pos), is)) = Named ((f name, pos), is)
  | map_ref_name _ r = r;

fun string_of_selection NONE = ""
  | string_of_selection (SOME is) = enclose "(" ")" (commas (map string_of_interval is));

fun string_of_ref (Named ((name, _), sel)) = name ^ string_of_selection sel
  | string_of_ref (Fact _) = raise Fail "Illegal literal fact";


(* select *)

fun select (Fact _) ths = ths
  | select (Named (_, NONE)) ths = ths
  | select (Named ((name, pos), SOME ivs)) ths =
      let
        val n = length ths;
        fun err msg = error (msg ^ " for fact " ^ quote name ^ length_msg ths pos);
        fun sel i =
          if i > 0 andalso i <= n then nth ths (i - 1)
          else err_selection (name, pos) i ths;
        val is = maps (interval n) ivs handle Fail msg => err msg;
      in map sel is end;


(* selections *)

fun selections (name, [th]) = [(Named ((name, Position.none), NONE), th)]
  | selections (name, ths) = map2 (fn i => fn th =>
      (Named ((name, Position.none), SOME [Single i]), th)) (1 upto length ths) ths;



(** fact environment **)

(* datatypes *)

datatype fact = Static of thm list lazy | Dynamic of Context.generic -> thm list;

datatype T = Facts of
 {facts: fact Name_Space.table,
  props: (thm * Position.T) Net.net};

fun make_facts facts props = Facts {facts = facts, props = props};

val empty = make_facts (Name_Space.empty_table Markup.factN) Net.empty;


(* named facts *)

fun facts_of (Facts {facts, ...}) = facts;

val space_of = Name_Space.space_of_table o facts_of;

fun alias naming binding name (Facts {facts, props}) =
  make_facts (Name_Space.alias_table naming binding name facts) props;

val is_concealed = Name_Space.is_concealed o space_of;

fun check context facts (xname, pos) =
  let
    val (name, fact) = Name_Space.check context (facts_of facts) (xname, pos);
    val _ =
      (case fact of
        Static _ => ()
      | Dynamic _ => Context_Position.report_generic context pos (Markup.dynamic_fact name));
  in name end;

val intern = Name_Space.intern o space_of;
fun extern ctxt = Name_Space.extern ctxt o space_of;
fun markup_extern ctxt = Name_Space.markup_extern ctxt o space_of;


(* retrieve *)

val defined = Name_Space.defined o facts_of;

fun is_dynamic facts name =
  (case Name_Space.lookup (facts_of facts) name of
    SOME (Dynamic _) => true
  | _ => false);

fun lookup context facts name =
  (case Name_Space.lookup (facts_of facts) name of
    NONE => NONE
  | SOME (Static ths) => SOME {dynamic = false, thms = Lazy.force ths}
  | SOME (Dynamic f) => SOME {dynamic = true, thms = f context});

fun retrieve context facts (xname, pos) =
  let
    val name = check context facts (xname, pos);
    val {dynamic, thms} =
      (case lookup context facts name of
        SOME res =>
          (if #dynamic res
           then Context_Position.report_generic context pos (Markup.dynamic_fact name)
           else ();
           res)
      | NONE => error ("Unknown fact " ^ quote name ^ Position.here pos));
  in
   {name = name,
    dynamic = dynamic,
    thms = map (Thm.transfer'' context) thms}
  end;


(* content *)

local

fun fold_static_lazy f =
  Name_Space.fold_table (fn (a, Static ths) => f (a, ths) | _ => I) o facts_of;

fun consolidate facts =
  let
    val unfinished =
      (facts, []) |-> fold_static_lazy (fn (_, ths) => if Lazy.is_finished ths then I else cons ths);
    val _ = Lazy.consolidate unfinished;
  in facts end;

fun included verbose prev_facts facts name =
  not (exists (fn prev => defined prev name) prev_facts orelse
    not verbose andalso is_concealed facts name);

in

fun fold_static f facts =
  fold_static_lazy (f o apsnd Lazy.force) (consolidate facts);

fun dest_static verbose prev_facts facts =
  fold_static (fn (a, ths) => included verbose prev_facts facts a ? cons (a, ths)) facts []
  |> sort_by #1;

fun dest_all context verbose prev_facts facts =
  (facts_of (consolidate facts), [])
  |-> Name_Space.fold_table (fn (a, fact) =>
    let val ths = (case fact of Static ths => Lazy.force ths | Dynamic f => f context)
    in included verbose prev_facts facts a ? cons (a, ths) end)
  |> sort_by #1;

end;


(* indexed props *)

val prop_ord = Term_Ord.term_ord o apply2 (Thm.full_prop_of o fst);

fun props (Facts {props, ...}) = sort_distinct prop_ord (Net.content props);
fun could_unify (Facts {props, ...}) = Net.unify_term props;


(* merge facts *)

fun merge (Facts {facts = facts1, props = props1}, Facts {facts = facts2, props = props2}) =
  let
    val facts' = Name_Space.merge_tables (facts1, facts2);
    val props' =
      if Net.is_empty props2 then props1
      else if Net.is_empty props1 then props2
      else Net.merge (is_equal o prop_ord) (props1, props2);  (*beware of non-canonical merge*)
  in make_facts facts' props' end;


(* add entries *)

fun add_prop pos th =
  Net.insert_term (K false) (Thm.full_prop_of th, (th, pos));

fun add_static context {strict, index} (b, ths) (Facts {facts, props}) =
  let
    val ths' = ths
      |> index ? Lazy.force_value
      |> Lazy.map_finished (map Thm.trim_context);
    val (name, facts') =
      if Binding.is_empty b then ("", facts)
      else Name_Space.define context strict (b, Static ths') facts;
    val props' =
      if index then
        props |> fold (add_prop (Binding.pos_of (Binding.default_pos b))) (Lazy.force ths')
      else props;
  in (name, make_facts facts' props') end;

fun add_dynamic context (b, f) (Facts {facts, props}) =
  let val (name, facts') = Name_Space.define context true (b, Dynamic f) facts;
  in (name, make_facts facts' props) end;


(* remove entries *)

fun del name (Facts {facts, props}) =
  make_facts (Name_Space.del_table name facts) props;

fun hide fully name (Facts {facts, props}) =
  make_facts (Name_Space.hide_table fully name facts) props;

end;

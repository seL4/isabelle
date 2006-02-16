signature IMPORT_RECORDER =
sig

    datatype deltastate = Consts of (string * typ * mixfix) list
			| Specification of (string * string * bool) list * term
			| Hol_mapping of string * string * string
			| Hol_pending of string * string * term
			| Hol_const_mapping of string * string * string
			| Hol_move of string * string
			| Defs of string * term
			| Hol_theorem of string * string * term
			| Typedef of string option * (string * string list * mixfix) * term * (string * string) option * term 
			| Hol_type_mapping of string * string * string
			| Indexed_theorem of int * term
	                | Protect_varname of string * string

    datatype history = History of history_entry list
	 and history_entry = ThmEntry of string*string*bool*history | DeltaEntry of deltastate list

    val get_history : unit -> history
    val set_history : history -> unit
    val clear_history : unit -> unit
				      
    val start_replay_proof : string -> string -> unit
    val stop_replay_proof : string -> string -> unit
    val abort_replay_proof : string -> string -> unit

    val add_consts : (string * typ * mixfix) list -> unit
    val add_specification : (string * string * bool) list -> thm -> unit
    val add_hol_mapping : string -> string -> string -> unit
    val add_hol_pending : string -> string -> thm -> unit
    val add_hol_const_mapping : string -> string -> string -> unit
    val add_hol_move : string -> string -> unit
    val add_defs : string -> term -> unit
    val add_hol_theorem : string -> string -> thm -> unit
    val add_typedef :  string option -> string * string list * mixfix -> term -> (string * string) option -> thm -> unit
    val add_hol_type_mapping : string -> string -> string -> unit
    val add_indexed_theorem : int -> thm -> unit
    val protect_varname : string -> string -> unit

    val set_skip_import_dir : string option -> unit
    val get_skip_import_dir : unit -> string option

    val set_skip_import : bool -> unit
    val get_skip_import : unit -> bool

    val save_history : string -> unit
    val load_history : string -> unit
end

structure ImportRecorder :> IMPORT_RECORDER  =
struct

datatype deltastate = Consts of (string * typ * mixfix) list
		    | Specification of (string * string * bool) list * term
		    | Hol_mapping of string * string * string
		    | Hol_pending of string * string * term
		    | Hol_const_mapping of string * string * string
		    | Hol_move of string * string
		    | Defs of string * term
		    | Hol_theorem of string * string * term
		    | Typedef of string option * (string * string list * mixfix) * term * (string * string) option * term 
		    | Hol_type_mapping of string * string * string
		    | Indexed_theorem of int * term
	            | Protect_varname of string * string

datatype history_entry = StartReplay of string*string  
		       | StopReplay of string*string
		       | AbortReplay of string*string
		       | Delta of deltastate list

val history = ref ([]:history_entry list)
val history_dir = ref (SOME "")
val skip_imports = ref false

fun set_skip_import b = skip_imports := b
fun get_skip_import () = !skip_imports

fun clear_history () = history := []

fun add_delta d = history := (case !history of (Delta ds)::hs => (Delta (d::ds))::hs | hs => (Delta [d])::hs)
fun add_replay r = history := (r :: (!history))

local 
    open XMLConvOutput
    val consts = list (triple string typ mixfix)
    val specification = pair (list (triple string string bool)) term
    val hol_mapping = triple string string string
    val hol_pending = triple string string term
    val hol_const_mapping = triple string string string
    val hol_move = pair string string
    val defs = pair string term
    val hol_theorem = triple string string term
    val typedef = quintuple (option string) (triple string (list string) mixfix) term (option (pair string string)) term
    val hol_type_mapping = triple string string string
    val indexed_theorem = pair int term
    val entry = pair string string

    fun delta (Consts args) = wrap "consts" consts args
      | delta (Specification args) = wrap "specification" specification args
      | delta (Hol_mapping args) = wrap "hol_mapping" hol_mapping args
      | delta (Hol_pending args) = wrap "hol_pending" hol_pending args
      | delta (Hol_const_mapping args) = wrap "hol_const_mapping" hol_const_mapping args
      | delta (Hol_move args) = wrap "hol_move" hol_move args
      | delta (Defs args) = wrap "defs" defs args
      | delta (Hol_theorem args) = wrap "hol_theorem" hol_theorem args
      | delta (Typedef args) = wrap "typedef" typedef args
      | delta (Hol_type_mapping args) = wrap "hol_type_mapping" hol_type_mapping args
      | delta (Indexed_theorem args) = wrap "indexed_theorem" indexed_theorem args
      | delta (Protect_varname args) = wrap "protect_varname" entry args

    fun history_entry (StartReplay args) = wrap "startreplay" entry args
      | history_entry (StopReplay args) = wrap "stopreplay" entry args
      | history_entry (AbortReplay args) = wrap "abortreplay" entry args
      | history_entry (Delta args) = wrap "delta" (list delta) args
in

val xml_of_history = list history_entry

end

local 
    open XMLConvInput
    val consts = list (triple string typ mixfix)
    val specification = pair (list (triple string string bool)) term
    val hol_mapping = triple string string string
    val hol_pending = triple string string term
    val hol_const_mapping = triple string string string
    val hol_move = pair string string
    val defs = pair string term
    val hol_theorem = triple string string term
    val typedef = quintuple (option string) (triple string (list string) mixfix) term (option (pair string string)) term
    val hol_type_mapping = triple string string string
    val indexed_theorem = pair int term
    val entry = pair string string

    fun delta "consts" = unwrap Consts consts
      | delta "specification" = unwrap Specification specification 
      | delta "hol_mapping" = unwrap Hol_mapping hol_mapping 
      | delta "hol_pending" = unwrap Hol_pending hol_pending
      | delta "hol_const_mapping" = unwrap Hol_const_mapping hol_const_mapping
      | delta "hol_move" = unwrap Hol_move hol_move
      | delta "defs" = unwrap Defs defs
      | delta "hol_theorem" = unwrap Hol_theorem hol_theorem
      | delta "typedef" = unwrap Typedef typedef
      | delta "hol_type_mapping" = unwrap Hol_type_mapping hol_type_mapping
      | delta "indexed_theorem" = unwrap Indexed_theorem indexed_theorem
      | delta "protect_varname" = unwrap Protect_varname entry
      | delta _ = raise ParseException "delta"

    val delta = fn e => delta (name_of_wrap e) e

    fun history_entry "startreplay" = unwrap StartReplay entry 
      | history_entry "stopreplay" = unwrap StopReplay entry
      | history_entry "abortreplay" = unwrap AbortReplay entry
      | history_entry "delta" = unwrap Delta (list delta)
      | history_entry _ = raise ParseException "history_entry"

    val history_entry = fn e => history_entry (name_of_wrap e) e
in

val history_of_xml = list history_entry

end

fun start_replay_proof thyname thmname = add_replay (StartReplay (thyname, thmname))
fun stop_replay_proof thyname thmname = add_replay (StopReplay (thyname, thmname))
fun abort_replay_proof thyname thmname = add_replay (AbortReplay (thyname, thmname))
fun add_hol_theorem thyname thmname thm = add_delta (Hol_theorem (thyname, thmname, prop_of thm))
fun add_hol_mapping thyname thmname isaname = add_delta (Hol_mapping (thyname, thmname, isaname))
fun add_consts consts = add_delta (Consts consts)
fun add_typedef thmname_opt typ c absrep_opt th = add_delta (Typedef (thmname_opt, typ, c, absrep_opt, prop_of th))
fun add_defs thmname eq = add_delta (Defs (thmname, eq)) 
fun add_hol_const_mapping thyname constname fullcname = add_delta (Hol_const_mapping (thyname, constname, fullcname))
fun add_hol_move fullname moved_thmname = add_delta (Hol_move (fullname, moved_thmname))
fun add_hol_type_mapping thyname tycname fulltyname = add_delta (Hol_type_mapping (thyname, tycname, fulltyname))
fun add_hol_pending thyname thmname th = add_delta (Hol_pending (thyname, thmname, prop_of th))
fun add_specification names th = add_delta (Specification (names, prop_of th)) 
fun add_indexed_theorem i th = add_delta (Indexed_theorem (i, prop_of th))
fun protect_varname s t = add_delta (Protect_varname (s,t))
			    
fun set_skip_import_dir dir = (history_dir := dir)
fun get_skip_import_dir () = !history_dir

fun get_filename thyname = Path.pack (Path.append (Path.unpack (the (get_skip_import_dir ()))) (Path.unpack (thyname^".history")))

fun save_history thyname = 
    if get_skip_import () then
	XMLConv.write_to_file xml_of_history (get_filename thyname) (!history)
    else 
	()

fun load_history thyname = 
    if get_skip_import () then
	let 
	    val filename = get_filename thyname
	    val _ = writeln "load_history / before"
	    val _ = 
		if File.exists (Path.unpack filename) then					
		    (history := XMLConv.read_from_file history_of_xml (get_filename thyname)) 
		else
		    clear_history ()
	    val _ = writeln "load_history / after"
	in
	    ()
	end
    else
	()
    
 
datatype history = History of history_entry list
     and history_entry = ThmEntry of string*string*bool*history | DeltaEntry of deltastate list

exception CONV 

fun conv_histories ((StartReplay (thyname, thmname))::rest) = 
    let
	val (hs, rest) = conv_histories rest
	fun continue thyname' thmname' aborted rest = 
	    if thyname = thyname' andalso thmname = thmname' then
		let
		    val (hs', rest) = conv_histories rest
		in
		    ((ThmEntry (thyname, thmname, aborted, History hs))::hs', rest)
		end
	    else
		raise CONV 
    in
	case rest of 
	    (StopReplay (thyname',thmname'))::rest =>
	    continue thyname' thmname' false rest
	  | (AbortReplay (thyname',thmname'))::rest =>
	    continue thyname' thmname' true rest
	  | [] => (hs, [])
	  | _ => raise CONV
    end
  | conv_histories ((Delta ds)::rest) = (conv_histories rest) |>> (fn hs => (DeltaEntry (rev ds))::hs)  
  | conv_histories rest = ([], rest)

fun conv es = 
    let
	val (h, rest) = conv_histories (rev es)
    in
	case rest of
	    [] => h
	  | _ => raise CONV
    end 

fun get_history () = History (conv (!history))

fun reconv (History hs) rs = fold reconv_entry hs rs
and reconv_entry (ThmEntry (thyname, thmname, aborted, h)) rs =
    ((if aborted then AbortReplay else StopReplay) (thyname, thmname)) :: (reconv h ((StartReplay (thyname, thmname))::rs))
  | reconv_entry (DeltaEntry ds) rs = (Delta (rev ds))::rs
    
fun set_history h = history := reconv h []


end

let output_int oc i = output_string oc (string_of_int i);;
let string_list_of_string str sep =
  let rec slos_aux str ans =
    if str = "" then ans else
    try
      let first_space = String.index str sep in
      if first_space = 0 then
        slos_aux (String.sub str 1 (String.length str - 1)) ans
      else
        slos_aux
          (String.sub str (first_space + 1)(String.length str - 1 - first_space))
          ((String.sub str 0 (first_space)) :: ans)
    with
      Not_found ->
        List.rev (str :: ans)
  in slos_aux str []
;;

module SM = Map.Make(struct type t = string let compare = compare end);;
module IM = Map.Make(struct type t = int let compare = compare end);;
let facts = ref SM.empty;;
let maps = ref IM.empty;;
let facts_rev = ref IM.empty;;

let rec addfact s n =
  if SM.mem s (!facts) then failwith ("addfact:" ^ s) else
  if IM.mem n (!facts_rev) then () else (
  facts := SM.add s n (!facts);
  facts_rev := IM.add n s (!facts_rev));;

let read_facts () =
  let inc = open_in "facts.lst" in
  (try
    while true do
      let l = (string_list_of_string (input_line inc) ' ') in
      let no = int_of_string (List.nth l 1) in
      addfact (List.hd l) no
    done
  with End_of_file -> close_in inc);
  (let inc = open_in "maps.lst" in
  try
    while true do
      let (hl_name :: t) = (string_list_of_string (input_line inc) ' ') in
      let no = try SM.find hl_name (!facts) with Not_found -> failwith ("read facts: " ^ hl_name) in
      facts := SM.remove hl_name (!facts);
      let isa_name = if t = [] then "" else List.hd t in
      maps := IM.add no isa_name (!maps);
    done
  with End_of_file -> close_in inc);;

let tyno = ref 0;;
let tmno = ref 0;;
let thno = ref 0;;
let ios s = abs(int_of_string s);;

let process thth thtm tmtm thty tmty tyty = function
  ('R', [t]) -> incr thno; thtm (ios t)
| ('B', [t]) -> incr thno; thtm (ios t)
| ('T', [p; q]) -> incr thno; thth (ios p); thth (ios q)
| ('C', [p; q]) -> incr thno; thth (ios p); thth (ios q)
| ('L', [t; p]) -> incr thno; thth (ios p); thtm (ios t)
| ('H', [t]) -> incr thno; thtm (ios t)
| ('E', [p; q]) -> incr thno; thth (ios p); thth (ios q)
| ('D', [p; q]) -> incr thno; thth (ios p); thth (ios q)
| ('Q', ((h :: t) as l)) -> incr thno; thth (ios (List.hd (List.rev l)));
    List.iter thty (List.map ios (List.tl (List.rev l)))
| ('S', ((h :: t) as l)) -> incr thno; thth (ios (List.hd (List.rev l)));
    List.iter thtm (List.map ios (List.tl (List.rev l)))
| ('A', [_; t]) -> incr thno; thtm (ios t)
| ('F', [_; t]) -> incr thno; thtm (ios t)
| ('Y', [_; _; _; t; s; p]) -> incr thno; thth (ios p); thtm (ios t); thtm (ios s)
| ('1', [p]) -> incr thno; thth (ios p)
| ('2', [p]) -> incr thno; thth (ios p)
| ('t', [_]) -> incr tyno
| ('a', (h :: t)) -> incr tyno; List.iter tyty (List.map ios t)
| ('v', [_; ty]) -> incr tmno; tmty (ios ty)
| ('c', [_; ty]) -> incr tmno; tmty (ios ty)
| ('f', [t; s]) -> incr tmno; tmtm (ios t); tmtm (ios s)
| ('l', [t; s]) -> incr tmno; tmtm (ios t); tmtm (ios s)
| (c, l) -> failwith ((String.make 1 c) ^ (String.concat " " l))
;;

let thth = Array.make 155097624 [];;
let tmth = Array.make 55000000 [];;
let tmtm = Array.make 55000000 [];;
let tyth = Array.make 200000 [];;
let tytm = Array.make 200000 [];;
let tyty = Array.make 200000 [];;

let needth no = not (IM.mem no !maps);;

let addthth s = if needth !thno then thth.(s) <- !thno :: thth.(s);;
let addtmth s = if needth !thno then tmth.(s) <- !thno :: tmth.(s);;
let addtyth s = if needth !thno then tyth.(s) <- !thno :: tyth.(s);;
let addtmtm s = tmtm.(s) <- !tmno :: tmtm.(s);;
let addtytm s = tytm.(s) <- !tmno :: tytm.(s);;
let addtyty s = tyty.(s) <- !tyno :: tyty.(s);;

let add_facts_deps () =
  thth.(0) <- 0 :: thth.(0);
  SM.iter (fun _ n -> thth.(n) <- 0 :: thth.(n)) !facts
;;

let process_all thth thtm tmtm thty tmty tyty =
  tyno := 0; tmno := 0; thno := 0;
  let inc = open_in "proofs" in
  try while true do
      let c = input_char inc in
      let s = input_line inc in
      process thth thtm tmtm thty tmty tyty (c, (string_list_of_string s ' '))
    done
  with End_of_file -> close_in inc;;

let count_nonnil l =
  Array.fold_left (fun n l -> if l = [] then n else n + 1) 0 l;;

let clean tab filter =
  for i = Array.length tab - 1 downto 1 do
    tab.(i) <- List.filter filter tab.(i)
  done;;

let clean_all () =
  clean thth (fun j -> not (thth.(j) = []));
  clean tmth (fun j -> not (thth.(j) = []));
  clean tmtm (fun j -> not (tmth.(j) = [] && tmtm.(j) = []));
  clean tyth (fun j -> not (thth.(j) = []));
  clean tytm (fun j -> not (tmth.(j) = [] && tmtm.(j) = []));
  clean tyty (fun j -> not (tyth.(j) = [] && tytm.(j) = [] && tyty.(j) = []))
;;

read_facts ();;
let facts_rev = !facts_rev;;
add_facts_deps ();;
process_all addthth addtmth addtmtm addtyth addtytm addtyty;;

print_string "thms: "; print_int !thno;
print_string " tms: "; print_int !tmno;
print_string " tys: "; print_int !tyno; print_newline (); flush stdout;;
print_string "Direct uses: th->th th->tm tm->tm th->ty tm->ty ty->ty: \n";
print_int (count_nonnil thth); print_char ' ';
print_int (count_nonnil tmth); print_char ' ';
print_int (count_nonnil tmtm); print_char ' ';
print_int (count_nonnil tyth); print_char ' ';
print_int (count_nonnil tytm); print_char ' ';
print_int (count_nonnil tyty); print_newline (); flush stdout;;
clean_all ();;

print_string "After removing:\n";
print_string "Depends: th->th th->tm tm->tm th->ty tm->ty ty->ty: \n";
print_int (count_nonnil thth); print_char ' ';
print_int (count_nonnil tmth); print_char ' ';
print_int (count_nonnil tmtm); print_char ' ';
print_int (count_nonnil tyth); print_char ' ';
print_int (count_nonnil tytm); print_char ' ';
print_int (count_nonnil tyty); print_newline (); flush stdout;;

let rev_tables () =
  let rev_tab t =
    for i = 0 to Array.length t - 1 do
      t.(i) <- List.rev (t.(i));
    done
  in
  rev_tab thth; rev_tab tmth; rev_tab tyth;
  rev_tab tmtm; rev_tab tytm; rev_tab tyty
;;
print_char 'c'; flush stdout;;
rev_tables ();;
print_char 'C'; flush stdout;;

let othnth = Array.make 155300000 0;;
let otmntm = Array.make 55000000 0;;
let otynty = Array.make 200000 0;;

let outl oc tag ss is =
  let ss = ss @ (List.map string_of_int is) in
  output_char oc tag; output_string oc (String.concat " " ss); output_char oc '\n'
;;
let ntyno = ref 0;; let ntmno = ref 0;; let nthno = ref 0;;
let ty t i = (*!ntyno -*)
  t.(i) <- List.tl t.(i);
  if tyth.(i) = [] && tytm.(i) = [] && tyty.(i) = [] then (- otynty.(i)) else otynty.(i);;
let tm t i = (*!ntmno -*)
  t.(i) <- List.tl t.(i);
  if tmth.(i) = [] && tmtm.(i) = [] then (- otmntm.(i)) else otmntm.(i);;
let th i = (*!nthno -*)
(*  (if List.hd thth.(i) = 0 then (print_int !thno));*)
  thth.(i) <- List.tl thth.(i);
  if thth.(i) = [] then (- othnth.(i)) else othnth.(i);;

let rec itlist f l b =
  match l with
    [] -> b
  | (h::t) -> f h (itlist f t b);;

let insert x l =
  if List.mem x l then l else x::l;;

let union l1 l2 = itlist insert l1 l2;;

let rec neededby l acc =
  match l with [] -> acc
  | h :: t ->
      try if List.length acc > 10 then acc else
        neededby t (insert (IM.find h facts_rev) acc)
      with Not_found -> neededby (union thth.(h) t) acc
;;
let neededby l = String.concat " " (neededby l [])

let outt oc tag ss tys tms ths =
  if thth.(!thno) = [] then () else
  begin
    incr nthno;
    othnth.(!thno) <- !nthno;
    begin
      try
        let s = IM.find (!thno) (!maps) in
        if s = "-" then failwith ("removed thm:" ^ IM.find !thno facts_rev ^ " around:" ^ neededby (thth.(!thno)))
        else if s = "" then outl oc tag ss []
        else outl oc 'M' [s] []
      with Not_found ->
        outl oc tag ss
          (List.map (fun i -> ty tyth (ios i)) tys @ List.map
          (fun i -> tm tmth (ios i)) tms @ List.map (fun i -> th (ios i)) ths)
    end;
    try outl oc '+' [IM.find (!thno) facts_rev] []
    with Not_found -> ()
  end
;;

let outtm oc tag ss tys tms =
  if tmth.(!tmno) = [] && tmtm.(!tmno) = [] then () else
  (incr ntmno; otmntm.(!tmno) <- !ntmno; outl oc tag ss (List.map (fun i -> ty tytm (ios i)) tys @ List.map (fun i -> tm tmtm (ios i)) tms))
;;

let outty oc tag ss tys =
  if tyth.(!tyno) = [] && tytm.(!tyno) = [] && tyty.(!tyno) = [] then () else
  (incr ntyno; otynty.(!tyno) <- !ntyno; outl oc tag ss (List.map (fun i -> ty tyty (ios i)) tys))
;;

let printer oc = function
  ('R', [t]) -> incr thno; outt oc 'R' [] [] [t] []
| ('B', [t]) -> incr thno; outt oc 'B' [] [] [t] []
| ('T', [p; q]) -> incr thno; outt oc 'T' [] [] [] [p; q]
| ('C', [p; q]) -> incr thno; outt oc 'C' [] [] [] [p; q]
| ('L', [t; p]) -> incr thno; outt oc 'L' [] [] [t] [p]
| ('H', [t]) -> incr thno; outt oc 'H' [] [] [t] []
| ('E', [p; q]) -> incr thno; outt oc 'E' [] [] [] [p; q]
| ('D', [p; q]) -> incr thno; outt oc 'D' [] [] [] [p; q]
| ('Q', ((h :: t) as l)) -> incr thno;
    let (th, tys) = (List.hd (List.rev l), List.rev (List.tl (List.rev l))) in
    outt oc 'Q' [] tys [] [th]
| ('S', ((h :: t) as l)) -> incr thno;
    let (th, tms) = (List.hd (List.rev l), List.rev (List.tl (List.rev l))) in
    outt oc 'S' [] [] tms [th]
| ('A', [n; t]) -> incr thno; outt oc 'A' [n] [] [t] []
| ('F', [n; t]) -> incr thno; outt oc 'F' [n] [] [t] []
| ('Y', [n1; n2; n3; t; s; p]) -> incr thno; outt oc 'Y' [n1; n2; n3] [] [t; s] [p]
| ('1', [p]) -> incr thno; outt oc '1' [] [] [] [p]
| ('2', [p]) -> incr thno; outt oc '2' [] [] [] [p]
| ('t', [n]) -> incr tyno; outty oc 't' [n] []
| ('a', (h :: t)) -> incr tyno; outty oc 'a' [h] t
| ('v', [n; ty]) -> incr tmno; outtm oc 'v' [n] [ty] []
| ('c', [n; ty]) -> incr tmno; outtm oc 'c' [n] [ty] []
| ('f', [t; s]) -> incr tmno; outtm oc 'f' [] [] [t; s]
| ('l', [t; s]) -> incr tmno; outtm oc 'l' [] [] [t; s]
| (c, l) -> failwith ((String.make 1 c) ^ (String.concat " " l))
;;

let print_all () =
  tyno := 0; tmno := 0; thno := 0;
  let inc = open_in "proofs" in
  let oc = open_out "proofsN" in
  try while true do
      let c = input_char inc in
      let s = input_line inc in
      printer oc (c, string_list_of_string s ' ')
    done
  with End_of_file -> (close_in inc; close_out oc);;

print_all ();;

print_string "thms: "; print_int !nthno;
print_string " tms: "; print_int !ntmno;
print_string " tys: "; print_int !ntyno; print_newline (); flush stdout;;

let inc = open_in "facts.lst" in
let oc = open_out "facts.lstN" in
try
  while true do
    let [name; no] = string_list_of_string (input_line inc) ' ' in
    let no = int_of_string no in
    try if IM.find no facts_rev = name then (
    output_string oc name; output_char oc ' ';
    output_int oc othnth.(no); output_char oc '\n'
    ) else ()
    with Not_found -> ()
  done
  with End_of_file -> (close_in inc; close_out oc);;

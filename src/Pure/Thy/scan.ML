(*  Title: 	Pure/Thy/scan
    ID:         $Id$
    Author: 	Sonia Mahjoub / Tobias Nipkow
    Copyright   1992  TU Muenchen

The scanner. Adapted from Larry Paulson's ML for the Working Programmer.
*)

signature LEXICAL =
sig


datatype token = Id  of string 
               | Key of string
               | Nat of string
               | Stg of string
               | Txt of string

val scan : string list -> (token * int) list
end;

signature KEYWORD = 
sig
val alphas  : string list
val symbols : string list
end;


functor LexicalFUN (Keyword: KEYWORD): LEXICAL = 

struct



datatype token = Id  of string 
               | Key of string
               | Nat of string
               | Stg of string
               | Txt of string;


fun lexerr(n,s) =
    error("Lexical error on line " ^ (string_of_int n) ^ ": " ^ s);

val specials = explode"!{}@#$%^&*()+-=[]:\";',./?`_~<>|\\";

fun is_symbol c = "_" = c orelse "'" = c;

fun alphanum (id, c::cs) =
       if is_letter c orelse is_digit c orelse is_symbol c
       then alphanum (id ^ c , cs)
       else (id , c :: cs)
  | alphanum (id ,[]) = (id ,[]);

fun numeric (nat, c::cs) =
      if is_digit c 
      then numeric (nat^c, cs)
      else (nat, c::cs)
  | numeric (nat, []) = (nat,[]);
 
fun tokenof (a, n) =
      if a mem Keyword.alphas
      then (Key a, n) 
      else (Id a, n);

fun symbolic (sy, c::cs) =
       if (sy mem Keyword.symbols) andalso 
          not((sy^c) mem Keyword.symbols) 
          orelse not (c mem specials)
       then (sy, c::cs)
       else symbolic(sy^c, cs)
  | symbolic (sy, []) = (sy, []);


fun stringerr(n) = lexerr(n, "No matching quote found on this line");

fun is_control_chr ([],_,n) = stringerr(n)
  | is_control_chr (c::cs,s,n) = 
          let val m = ord c
          in if (m >= 64 andalso m <= 95)
             then (cs, s^c, n)
             else stringerr(n)
          end;

fun is_3_dgt (c1::c2::cs, c,n) = 
          let val s = c^c1^c2
          in  if (s >= "000" andalso s <= "255")
              then (cs, s)
              else stringerr(n)
          end 
  | is_3_dgt (_,_,n) = stringerr(n); 

fun is_imprt_seq ([],_,n) = stringerr(n)
  | is_imprt_seq ((c::cs),s,n) = 
          if c = "\\" then (cs,s^"\\",n)
          else if c = "\n"
               then is_imprt_seq (cs,s^"\n",n+1)
          else if (c = "\t") orelse (c = " ")
               then is_imprt_seq (cs,s^c,n)
          else stringerr(n);

fun is_escape_seq ([],_,n) = stringerr(n)
  | is_escape_seq ((c::cs),s,n) =  
          if c = "\\" then (cs,s^"\\",n)
          else if c = "\n" 
               then is_imprt_seq (cs,s^"\n",n+1) 
          else if (c = "\t") orelse (c = " ")
               then is_imprt_seq (cs,s^c,n)
          else if c = "^" 
               then is_control_chr (cs,s^"^",n)
          else if ("0" <= c andalso c <= "2") 
               then let val (cs',s') = 
                            is_3_dgt(cs,c,n)
                    in (cs',s^s',n)
                    end
          else stringerr(n);


fun string (_,[],_,n) = stringerr(n)
  | string (toks, c::cs, s, n) =
       if c  = "\"" then ((Stg s, n)::toks , cs, n)
       else if c = "\\" 
            then  let val (cs',s',n') = 
                          is_escape_seq (cs, s^"\\",n) 
                  in string (toks,cs',s',n') end 
       else string (toks,cs,s^c,n);


fun comment ((c1::c2::cs), n) =
      if c1 = "*" andalso c2 = ")" then (cs,n) else
      if c1 = "\n" then comment((c2::cs), n+1)
      else comment((c2::cs), n)
  | comment (_, n) = lexerr(n, "Missing end of comment");

fun scanning (toks , [], n) = rev toks
  | scanning (toks , c :: cs, n) = 
       if is_letter c 
       then let val (id , cs2) = alphanum (c , cs)
            in if id = "ML"
               then let val text = implode cs2
                    in  scanning ((Txt text,n) :: toks , [], n)
                    end
               else scanning (tokenof(id,n) :: toks , cs2, n) 
            end
       else if is_digit c 
            then let val (nat , cs2) = numeric(c , cs)
                 in scanning ((Nat nat,n) :: toks , cs2, n) end
       else if c mem specials
            then if c = "\""
                 then let val (toks', cs', n') = string (toks, cs, "", n)
                      in scanning (toks', cs', n') end
                 else let val (sy , cs2) = symbolic (c , cs)
                      in if sy = "(*"
                         then let val (cs3,n2) = comment(cs2,n)
                              in scanning (toks , cs3, n2) end
                         else scanning ((Key sy,n) :: toks, cs2, n)
                      end
       else if c = "\n" then scanning (toks, cs, n+1)
       else if c = " " orelse c = "\t" then scanning (toks , cs, n)
       else lexerr(n,"Illegal character " ^ c);

fun scan a = scanning ([] , a, 1);

end;

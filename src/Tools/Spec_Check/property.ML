(*  Title:      Tools/Spec_Check/property.ML
    Author:     Lukas Bulwahn and Nicolai Schaffroth, TU Muenchen
    Author:     Christopher League

Conditional properties that can track argument distribution.
*)

signature PROPERTY =
sig

type 'a pred = 'a -> bool
type 'a prop
val pred : 'a pred -> 'a prop
val pred2 : ('a * 'b) pred -> 'b -> 'a  prop
val implies : 'a pred * 'a prop -> 'a prop
val ==> : 'a pred * 'a pred -> 'a prop
val trivial : 'a pred -> 'a prop -> 'a prop
val classify : 'a pred -> string -> 'a prop -> 'a prop
val classify' : ('a -> string option) -> 'a prop -> 'a prop

(*Results*)
type result = bool option
type stats = { tags : (string * int) list, count : int }
val test : 'a prop -> 'a * stats -> result * stats
val stats : stats
val success : result pred
val failure : result pred

end

structure Property : PROPERTY =
struct

type result = bool option
type stats = { tags : (string * int) list, count : int }
type 'a pred = 'a -> bool
type 'a prop = 'a * stats -> result * stats

fun success (SOME true) = true
  | success _ = false

fun failure (SOME false) = true
  | failure _ = false

fun apply f x = (case try f x of NONE => SOME false | some => some)
fun pred f (x,s) = (apply f x, s)
fun pred2 f z = pred (fn x => f (x, z))

fun implies (cond, p) (x,s) = if cond x then p (x, s) else (NONE, s)

fun ==> (p1, p2) = implies (p1, pred p2)

fun wrap trans p (x,s) =
  let val (result,s) = p (x,s)
  in (result, trans (x, result, s)) end

fun classify' f =
  wrap (fn (x, result, {tags, count}) =>
    { tags =
        if is_some result then
          (case f x of
            NONE => tags
          | SOME tag => AList.map_default (op =) (tag, 0) (fn c => c + 1) tags)
        else tags,
     count = count })

fun classify p tag = classify' (fn x => if p x then SOME tag else NONE)

fun trivial cond = classify cond "trivial"

fun test p =
  wrap (fn (_, result, {tags, count}) =>
    { tags = tags, count = if is_some result then count + 1 else count }) p

val stats = { tags = [], count = 0 }

end

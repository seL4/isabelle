(* type inference *)

Type = Func +

types ty

arities ty :: term

consts  bool	:: ty
	nat	:: ty
	"->"	:: ty => ty => ty	(infixr 20)
	typeof	:: [tm, ty] => bool
        anyterm :: tm

rules	common_typeof	"
typeof (app M N) B       :- typeof M (A -> B) & typeof N A..

typeof (cond C L R) A :- typeof C bool & typeof L A & typeof R A..
typeof (fix F)   A       :- (!x. typeof x A => typeof (F  x) A)..

typeof true  bool..
typeof false bool..
typeof (M and N) bool :- typeof M bool & typeof N bool..

typeof (M eq  N) bool :- typeof M T    & typeof N T   ..

typeof  Z    nat..
typeof (S N) nat :- typeof N nat..
typeof (M + N) nat :- typeof M nat & typeof N nat..
typeof (M - N) nat :- typeof M nat & typeof N nat..
typeof (M * N) nat :- typeof M nat & typeof N nat"

rules	good_typeof	"
typeof (abs Bo) (A -> B) :- (!x. typeof x A => typeof (Bo x) B)"

rules	bad1_typeof	"
typeof (abs Bo) (A -> B) :- (typeof varterm A => typeof (Bo varterm) B)"

rules	bad2_typeof	"
typeof (abs Bo) (A -> B) :- (typeof anyterm A => typeof (Bo anyterm) B)"

end

Traces = UNITY +

consts traces :: "['a set, ('a * 'a)set set] => 'a list set"

inductive "traces Init Acts"
  intrs 
         (*Initial trace is empty*)
    Init  "s: Init ==> [s] : traces Init Acts"

    Acts  "[| act: Acts;  s#evs : traces Init Acts;  (s,s'): act |]
	   ==> s'#s#evs : traces Init Acts"


consts reachable :: "['a set, ('a * 'a)set set] => 'a set"

inductive "reachable Init Acts"
  intrs 
         (*Initial trace is empty*)
    Init  "s: Init ==> s : reachable Init Acts"

    Acts  "[| act: Acts;  s : reachable Init Acts;  (s,s'): act |]
	   ==> s' : reachable Init Acts"

end

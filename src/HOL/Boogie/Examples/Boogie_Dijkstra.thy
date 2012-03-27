(*  Title:      HOL/Boogie/Examples/Boogie_Dijkstra.thy
    Author:     Sascha Boehme, TU Muenchen
*)

header {* Boogie example: Dijkstra's algorithm *}

theory Boogie_Dijkstra
imports Boogie
uses ("Boogie_Dijkstra.b2i")
begin

text {*
We prove correct the verification condition generated from the following
Boogie code:

\begin{verbatim}
type Vertex;
const G: [Vertex, Vertex] int;
axiom (forall x: Vertex, y: Vertex ::  x != y ==> 0 < G[x,y]);
axiom (forall x: Vertex, y: Vertex ::  x == y ==> G[x,y] == 0);

const Infinity: int;
axiom 0 < Infinity;

const Source: Vertex;
var SP: [Vertex] int;

procedure Dijkstra();
  modifies SP;
  ensures (SP[Source] == 0);
  ensures (forall z: Vertex, y: Vertex ::
    SP[y] < Infinity && G[y,z] < Infinity ==> SP[z] <= SP[y] + G[y,z]);
  ensures (forall z: Vertex :: z != Source && SP[z] < Infinity ==>
    (exists y: Vertex :: SP[y] < SP[z] && SP[z] == SP[y] + G[y,z]));

implementation Dijkstra()
{
  var v: Vertex;
  var Visited: [Vertex] bool;
  var oldSP: [Vertex] int;

  havoc SP;
  assume (forall x: Vertex :: x == Source ==> SP[x] == 0);
  assume (forall x: Vertex :: x != Source ==> SP[x] == Infinity);

  havoc Visited;
  assume (forall x: Vertex :: !Visited[x]);
            
  while ((exists x: Vertex :: !Visited[x] && SP[x] < Infinity))
    invariant (SP[Source] == 0);
    invariant (forall x: Vertex :: SP[x] >= 0);
    invariant (forall y: Vertex, z: Vertex :: 
      !Visited[z] && Visited[y] ==> SP[y] <= SP[z]);
    invariant (forall z: Vertex, y: Vertex ::
      Visited[y] && G[y,z] < Infinity ==> SP[z] <= SP[y] + G[y,z]);
    invariant (forall z: Vertex :: z != Source && SP[z] < Infinity ==>
      (exists y: Vertex :: SP[y] < SP[z] && Visited[y] && 
        SP[z] == SP[y] + G[y,z]));
  {
    havoc v;
    assume (!Visited[v]);
    assume (SP[v] < Infinity); 
    assume (forall x: Vertex :: !Visited[x] ==> SP[v] <= SP[x]);

    Visited[v] := true;

    oldSP := SP;
    havoc SP;
    assume (forall u: Vertex :: 
      G[v,u] < Infinity && oldSP[v] + G[v,u] < oldSP[u] ==> 
        SP[u] == oldSP[v] + G[v,u]);
    assume (forall u: Vertex :: 
      !(G[v,u] < Infinity && oldSP[v] + G[v,u] < oldSP[u]) ==> 
        SP[u] == oldSP[u]);
    assert (forall z: Vertex:: SP[z] <= oldSP[z]);
    assert (forall y: Vertex:: Visited[y] ==> SP[y] == oldSP[y]);
  }
}
\end{verbatim}
*}


boogie_open "Boogie_Dijkstra.b2i"

declare [[smt_certificates = "Boogie_Dijkstra.certs"]]
declare [[smt_read_only_certificates = true]]
declare [[smt_oracle = false]]

boogie_vc Dijkstra
  by boogie

boogie_end 

end

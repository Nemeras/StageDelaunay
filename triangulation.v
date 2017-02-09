From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple.
From mathcomp Require Import choice path finset finfun fintype bigop.
From mathcomp Require Import ssralg ssrnum matrix mxalgebra.

From mathcomp Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope fset_scope.

Variable R : numDomainType.
(*numDomainType.*)

Parameter P : choiceType.
Parameter T : choiceType.

Check R.


Parameter xCoord : P -> R.
Parameter yCoord : P -> R.


Axiom not_2points : forall p1, forall p2, xCoord p1 = xCoord p2 -> yCoord p1 != yCoord p2.

Parameter Tr : {fset T}.
Parameter D : {fset P}.

Parameter vertex : T ->P^3.

Variable tt:T.
Check vertex tt .

Parameter interior : T -> P -> bool.
Parameter surface : T -> P -> bool.
Parameter orientedSurface : P -> P -> P -> R.

(*Axiom triangle3Vertices : forall (t: T), #|` vertex t| = 3.*)
Axiom triangle3Vertices : forall (t:T), injective (vertex t).

Open Local Scope ring_scope.
Definition vertexSet t := image (vertex t) 'I_3.
Check vertexSet.
Definition adjacent t1 t2:= #|` ((vertexSet t1) `&` (vertexSet t2))| = 2 /\ (forall p, interior t1 p -> interior t2 p = false).
Definition isLeftOf p a b := orientedSurface p a b > 0%R.

(* à ameliorer : regarder le troisieme sommet ?*)

Definition inTriangle t p := match 

  : T -> P -> bool.

Parameter inCircle :  T -> P -> bool.

Axiom allTriangles : forall p1, forall p2, forall p3, exists t, p1 \in vertex t /\ p2 \in vertex t /\ p3 \in vertex t.


Definition  Delaunay (Ts:{fset T})  := forall t1 , forall t2,
      t1 \in Ts -> t2 \in Ts ->
                          adjacent t1 t2 ->
                          forall p,
                           p \in vertex t1-> inCircle t2 p -> p \in vertex t2.




(*Axiom union_TrD : \bigcup_ ( t in Tr ) (vertex t) = D.
??*)

Definition unionTrD1 (Ts: {fset T}) (Ds : {fset P}) := forall (t:T), t \in Ts -> forall p, p \in vertex t -> p \in Ds. 

Definition unionTrD2 (Ts: {fset T}) (Ds : {fset P}) := forall (p:P), p \in Ds -> exists (t:T), t \in Ts /\ p \in vertex t.

Definition unionTrD Ts Ds := unionTrD1 Ts Ds /\ unionTrD2 Ts Ds.
                                           

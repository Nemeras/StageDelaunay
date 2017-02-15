From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple.
From mathcomp Require Import choice path finset finfun fintype bigop.
From mathcomp Require Import ssralg ssrnum matrix mxalgebra.
From mathcomp Require Import finmap.
From mathcomp Require Import zmodp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Triangulation.

Open Scope fset_scope.

Parameter R : numDomainType.


Parameter P : choiceType.
Parameter T : choiceType.

Parameter xCoord : P -> R.
Parameter yCoord : P -> R.


Axiom not_2points : forall p1, forall p2, xCoord p1 = xCoord p2 -> yCoord p1 != yCoord p2.

Parameter Tr : {fset T}.
Parameter D : {fset P}.

Parameter vertex : T -> P^3.

Variable tt:T.

(*Parameter interior : T -> P -> bool.*)
(*Parameter surface : T -> P -> bool.*)
Parameter orientedSurface : P -> P -> P -> R.


Axiom triangle3Vertices : forall (t:T), injective (vertex t).


Open Local Scope ring_scope.
Definition vertexSet t := (vertex t) @` 'I_3.


Definition isLeftOf p a b := orientedSurface p a b > 0%R.
Definition isLeftOfOrOn p a b := orientedSurface p a b >= 0%R.

Definition vertex1 t := vertex t (@Ordinal 3 0 isT).
Definition vertex2 t := vertex t (@Ordinal 3 1 isT).
Definition vertex3 t := vertex t (@Ordinal 3 2 isT).

Axiom orientedTriangle : forall t, orientedSurface (vertex1 t) (vertex2 t) (vertex3 t)>0. 


Definition inTriangle t p := isLeftOf (vertex1 t) (vertex2 t) p &&
                             isLeftOf p (vertex2 t) (vertex3 t) &&
                             isLeftOf (vertex1 t) p (vertex3 t).

Definition inTriangleWEdges t p := isLeftOfOrOn (vertex1 t) (vertex2 t) p &&
                             isLeftOfOrOn p (vertex2 t) (vertex3 t) &&
                             isLeftOfOrOn (vertex1 t) p (vertex3 t).

Definition adjacent t1 t2:= #|` ((vertexSet t1) `&` (vertexSet t2))| = 2 /\ (forall p, inTriangle t1 p -> inTriangle t2 p = false).

Parameter inCircleDeterminant : P -> P -> P -> P -> R.

Definition inCircle p a b c  := inCircleDeterminant p a b c >0.
Definition inCircleWithBoundaries p a b c := inCircleDeterminant p a b c >= 0.

Axiom allTriangles : forall p1, forall p2, forall p3, exists t, p1 \in vertexSet t /\ p2 \in vertexSet t /\ p3 \in vertexSet t.

Definition inCircleTriangle p t := inCircle p (vertex1 t) (vertex2 t) (vertex3 t).
 

Definition  Delaunay (Ts:{fset T})  := forall t1 , forall t2,
      t1 \in Ts -> t2 \in Ts ->
                          adjacent t1 t2 ->
                          forall p,
                           p \in vertexSet t1-> inCircleTriangle p t2 -> p \in vertexSet t2.

Definition n := #|`D|.

Definition RCH n (x:P) (d:P^n) (a :R^n) := ((xCoord x) == \sum_( i < n ) (a i) * xCoord (d i)) && ((yCoord x) == \sum_( i < n ) (a i) * yCoord (d i)) && (\sum_( i < n ) (a i) == 1) && [forall i : 'I_n, (0 <= (a i))].



(*Definition surfaceConvexHull1 (tr : {fset T}) (d : {fset P}) h :=
  forall t , forall p, t \in tr -> p \in d -> inTriangleWEdges t p ->  exists a, RCH p (nth p (enum_fset h)) a.

Definition surfaceConvexHull2 (tr : {fset T}) (d : {fset P}) h :=
 forall p, p \in d -> exists a, RCH p (nth p (enum_fset h)) a -> #|` [fset t in Tr | inTriangle t p]  | != 0%nat.


Definition surfaceCH tr d h := surfaceConvexHull2 tr d h /\ surfaceConvexHull1 tr d h. 
 *)


Definition unionTrD1 (Ts: {fset T}) (Ds : {fset P}) := forall (t:T), t \in Ts -> forall p, p \in vertexSet t -> p \in Ds. 

Definition unionTrD2 (Ts: {fset T}) (Ds : {fset P}) := forall (p:P), p \in Ds -> exists (t:T), t \in Ts /\ p \in vertexSet t.

Definition unionTrD Ts Ds := unionTrD1 Ts Ds /\ unionTrD2 Ts Ds.
Variable pp : P.
Variable t:{fset T}.
Check [finType of t].

Check fun (t : {fset T}) => [exists j : t, inTriangle (val j) pp].

Definition CH k (h : 'I_k.+1 -> P) (d : {fset P}) := [forall i : 'I_k.+1 , [exists j : d, h i == val j]] /\
                                                    forall i, forall p, p \in d -> isLeftOfOrOn (h i) ( h (Zp_add i (inZp 1))) p.

Check CH.

End Triangulation.
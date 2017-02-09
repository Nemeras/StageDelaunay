From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
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

Parameter vertex : T -> {fset P}.

Parameter interior : T -> P -> bool.
Parameter surface : T -> P -> bool.

Definition adjacent t1 t2:= #|` ((vertex t1) `&` (vertex t2))| = 2 /\ (forall p, interior t1 p -> interior t2 p = false).

(* à ameliorer : regarder le troisieme sommet ?*)
Open Local Scope ring_scope.
Locate one.
Check (ssralg.GRing.one R): R.
Definition isLeftOf := fun (p a b : P) =>
  let M1 := \matrix_( i<3, j<3) if i==@Ordinal 3 0 isT then if j==@Ordinal 3 0 isT then xCoord p
                                        else if j==@Ordinal 3 1 isT then yCoord p
                                               else 1%R
                             else if i==@Ordinal 3 1 isT then if j==@Ordinal 3 0 isT then xCoord a
                                               else if j==@Ordinal 3 1 isT then yCoord a
                                                    else 1%R
                                  else if j==@Ordinal 3 0 isT then xCoord b
                                       else if j==@Ordinal 3 1 isT then yCoord b
                                            else 1%R
  in \det M1.
                               

Definition inTriangle (p 

Parameter inCircle :  T -> P -> bool.

(*Definition in_circle t p := let x = x_coord p in
                            let y = y_coord p in*)
                            

Axiom allTriangles : forall p1, forall p2, forall p3, exists t, p1 \in vertex t /\ p2 \in vertex t /\ p3 \in vertex t.


Definition  Delaunay (Ts:{fset T})  := forall t1 , forall t2,
      t1 \in Ts -> t2 \in Ts ->
                          adjacent t1 t2 ->
                          forall p,
                           p \in vertex t1-> inCircle t2 p -> p \in vertex t2.

Axiom triangle3Vertices : forall (t: T), #|` vertex t| = 3.



(*Axiom union_TrD : \bigcup_ ( t in Tr ) (vertex t) = D.
??*)
Check Tr.
Definition test_union_TrD (Ts: {fset T}) (Ds : {fset P}) := forall (t:T), t \in Ts -> forall p, p \in vertex t -> p \in Ds. 

Definition test_union_TrD2 (Ts: {fset T}) (Ds : {fset P}) := forall (p:P), p \in Ds -> exists (t:T), t \in Ts /\ p \in vertex t.

Definition union_TrD Ts Ds := test_union_TrD Ts Ds /\ test_union_TrD2 Ts Ds.
                                           
Definition get_vertices t := enum_fset (vertex t).

Definition in_


From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import choice path finset finfun fintype bigop.
From mathcomp Require Import ssrnum matrix mxalgebra.

(*From mathcomp Require Import finmap.*)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Variable R : numDomainType.

Parameter P : Set.
Parameter T : Set.

Parameter x_coord : P -> R.
Parameter y_coord : P -> R.


Axiom not_2points : forall p1, forall p2, x_coord p1 = x_coord p2 -> y_coord p1 != y_coord p2.

Definition Tr := finset T.
Definition D := finset P.

Parameter vertex : T -> P -> bool.

(*Variable t : T.*)

Parameter interior : T -> P -> bool.
Parameter surface : T -> P -> bool.

Definition adjacent t1 t2 := #| finset (vertex t1) :&: finset (vertex t2)| = 2 /\ #|finset (interior t1) :&: finset (interior t2)| = 0.
  


Parameter in_circle :  T -> P -> bool.

(*Definition in_circle t p := let x = x_coord p in
                            let y = y_coord p in*)
                            

Axiom all_triangles : forall p1, forall p2, forall p3, exists t, vertex t p1 /\ vertex t p2 /\ vertex t p3.

Axiom truc : forall t1, forall t2, adjacent t1 t2 ->
                                     forall p, p \in vertex t1->in_circle t2 p -> p \in vertex t2.

Axiom triangle_3vertices : forall (t: T), #|vertex t| = 3.
Variable t:T.
Variable k:T.
Variable u:T.
Axiom union_TrD : \bigcup_ ( t in Tr ) (finset (vertex t)) = D.

Function get_vertices t :=
  let vertices := enum (finset (vertex t)) in vertices.
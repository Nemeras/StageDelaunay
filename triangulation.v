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

Variable R : numDomainType.

Variable P : choiceType.
Variable T : choiceType.

Variable xCoord : P -> R.
Variable yCoord : P -> R.


Axiom not_2points : forall p1, forall p2, xCoord p1 = xCoord p2 -> yCoord p1 != yCoord p2.

Variable Tr : {fset T}.
Variable D : {fset P}.

Variable vertex : T -> P^3.


(*Variable interior : T -> P -> bool.*)
(*Variable surface : T -> P -> bool.*)
Variable oriented_surface : P -> P -> P -> R.


Axiom triangle_3vertices : forall (t:T), injective (vertex t).

Open Local Scope ring_scope.
Definition vertex_set t := (vertex t) @` 'I_3.

Variable vertices_to_triangle : P -> P -> P -> T.

Hypothesis vertices_to_triangle_correct :
  forall p1, forall p2, forall p3, forall t, vertices_to_triangle p1 p2 p3 == t <->
  (p1 \in vertex_set t /\ p2 \in vertex_set t /\ p3 \in vertex_set t).
                                                                 

Axiom not_2_triangles : forall (t1 : T), forall (t2 : T), t1 == t2 <-> (vertex_set t1 == vertex_set t2).




Definition is_left_of p a b := oriented_surface p a b > 0%R.
Definition is_left_or_on_line p a b := oriented_surface p a b >= 0%R.

Definition vertex1 t := vertex t (@Ordinal 3 0 isT).
Definition vertex2 t := vertex t (@Ordinal 3 1 isT).
Definition vertex3 t := vertex t (@Ordinal 3 2 isT).

Axiom oriented_triangle : forall t, oriented_surface (vertex1 t) (vertex2 t) (vertex3 t)>0. 


Definition in_triangle t p := is_left_of (vertex1 t) (vertex2 t) p &&
                             is_left_of p (vertex2 t) (vertex3 t) &&
                             is_left_of (vertex1 t) p (vertex3 t).

Definition in_triangle_wedges t p := is_left_or_on_line (vertex1 t) (vertex2 t) p &&
                             is_left_or_on_line p (vertex2 t) (vertex3 t) &&
                             is_left_or_on_line (vertex1 t) p (vertex3 t).

Definition adjacent t1 t2:= #|` ((vertex_set t1) `&` (vertex_set t2))| = 2.
(*/\ (forall p, in_triangle t1 p -> in_triangle t2 p = false).*)

Variable in_circle_determinant : P -> P -> P -> P -> R.

Definition in_circle p a b c  := in_circle_determinant p a b c >0.
Definition in_circle_wboundaries p a b c := in_circle_determinant p a b c >= 0.

Axiom allTriangles : forall p1, forall p2, forall p3, exists t, p1 \in vertex_set t /\ p2 \in vertex_set t /\ p3 \in vertex_set t.

Definition in_circle_triangle p t := in_circle p (vertex1 t) (vertex2 t) (vertex3 t).


Definition nd := #|`D|.


(*Definition RCH (x:P) n (d:P^n) (a :R^n) := ((xCoord x) == \sum_( i < n ) (a i) * xCoord (d i)) && ((yCoord x) == \sum_( i < n ) (a i) * yCoord (d i)) && (\sum_( i < n ) (a i) == 1) && [forall i : 'I_n, (0 <= (a i))].*)

Definition hull (d: {fset P}) (x : P) := exists (a : d -> R), 
  ((xCoord x) == \sum_ i  (a i) * xCoord (val i)) && 
 ((yCoord x) == \sum_ i (a i) * yCoord (val i)) &&
 (\sum_ i (a i) == 1) && [forall i, (0 <= (a i))].

Definition encompassed x h := ucycle (is_left_or_on_line x) h.

Definition all_left_of (d : {fset P}) x y  := [forall p : d, is_left_or_on_line x y (val p)].

Open Local Scope nat_scope.

Definition CH (s : seq P) (d : {fset P}) := ((seq_fset s) `<=` d) /\
                                            (forall x, encompassed x s) /\
                                            (#|`d| >= 2 -> (size s) >= 2).

Hypothesis encompassed_ch : forall d : {fset P}, forall x, hull d x <-> forall h,  (CH h d  -> encompassed x h).

Definition union_trD1 (Ts: {fset T}) (Ds : {fset P}) :=
forall (t:T), t \in Ts -> forall p, p \in vertex_set t -> p \in Ds. 

Definition union_trD2 (Ts: {fset T}) (Ds : {fset P}) :=
forall (p:P), p \in Ds -> exists (t:T), t \in Ts /\ p \in vertex_set t.

Definition union_trD Ts Ds := union_trD1 Ts Ds /\ union_trD2 Ts Ds.

Variable mkCH : {fset P} -> seq P. 

Hypothesis mkCH_correct : forall d, CH (mkCH d) d. 

Definition covers_hull (tr : {fset T}) (d : {fset P}) :=
forall p : P, hull d p -> exists t, (t \in tr) /\ (in_triangle_wedges t p).

Definition covers_vertices (tr : {fset T}) (d : {fset P}) :=
forall p : P, p \in d -> exists t, (t \in tr) /\ (p \in vertex_set t).


Definition no_cover_intersection (tr : {fset T}) (d : {fset P}) :=
  forall t1, forall t2, forall p, p \in vertex_set t1 -> in_triangle t2 p -> false.

Definition regular (Ts:{fset T})  := forall t1 , forall t2,
      t1 \in Ts -> t2 \in Ts ->
                         forall p, p \in vertex_set t1-> in_circle_triangle p t2 -> false.

Definition no_point_on_segment (Ts : {fset T}) (d : {fset P}) :=
  forall t1, forall t2,forall p, p \in vertex_set t1 -> in_triangle_wedges t2 p -> p \in vertex_set t2.

Definition triangulation tr d := covers_hull tr d /\ covers_vertices tr d /\
                                 no_cover_intersection tr d /\ no_point_on_segment tr d.

Definition delaunay tr d := triangulation tr d /\ regular tr.

End Triangulation.
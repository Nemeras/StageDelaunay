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



Hypothesis oriented_surface_x_x_x : forall x, oriented_surface x x x = 0%R.

Lemma is_left_or_on_line_x_x_x : forall x, is_left_or_on_line x x x.
Proof.
  by intro;unfold is_left_or_on_line; rewrite oriented_surface_x_x_x.
Qed.

Definition vertex1 t := vertex t (@Ordinal 3 0 isT).
Definition vertex2 t := vertex t (@Ordinal 3 1 isT).
Definition vertex3 t := vertex t (@Ordinal 3 2 isT).

Axiom oriented_triangle : forall t, oriented_surface (vertex1 t) (vertex2 t) (vertex3 t)>0. 


Definition in_triangle t p := is_left_of (vertex1 t) (vertex2 t) p &&
                             is_left_of p (vertex2 t) (vertex3 t) &&
                             is_left_of (vertex1 t) p (vertex3 t).

Definition in_triangle_w_edges t p := is_left_or_on_line (vertex1 t) (vertex2 t) p &&
                             is_left_or_on_line p (vertex2 t) (vertex3 t) &&
                             is_left_or_on_line (vertex1 t) p (vertex3 t).

Hypothesis in_triangle_imply_w_edges : forall t, forall p, in_triangle t p -> in_triangle_w_edges t p.

Hypothesis in_triangle_vertex_correct: forall t, forall p, p \in vertex_set t -> in_triangle_w_edges t p.
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
  ((xCoord x) == \sum_ i  (a i) * xCoord (val i)) /\ 
 ((yCoord x) == \sum_ i (a i) * yCoord (val i)) /\
 (\sum_ i (a i) == 1) /\ [forall i, (0 <= (a i))].

Definition encompassed x h := ucycle (is_left_or_on_line x) h.

Definition all_left_of (d : {fset P}) x y  := [forall p : d, is_left_or_on_line x y (val p)].

Open Local Scope nat_scope.

Definition CH (s : seq P) (d : {fset P}) := ((seq_fset s) `<=` d) /\
                                            (forall x, x \in d -> encompassed x s) /\
                                            (#|`d| >= 2 -> (size s) >= 2) /\
                                            (#|`d| = 1 -> (size s) = 1).

Hypothesis encompassed_ch : forall d : {fset P}, forall x, hull d x = forall h,  (CH h d  -> encompassed x h).

Definition union_trD1 (Ts: {fset T}) (Ds : {fset P}) :=
forall (t:T), t \in Ts -> forall p, p \in vertex_set t -> p \in Ds. 

Definition union_trD2 (Ts: {fset T}) (Ds : {fset P}) :=
forall (p:P), p \in Ds -> exists (t:T), t \in Ts /\ p \in vertex_set t.

Definition union_trD Ts Ds := union_trD1 Ts Ds /\ union_trD2 Ts Ds.

Variable mkCH : {fset P} -> seq P. 

Hypothesis mkCH_correct : forall d, CH (mkCH d) d. 

Definition covers_hull (tr : {fset T}) (d : {fset P}) :=
forall p : P, hull d p -> exists t, (t \in tr) /\ (in_triangle_w_edges t p).

Definition covers_vertices (tr : {fset T}) (d : {fset P}) :=
forall p : P, p \in d -> exists t, (t \in tr) /\ (p \in vertex_set t).


Definition no_cover_intersection (tr : {fset T}) (d : {fset P}) :=
  forall t1, forall t2, forall p, p \in vertex_set t1 -> in_triangle t2 p -> false.

Definition regular (Ts:{fset T})  := forall t1 , forall t2,
      t1 \in Ts -> t2 \in Ts ->
                         forall p, p \in vertex_set t1-> in_circle_triangle p t2 -> false.

Definition no_point_on_segment (Ts : {fset T}) (d : {fset P}) :=
  forall t1, forall t2,forall p, p \in vertex_set t1 -> in_triangle_w_edges t2 p -> p \in vertex_set t2.

Definition triangulation tr d := covers_hull tr d /\ covers_vertices tr d /\
                                 no_cover_intersection tr d /\ no_point_on_segment tr d.

Definition delaunay tr d := triangulation tr d /\ regular tr.

Definition split_triangle_aux t p :=
  let p1 := vertex1 t in
  let p2 := vertex2 t in
  let p3 := vertex3 t in
  let t1 := vertices_to_triangle p1 p2 p in
  let t2 := vertices_to_triangle p p2 p3 in
  let t3 := vertices_to_triangle p1 p p3 in
  t1 |` (t2 |` [fset t3]).



Definition split_triangle tr t p := (split_triangle_aux t p ) `|` (tr `\ t).

Check split_triangle.
Hypothesis three_triangles_cover_one :
  forall t, forall p, in_triangle_w_edges t p ->
            forall p0, exists t1, (t1 \in split_triangle_aux t p) /\ (in_triangle_w_edges t1 p0).

Definition get_third_vertex t p1 p2 :=
  if (vertex1 t == p1) || (vertex1 t == p2) then
    (if (vertex2 t == p1) || (vertex2 t == p2) then
       vertex3 t
     else vertex2 t)
    else vertex1 t.

Definition flip_edge tr t1 t2 p1 p2 :=
  let p31 := get_third_vertex t1 p1 p2 in
  let p32 := get_third_vertex t2 p1 p2 in
  let new_t1 := vertices_to_triangle p31 p32 p1 in
  let new_t2 := vertices_to_triangle p31 p32 p2 in
  new_t1 |` (new_t2 |` ((tr `\ t1) `\ t2)).

Lemma hull_add_point : forall p, forall d, hull d p -> forall p0, (hull (p |` d ) p0) -> hull d p0.
Proof.
  intros.
  unfold hull in H0.
  destruct H0 as [a H0].
  destruct H0 as [Hx H0].
  destruct H0 as [Hy H0].
  destruct H0 as [Hsum Hpos].
  unfold hull in H. 
  destruct H as [b H].
  destruct H as [Hbx H].
  destruct H as [Hby H].
  destruct H as [Hbsum Hbpos].
  
  
(*   intros.
    rewrite encompassed_ch.
    intros.
    rewrite encompassed_ch in H0.
    apply H0.
    assert (CH_h_d := H1).
    unfold CH.
    unfold CH in H1.
    destruct H1.
    split.
    assert (d `<=` p |` d).
    exact:fsubsetU1.
    apply/fsubset_trans.
    apply H1. trivial.
    destruct H2.
    split.
    intros.
    assert (x=p \/ x \in d).
      by apply /fset1UP.
      destruct H5.
      rewrite encompassed_ch in H.
      rewrite H5.
        by apply H.
          by apply H2.
          split.
          rewrite encompassed_ch in H.    
          intro.
          assert (#|` d| = 1%N \/ #|` d|>1%N).
          admit.
          destruct H5.
          assert (exists x, d = [fset x]).
            by apply /cardfs1P; rewrite H5.
            destruct H6.
            remember [:: x] as S.
            assert (CH S d).
            unfold CH.
            split.
            rewrite HeqS.
            rewrite H6.
            exact:fsubset_refl.
            split.
            rewrite H6.
            intros.
            assert (x0 = x).
            by apply /fset1P.
            rewrite H8.
            unfold encompassed.
       (*     unfold is_left_or_on_line.*)
            rewrite HeqS.
            unfold ucycle.
            assert (uniq [:: x]).
              by [].
              rewrite H9.
              simpl.
              by rewrite is_left_or_on_line_x_x_x.
            rewrite H5.
            split.
            intro.
            rewrite ltnn in H7.
            trivial.
              by assert false.
              intro.
                by rewrite HeqS.
                assert (encompassed p S).
                  by apply H.
                  unfold CH in H7.
                  destruct H7.
                  destruct H9.
                  destruct H10.
                  unfold encompassed in H8.
                  unfold ucycle in H8.
                  rewrite HeqS in H8.
                  simpl in H8.*)
    Qed.
   Lemma hull_from_triangle :
  forall d, forall tr, forall t, forall p, triangulation tr d -> t \in tr -> in_triangle t p -> hull d p.
  Proof.
    intros.
    
    unfold triangulation in H.    
    destruct H as [H H'].
    unfold covers_hull in H.
    Admitted.
    (*apply H.
    exists t.
    apply in_triangle_imply_w_edges in H1.
    by rewrite H0 H1.
Qed.*)

  Theorem triangulation_split_triangle:
  forall tr, forall t , forall p, forall d, triangulation tr d -> t \in tr -> in_triangle t p ->
                      triangulation (split_triangle tr t p) (p |` d).
    intros.
    assert(triangulation_tr_d := H).
    unfold triangulation in H.
    unfold triangulation.
  split.
  unfold covers_hull.
  intros.
  destruct H as [covers_hull_trd H].
  unfold covers_hull in covers_hull_trd.
  assert (p0 = p \/ p0 != p).
  admit.
  destruct H3.
  rewrite H3.
  exists (vertices_to_triangle (vertex1 t) (vertex2 t) p).
  trivial.
  split.
  unfold split_triangle.
  unfold split_triangle_aux.
  assert (vertices_to_triangle (vertex1 t) (vertex2 t) p
    \in vertices_to_triangle (vertex1 t) (vertex2 t) p
        |` [fset vertices_to_triangle p (vertex2 t) (vertex3 t); vertices_to_triangle 
                                                                   (vertex1 t) p 
                                                                   (vertex3 t)]).
  apply fset1U1.
  by apply /fsetUP;rewrite H4;left.


  assert (((vertex1 t) \in vertex_set (vertices_to_triangle (vertex1 t) (vertex2 t) p)) /\
          (vertex2 t \in vertex_set (vertices_to_triangle (vertex1 t) (vertex2 t) p)) /\
          p \in vertex_set (vertices_to_triangle (vertex1 t) (vertex2 t) p)).
    by apply vertices_to_triangle_correct.
    by destruct H4;destruct H4; destruct H5; destruct H4; apply in_triangle_vertex_correct.

    assert (hull d p).
    Check hull_from_triangle.
    apply hull_from_triangle with tr t; trivial.
    assert (hull d p0).

    
    admit.

    
    apply covers_hull_trd in H4.
    destruct H4 as [t1 H4]; destruct H4.
    assert (t1 = t \/ t1 !=t).
    admit.

    destruct H6.
    assert (in_triangle_w_edges t p0).
    rewrite <- H6;trivial.
    assert (in_triangle_w_edges t p) as intwe. by apply in_triangle_imply_w_edges.
    assert (exists t1, (t1 \in split_triangle_aux t p) /\ (in_triangle_w_edges t1 p0)).
    by apply three_triangles_cover_one.
    destruct H8 as [x H8].
    destruct H8 as [H8 H9].
    exists x.
    split;trivial.
    unfold split_triangle.
    by apply /fsetUP; rewrite H8; left.


    exists t1.
    split; trivial.
    unfold split_triangle.
    assert (t1 \in (tr `\ t)).
    
    apply /fsetD1P;split;trivial.
    by apply /fsetUP; rewrite H7; right.

    
End Triangulation.
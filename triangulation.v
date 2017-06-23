From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple.
From mathcomp Require Import choice path finset finfun fintype bigop.
From mathcomp Require Import ssralg ssrnum matrix mxalgebra.
From mathcomp Require Import finmap.
From mathcomp Require Import zmodp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Open Scope fset_scope.

Lemma leq_imfset_card (T K : choiceType) (f : T -> K) P (A : {fset T})
  (p : finmempred P A) : (#|` imfset f p| <= #|` A|)%N.
Proof.
have vP (x : A) : P (val x) by rewrite -(finmempredE p) (valP x).
rewrite
  (leq_trans _ (leq_imset_card (fun x : A => [` in_imfset f p (vP x)]) _)) //.
apply/subset_leq_card/subsetP=> /= x _; apply/imsetP => /=.
have /imfsetP [t Pt x_def] := valP x.
have tA : t \in A by rewrite (finmempredE p).
by exists [` tA] => //; apply/val_inj.
Qed.

Section Triangulation.

Open Scope fset_scope.

Variable R : realDomainType.

Variable P : choiceType.
Variable T : choiceType.
Variable E : choiceType.

Variable xCoord : P -> R.
Variable yCoord : P -> R.

Variable vertex : T -> 'I_3 -> P.

Definition ord30 := @Ordinal 3 0 isT.
Definition ord31 := @Ordinal 3 1 isT.
Definition ord32 := @Ordinal 3 2 isT.

Definition ord20 := @Ordinal 2 0 isT.
Definition ord21 := @Ordinal 2 1 isT.


Definition vertex1 t := vertex t ord30.
Definition vertex2 t := vertex t ord31.
Definition vertex3 t := vertex t ord32.

Variable vertices_to_edge : P -> P -> E.

Variable edge : T -> 'I_3 -> E.

Definition edge1 t := edge t ord30.
Definition edge2 t := edge t ord31.
Definition edge3 t := edge t ord32.

Open Scope fset_scope.

Variable oriented_surface : P -> P -> P -> R.

Open Scope ring_scope.

Definition vertex_set t := (vertex t) @` 'I_3.
Definition edges_set t := (edge t) @` 'I_3.
Variable vertices_to_triangle : P -> P -> P -> T.

Definition is_left_of p a b := oriented_surface p a b > 0%R.
Definition is_left_or_on_line p a b := oriented_surface p a b >= 0%R.
Variable on_edge : E -> P-> bool.


Hypothesis vertices_to_triangle_correct : forall a b c, 
    is_left_or_on_line a b c ->
    a = vertex (vertices_to_triangle a b c) ord30 /\
    b = vertex (vertices_to_triangle a b c) ord31 /\
    c = vertex (vertices_to_triangle a b c) ord32.

Hypothesis vertices_to_edge_sym :
  forall a b, vertices_to_edge a b = vertices_to_edge b a.

Hypothesis oriented_surface_x_x : forall x y, oriented_surface x x y = 0%R.

Definition oriented_triangle t:=
  oriented_surface (vertex1 t) (vertex2 t) (vertex3 t)>=0.

Definition oriented_triangle_strict t :=
  oriented_surface (vertex1 t) (vertex2 t) (vertex3 t)>0.

Hypothesis vertices_to_triangle_oriented :
  forall a b c, oriented_triangle (vertices_to_triangle a b c).

Hypothesis oriented_surface_change1 :
  forall a b c, oriented_surface a b c = -oriented_surface a c b.

Hypothesis oriented_surface_circular :
  forall a b c, oriented_surface a b c = oriented_surface c a b.

Lemma is_left_of_circular  a b c: is_left_of a b c = is_left_of c a b.
Proof.
by rewrite /is_left_of oriented_surface_circular.
Qed.

Lemma is_left_or_on_line_circular a b c: 
        is_left_or_on_line a b c = is_left_or_on_line c a b.
Proof.
by rewrite /is_left_or_on_line oriented_surface_circular.
Qed.

Lemma is_left_or_on_line_change1 a b c:
  ~~ is_left_or_on_line b a c ->  is_left_or_on_line a b c.
Proof.
rewrite /is_left_or_on_line.
rewrite oriented_surface_change1 oriented_surface_circular oppr_ge0 -ltrNge.
rewrite -[X in 0 <= X]opprK oppr_ge0 ler_oppl oppr0 ltr_def.
by move => /andP[].
Qed.

Definition is_on_line a b c := oriented_surface a b c == 0.

Lemma is_on_line_sym a b c : is_on_line a b c = is_on_line b a c.
Proof.
rewrite /is_on_line oriented_surface_change1.
by rewrite oriented_surface_circular oppr_eq0.
Qed.

Lemma is_on_line_circular a b c : is_on_line a b c = is_on_line c a b.
Proof.
by rewrite /is_on_line oriented_surface_circular.
Qed.

Hypothesis is_on_line_trans :
  forall a b c d, a != b -> is_on_line a b c -> is_on_line a b d ->
    is_on_line a c d.

Hypothesis on_line_on_edge :
  forall a b c, is_left_of a b c -> forall q, is_on_line a c q -> 
                                   is_left_of a b q -> is_left_of b c q ->
                                   on_edge (vertices_to_edge a c) q.

Hypothesis on_edge_on_line :
  forall a b c, is_left_of a b c -> 
  forall q, on_edge (vertices_to_edge a c) q ->
           is_on_line a c q /\ is_left_of a b q /\ is_left_of b c q.

Lemma  is_left_or_on_split a b c :
  is_left_or_on_line a b c  -> is_on_line a b c \/ is_left_of a b c.
Proof.
move => is_lor_abc.
case abc0 : (is_on_line a b c);first by left.
right. rewrite /is_left_of lt0r. apply/andP;split => //=.
by move:abc0;rewrite /is_on_line;move => /eqP /eqP. 
Qed.

Hypothesis edges_set_vertices_to_triangle: 
  forall a b c, is_left_of a b c ->
    edges_set (vertices_to_triangle a b c) = 
                       [fset (vertices_to_edge a b);
                           vertices_to_edge a c;
                           vertices_to_edge b c].

(*Lemma oriented_surface_change2 a b c :
        oriented_surface a b c = -oriented_surface b a c.
Proof.
rewrite -[X in _ = - X] oriented_surface_circular.
exact : oriented_surface_change1.
Qed.

Lemma oriented_surface_change3 a b c: 
        oriented_surface a b c = -oriented_surface c b a.
Proof.
rewrite [X in _ = - X] oriented_surface_circular.
exact:oriented_surface_change1.
Qed.*)

Lemma is_left_or_on_change a b c :
        is_left_or_on_line a b c = ~~ is_left_of b a c.
Proof.
by rewrite /is_left_or_on_line /is_left_of oriented_surface_change1 
oriented_surface_circular oppr_ge0 real_lerNgt => //=; apply num_real.
Qed.


Lemma is_left_of_change a b c: 
        is_left_of a b c = ~~ is_left_or_on_line b a c.
Proof.
rewrite /is_left_or_on_line /is_left_of.
rewrite oriented_surface_change1 oriented_surface_circular.
rewrite oppr_gt0.
by rewrite real_ltrNge => //=; apply num_real.
Qed.

Lemma is_lof_imply_is_lor_on_line a b c :
    is_left_of a b c -> is_left_or_on_line a b c.
Proof.
by apply ltrW.
Qed.


Hypothesis vertex_set_vertices_to_triangle :
  forall a b c, vertex_set (vertices_to_triangle a b c) = [fset a;b;c].

Lemma vertices_to_triangle_correct2 : forall p1 p2 p3 t,
  t = vertices_to_triangle p1 p2 p3 ->
  p1 \in vertex_set t /\ p2 \in vertex_set t /\ p3 \in vertex_set t.
Proof.
by move => p1 p2 p3 t tv; rewrite tv vertex_set_vertices_to_triangle !inE
  !eqxx !orbT.
Qed.

Definition in_triangle t p := is_left_of (vertex1 t) (vertex2 t) p &&
                              is_left_of p (vertex2 t) (vertex3 t) &&
                              is_left_of (vertex1 t) p (vertex3 t).

Hypothesis axiom4_knuth : forall a b c d, is_left_of a b d ->
                                     is_left_of b c d ->
                                     is_left_of c a d ->
                                     is_left_of a b c.

Definition in_triangle_w_edges t p := 
  is_left_or_on_line (vertex1 t) (vertex2 t) p &&
  is_left_or_on_line p (vertex2 t) (vertex3 t) &&
  is_left_or_on_line (vertex1 t) p (vertex3 t).

Lemma in_triangle_imply_w_edges t p : in_triangle t p ->
   in_triangle_w_edges t p.
Proof.
move => /andP [intp intp3];move:intp => /andP [intp1 intp2].
by apply /andP;split;first apply /andP;first split;apply ltrW.
Qed.

Hypothesis in_triangle_on_edge :
  forall t, forall p,   in_triangle t p ->
  forall t2, (exists p2, in_triangle t2 p2) ->
  forall e,  e \in edges_set t2 -> on_edge e p ->
  exists q,  in_triangle t q /\ in_triangle t2 q.

Hypothesis intersection_of_lines : forall a b c d,
  is_left_of a b c -> is_on_line a b d ->
  is_on_line a c d -> d = a.

Lemma is_left_or_on_line_on_line a b c :
  is_left_or_on_line a b c -> is_left_or_on_line a c b -> is_on_line a b c.
Proof.
rewrite /is_left_or_on_line => Habc.
rewrite oriented_surface_change1 ler_oppr oppr0 => Habc2.
by rewrite /is_on_line;apply/eqP;symmetry;apply/eqP;
rewrite eqr_le Habc;apply/andP;split.
Qed.

Hypothesis vertices_to_edge_in_edges_set:
forall a, forall t,  a \in vertex_set t -> forall b, b \in vertex_set t ->
b != a -> (vertices_to_edge a b) \in edges_set t.

Lemma is_ol_imply_islor a b c :is_on_line a b c -> is_left_or_on_line a b c.
Proof.
by rewrite /is_on_line /is_left_or_on_line => /eqP ->.
Qed.

Ltac easygeo_aux:=
(try by []);
(try by rewrite is_left_of_circular);
(try by rewrite -is_left_of_circular);
(try by rewrite is_left_or_on_line_circular);
(try by rewrite -is_left_or_on_line_circular);
(try by rewrite is_on_line_circular);
(try by rewrite -is_on_line_circular);
(try by rewrite is_on_line_sym is_on_line_circular);
(try by rewrite is_on_line_sym -is_on_line_circular);
(try by rewrite is_on_line_sym);
(try by rewrite /is_left_of /is_left_or_on_line /oriented_triangle
 /oriented_triangle_strict;
(try by rewrite oriented_surface_circular);
(try by rewrite -oriented_surface_circular);
(try by rewrite oriented_surface_x_x);
(try by rewrite oriented_surface_circular oriented_surface_x_x);
(try by rewrite -oriented_surface_circular oriented_surface_x_x)).

Ltac easygeo :=
easygeo_aux;
try (by apply is_lof_imply_is_lor_on_line;easygeo_aux);
try (by apply is_ol_imply_islor;easygeo_aux).

Lemma triangle_not_empty t p:  in_triangle t p -> oriented_triangle_strict t.
Proof.
move => /andP[] /andP [] islof1 islof2 islof3.
rewrite /oriented_triangle_strict.
apply:(axiom4_knuth islof1);easygeo.
Qed.

Hypothesis all_triangles_oriented :
forall t, oriented_triangle_strict t ->
  t = vertices_to_triangle (vertex1 t) (vertex2 t) (vertex3 t).

Lemma in_triangle_w_edge_edges t: 
  oriented_triangle_strict t -> forall p, in_triangle_w_edges t p <->
  (p \in vertex_set t) \/ (in_triangle t p) \/
  (exists e, e \in edges_set t /\ on_edge e p). 
Proof.
move => or_t p.
have d31 : vertex3 t != vertex1 t.
  apply/negP => /eqP abs; move: or_t; rewrite /oriented_triangle_strict.
  by rewrite oriented_surface_circular abs oriented_surface_x_x ltrr.
have d23 : vertex2 t != vertex3 t.
  apply/negP => /eqP abs; move: or_t; rewrite /oriented_triangle_strict.
  by rewrite 2!oriented_surface_circular abs oriented_surface_x_x ltrr.
have d12 : vertex1 t != vertex2 t.
  apply/negP => /eqP abs; move: or_t; rewrite /oriented_triangle_strict.
  by rewrite abs oriented_surface_x_x ltrr.
split.
  move => /andP [] /andP[] islor12p islorp23 islor1p3.
  case islo12p:(is_left_of (vertex1 t) (vertex2 t) p);
  case islop23:(is_left_of p (vertex2 t) (vertex3 t));
  case islo1p3:(is_left_of (vertex1 t) p (vertex3 t));
  try (by right;left;apply/andP;split => //=;apply/andP;split);
  try (move:islo1p3;rewrite /is_left_of => /negP /negP;
  rewrite -lerNgt oriented_surface_change1 ler_oppl oppr0 
  => islor13p);
  try (move:islo12p;rewrite /is_left_of => /negP /negP;
  rewrite -lerNgt oriented_surface_change1 ler_oppl oppr0
  => islor1p2);
  try (move:islop23;rewrite /is_left_of => /negP /negP;
  rewrite -lerNgt oriented_surface_change1 ler_oppl oppr0
  => islorp32);
  try (have isol1p3 := is_left_or_on_line_on_line islor1p3 islor13p);
  try (have isol12p := is_left_or_on_line_on_line islor12p islor1p2);
  try (have isolp23 := is_left_or_on_line_on_line islorp23 islorp32);
  [ | |
  by rewrite is_on_line_sym is_on_line_circular in isolp23;
  rewrite is_on_line_circular in isol1p3;
  rewrite /oriented_triangle_strict oriented_surface_circular in or_t;
  have temp := (intersection_of_lines or_t isol1p3 isolp23 );
  left;rewrite temp;apply/imfsetP;exists ord32|move|
  by rewrite -is_on_line_circular is_on_line_sym is_on_line_circular in isol1p3;
  have temp := (intersection_of_lines or_t isol12p isol1p3 );
  left;rewrite temp;apply/imfsetP;exists ord30|
  by rewrite is_on_line_sym in isol12p;
  rewrite -is_on_line_circular in isolp23;
  rewrite /oriented_triangle_strict -oriented_surface_circular in or_t;
  have temp := (intersection_of_lines or_t isolp23 isol12p );
  left;rewrite temp;apply/imfsetP;exists ord31|
  by rewrite is_on_line_sym in isol12p;
  rewrite -is_on_line_circular in isolp23;
  rewrite /oriented_triangle_strict -oriented_surface_circular in or_t;
  have temp := (intersection_of_lines or_t isolp23 isol12p );
  left;rewrite temp;apply/imfsetP;exists ord31];right;right;
  [exists (vertices_to_edge (vertex1 t) (vertex3 t))|exists (vertices_to_edge (vertex3 t) (vertex2 t))|
   exists (vertices_to_edge (vertex2 t) (vertex1 t))];split => //=;
  try (apply: vertices_to_edge_in_edges_set => //;apply/imfsetP);
  try (by exists ord30;rewrite/vertex1);
  try (by exists ord31;rewrite/vertex2);
  try (by exists ord32;rewrite/vertex3) => //=.
      apply:(@on_line_on_edge (vertex1 t) (vertex2 t) (vertex3 t) _ p);easygeo.
    apply:(@on_line_on_edge (vertex3 t) (vertex1 t) (vertex2 t) _ p);easygeo.
  apply:(@on_line_on_edge (vertex2 t) (vertex3 t) (vertex1 t) _ p);easygeo.
move => [|[|]];try by apply in_triangle_imply_w_edges.
  apply is_lof_imply_is_lor_on_line in or_t.
  move => /imfsetP [[[|[|[|x']]] px] _] ptx=> //=;
  (try have:Ordinal px = ord30 by apply:ord_inj);
  (try have:Ordinal px = ord31 by apply:ord_inj);
  (try have:Ordinal px = ord32 by apply:ord_inj) => Ordpx;
  rewrite Ordpx in ptx; rewrite ptx;
  apply/andP;split;try (apply/andP;split);
  rewrite -/vertex1 -/vertex2 -/vertex3;easygeo.
have deft := (all_triangles_oriented or_t). rewrite deft.
move => [e[e_t e_p]].
rewrite (edges_set_vertices_to_triangle or_t) in e_t.
move:e_t => /fsetUP [/fset2P[]|/fset1P] defe;rewrite defe in e_p;
[rewrite /oriented_triangle_strict -oriented_surface_circular in or_t|move|
rewrite /oriented_triangle_strict oriented_surface_circular in or_t];
have temp := on_edge_on_line or_t;
[rewrite vertices_to_edge_sym in temp|move|rewrite vertices_to_edge_sym in temp];
apply temp in e_p;move:e_p=> [H1 [ H2 H3]];
[rewrite oriented_surface_circular in or_t|move|
rewrite -oriented_surface_circular in or_t];
have vc := vertices_to_triangle_correct (is_lof_imply_is_lor_on_line or_t);
move :vc => [vc1 [vc2 vc3]];
rewrite /in_triangle_w_edges /vertex1 /vertex2 /vertex3 -vc1 -vc2 -vc3;
apply/andP;split;try (apply/andP;split);easygeo.
Qed.

Lemma vert_in_triangle_w_edges : forall t, forall p,
      oriented_triangle t -> p \in vertex_set t
                                  -> in_triangle_w_edges t p.
Proof.
move => t p or_t.
rewrite /vertex_set => /imfsetP [[[|[|[|x]]] px] _] p_tx => //=;
(try have:Ordinal px = ord30 by apply:ord_inj);
(try have:Ordinal px = ord31 by apply:ord_inj);
(try have:Ordinal px = ord32 by apply:ord_inj);
move => ordpx;rewrite ordpx in p_tx;rewrite p_tx /in_triangle_w_edges;
apply /andP;split;
[apply/andP;split|by rewrite /vertex1 /is_left_or_on_line oriented_surface_x_x|
 apply/andP;split|rewrite -/vertex2;exact:or_t|apply/andP;split|
rewrite /vertex3 /is_left_or_on_line -oriented_surface_circular oriented_surface_x_x] => //=;
rewrite /vertex1 /vertex2 /vertex3 /is_left_or_on_line;
(try by rewrite oriented_surface_x_x);
(try by rewrite oriented_surface_circular oriented_surface_x_x);
(try by rewrite -oriented_surface_circular oriented_surface_x_x).
Qed.


Lemma in_triangle_not_vert t p: 
 in_triangle t p -> p \notin vertex_set t.
Proof.
rewrite /in_triangle.
case abs:(p \in vertex_set t) => //=.
by move:abs => /imfsetP [[[|[|[|x']]] px] _] vtx => //=;
(try have:Ordinal px = ord30 by apply ord_inj);
(try have:Ordinal px = ord31 by apply ord_inj);
(try have:Ordinal px = ord32 by apply ord_inj) => ordpx;
rewrite ordpx in vtx;rewrite vtx;rewrite /vertex1 /vertex2 /vertex3;
move => /andP [] /andP [];[move => abs _ _|move => _ abs _|move => _ _ abs];
[rewrite is_left_of_circular in abs |move|rewrite -is_left_of_circular in abs];
rewrite /is_left_of oriented_surface_x_x ltrr in abs.
Qed.

Hypothesis vert_not_on_edges: forall t p,   oriented_triangle t -> p \in vertex_set t -> 
                         forall e, (e \in edges_set t -> on_edge e p -> false).

Definition adjacent t1 t2 := #|` ((vertex_set t1) `&` (vertex_set t2))| = 2.

Variable in_circle_determinant : P -> P -> P -> P -> R.

Definition in_circle p a b c  := 0 < in_circle_determinant p a b c.

Definition in_circle_wboundaries p a b c := in_circle_determinant p a b c >= 0.

Definition in_circle_triangle p t := in_circle p (vertex1 t) (vertex2 t) (vertex3 t).

Hypothesis vertex_set_edge_triangle :
  forall t, forall a, a \in vertex_set t ->  forall b, b \in vertex_set t -> a!=b ->
            (vertices_to_edge a b) \in edges_set t.



Definition hull (d: {fset P}) (x : P) := exists (a : d -> R), 
  ((xCoord x) == \sum_ i  (a i) * xCoord (val i)) /\ 
 ((yCoord x) == \sum_ i (a i) * yCoord (val i)) /\
 (\sum_ i (a i) == 1) /\ (forall i, (0 <= (a i))) /\ (d != fset0).

Definition encompassed x h := ucycle (is_left_or_on_line x) h.

Definition all_left_of (d : {fset P}) x y  := [forall p : d, is_left_or_on_line x y (val p)].

Open Scope nat_scope.

Definition CH (s : seq P) (d : {fset P}) := ((seq_fset s) `<=` d) /\
                                            (forall x, x \in d -> encompassed x s) /\
                                            (#|`d| >= 2 -> (size s) >= 2) /\
                                            (#|`d| = 1 -> (size s) = 1).

(*Hypothesis encompassed_ch : forall d : {fset P}, forall x, 0 < #|`d| -> hull d x = forall h,
                                  (CH h d  -> encompassed x h).
*)

(*Definition union_trD1 (Ts: {fset T}) (Ds : {fset P}) :=
forall (t:T), t \in Ts -> forall p, p \in vertex_set t -> p \in Ds. 

Definition union_trD2 (Ts: {fset T}) (Ds : {fset P}) :=
forall (p:P), p \in Ds -> exists (t:T), t \in Ts /\ p \in vertex_set t.

Definition union_trD Ts Ds := union_trD1 Ts Ds /\ union_trD2 Ts Ds.
(*
Variable mkCH : {fset P} -> seq P. 

Hypothesis mkCH_correct : forall d, CH (mkCH d) d. *)
*)
Definition covers_hull (tr : {fset T}) (d : {fset P}) :=
forall p : P, hull d p -> exists t, (t \in tr) /\ (in_triangle_w_edges t p).

Definition covers_vertices (tr : {fset T}) (d : {fset P}) :=
forall p : P, p \in d <-> exists t, (t \in tr) /\ (p \in vertex_set t).

Definition triangles_nempty (tr : {fset T}) :=
  forall t : T, t \in tr -> exists p, in_triangle t p.

Definition no_cover_intersection (tr : {fset T}) (d : {fset P}) :=
  forall t1, forall t2, t1 \in tr -> t2 \in tr ->  
  forall p, in_triangle t1 p -> in_triangle t2 p -> t1 = t2.

Definition regular (Ts:{fset T})  := forall t1 , forall t2,
      t1 \in Ts -> t2 \in Ts ->
      forall p, p \in vertex_set t1-> in_circle_triangle p t2 -> false.

Definition no_point_on_segment (tr : {fset T}) (d : {fset P}) :=
  forall t1, forall t2,t1 \in tr -> t2 \in tr -> forall p, p \in vertex_set t1 ->
  in_triangle_w_edges t2 p -> p \in vertex_set t2.

Definition triangle_3vertices_tr (tr:{fset T}) := forall t:T, t \in tr -> injective (vertex t).

Definition edge_disjoint_triangles (tr:{fset T}) :=
  forall t1:T, t1 \in tr -> forall e :E, e \in edges_set t1 -> forall p, on_edge e p ->
  forall t2:T, t2 \in tr -> ~(in_triangle t2 p).

Definition oriented_triangle_triangulation (tr:{fset T}) :=
  forall t:T, t \in tr -> oriented_triangle_strict t.

Definition triangulation tr d := triangle_3vertices_tr tr /\ covers_hull tr d /\ covers_vertices tr d /\
                                 no_cover_intersection tr d /\ no_point_on_segment tr d /\
                                 triangles_nempty tr /\ oriented_triangle_triangulation tr. 

Definition delaunay tr d := triangulation tr d /\ regular tr.

Definition split_triangle_aux t p :=
  let p1 := vertex1 t in
  let p2 := vertex2 t in
  let p3 := vertex3 t in
  let t1 := vertices_to_triangle p1 p2 p in
  let t2 := vertices_to_triangle p p2 p3 in
  let t3 := vertices_to_triangle p1 p p3 in
  t1 |` (t2 |` [fset t3]).


Hypothesis is_left_of_trans : forall a b c d q, is_left_of a b c ->
                                           is_left_of a b d ->
                                           is_left_of a b q ->
                                           is_left_of q b d ->
                                           is_left_of d b c ->
                                           is_left_of q b c.

Hypothesis is_left_of_mix_trans : forall a b c d q, is_left_or_on_line a b c ->
                                           is_left_or_on_line a b d ->
                                           is_left_or_on_line a b q ->
                                           is_left_of q b d ->
                                           is_left_of d b c ->
                                           is_left_of q b c.

Hypothesis is_left_or_line_trans : forall a b c d q, is_left_or_on_line a b c ->
                                           is_left_or_on_line a b d ->
                                           is_left_or_on_line a b q ->
                                           is_left_or_on_line q b d ->
                                           is_left_or_on_line d b c ->
                                           is_left_or_on_line q b c.

Hypothesis is_left_of_trans2 : forall a b c d q, is_left_of c b a ->
                                           is_left_of d b a ->
                                           is_left_of q b a ->
                                           is_left_of d b q ->
                                           is_left_of c b d ->
                                           is_left_of c b q.

(*Hypothesis is_left_of_mix_trans2 : forall a b c d q, is_left_or_on_line c b a ->
                                           is_left_or_on_line d b a ->
                                           is_left_or_on_line q b a ->
                                           is_left_of d b q ->
                                           is_left_of c b d ->
                                           is_left_of c b q.*)

Hypothesis is_left_or_line_trans2 : forall a b c d q, is_left_or_on_line c b a ->
                                           is_left_or_on_line d b a ->
                                           is_left_or_on_line q b a ->
                                           is_left_or_on_line d b q ->
                                           is_left_or_on_line c b d ->
                                           is_left_or_on_line c b q.



Definition split_triangle tr t p := (split_triangle_aux t p ) `|` (tr `\ t).


Open Scope ring_scope.


Lemma vertex1_vertices_to_triangle p1 p2 p3 :
  is_left_of p1 p2 p3 -> vertex1 (vertices_to_triangle p1 p2 p3) = p1.
Proof.
  move => p123.
  rewrite /vertex1.
assert (p123' : is_left_or_on_line p1 p2 p3).
  by apply: is_lof_imply_is_lor_on_line.
by case: (vertices_to_triangle_correct p123') => <- [_ _].
Qed.

Lemma vertex2_vertices_to_triangle p1 p2 p3 :
  is_left_of p1 p2 p3 -> vertex2 (vertices_to_triangle p1 p2 p3) = p2.
Proof.
move => p123.
rewrite /vertex2.
assert (p123' : is_left_or_on_line p1 p2 p3).
  by apply: is_lof_imply_is_lor_on_line.
by case: (vertices_to_triangle_correct p123') => _ [<- _].
Qed.

Lemma vertex3_vertices_to_triangle p1 p2 p3 :
  is_left_of p1 p2 p3 -> vertex3 (vertices_to_triangle p1 p2 p3) = p3.
Proof.
move => p123.
rewrite /vertex3.
assert (p123' : is_left_or_on_line p1 p2 p3).
  by apply: is_lof_imply_is_lor_on_line.
by case: (vertices_to_triangle_correct p123') => _ [_ <-].
Qed.

Lemma three_triangles_cover_one t p :
in_triangle t p ->forall p0, in_triangle_w_edges t p0 <-> 
                       exists t1, (t1 \in split_triangle_aux t p) 
                             /\ (in_triangle_w_edges t1 p0).
Proof.
move => intp;move:(intp) => /andP [] /andP [] v12p vp23 v1p3 q.
have v12p' := is_lof_imply_is_lor_on_line v12p.
have vp23' := is_lof_imply_is_lor_on_line vp23.
have v1p3' := is_lof_imply_is_lor_on_line v1p3.
split.
  move => /andP [] /andP [] v12q vq23 v1q3.
  rewrite /split_triangle_aux.
  case c1 :(is_left_or_on_line (vertex1 t) p q).
    case c3 :(is_left_or_on_line q p (vertex3 t)).
    have vc1p3:=vertices_to_triangle_correct v1p3'.
    move:vc1p3 => [v1t [vp v3t]].    
    exists (vertices_to_triangle (vertex1 t) p (vertex3 t));split;
      first apply /fset1UP.
        by right;apply/fset2P;right.
      by rewrite /in_triangle_w_edges;apply/andP;split;try (apply/andP;split);
      rewrite /vertex1 /vertex2 /vertex3;
      try rewrite -!vp;
      try rewrite -!v1t;
      try rewrite -!v3t.
    case c2 :(is_left_or_on_line p (vertex2 t) q).
      exists(vertices_to_triangle p (vertex2 t) (vertex3 t)).
      have vcp23:=vertices_to_triangle_correct vp23'.
       move:vcp23 => [vp [v2t v3t]].  
      split;first apply/fset1UP;try (by right;apply/fset2P;left).
      rewrite /in_triangle_w_edges /vertex1 /vertex2 /vertex3 -!vp -!v2t -!v3t.
      apply/andP;split;try(apply/andP;split) => //=.
      move:c3 => /negP /negP c3.
      by apply is_left_or_on_line_change1 in c3.
    move:c2;rewrite /is_left_or_on_line => /negP /negP;rewrite -ltrNge.
    rewrite oriented_surface_change1 oriented_surface_circular ltr_oppl oppr0.
    move => c2.
    move:c3;rewrite /is_left_or_on_line => /negP /negP;rewrite -ltrNge.
    rewrite oriented_surface_change1 -oriented_surface_circular ltr_oppl oppr0.
    move => c3.
    apply is_lof_imply_is_lor_on_line in c2.
    apply is_lof_imply_is_lor_on_line in c3.
    have islor1 : is_left_or_on_line (vertex3 t) q (vertex1 t).
      apply (@is_left_or_line_trans p q (vertex1 t) (vertex2 t) (vertex3 t));easygeo.
    have abs1 : is_on_line (vertex3 t) q (vertex1 t).
      rewrite /is_on_line;apply/eqP; symmetry;apply/eqP;rewrite eqr_le.
      rewrite /is_left_or_on_line in islor1.
      apply/andP;split => //=.
      by rewrite /is_left_or_on_line oriented_surface_change1 ler_oppr
              -oriented_surface_circular oppr0 in v1q3.
    have islor2 : is_left_or_on_line (vertex2 t) q (vertex3 t).
      apply (@is_left_or_line_trans p q (vertex3 t) (vertex1 t) (vertex2 t));easygeo.
    have abs2 :is_on_line (vertex2 t) q (vertex3 t) .
      rewrite /is_on_line;apply/eqP; symmetry;apply/eqP;rewrite eqr_le.
      rewrite /is_left_or_on_line  in islor2.
      apply/andP;split => //=.
      by rewrite /is_left_or_on_line oriented_surface_change1 ler_oppr
              oriented_surface_circular oppr0 in vq23.
    rewrite is_on_line_sym is_on_line_circular in abs2.
    case t3q : (vertex3 t == q).
      exists (vertices_to_triangle (vertex1 t) p (vertex3 t)).
      split; first by rewrite !inE eqxx !orbT.
      apply vert_in_triangle_w_edges.
        move/andP: intp => [_ it]; rewrite /oriented_triangle.
        rewrite vertex1_vertices_to_triangle // vertex3_vertices_to_triangle //.
        by rewrite vertex2_vertices_to_triangle.
      move: (@vertices_to_triangle_correct2
                    (vertex1 t) p (vertex3 t) _ (erefl _)).
      by rewrite (eqP t3q); move => [_ [_ it]].
    have abs := is_on_line_trans (negbT t3q) abs1 abs2.
    move:abs;rewrite /is_on_line - oriented_surface_circular => /eqP abs.
    have tne := triangle_not_empty intp.
    by rewrite /oriented_triangle_strict abs ltrr in tne.
  move:c1;rewrite /is_left_or_on_line => /negP /negP;rewrite -ltrNge.
  rewrite oriented_surface_change1 -oriented_surface_circular ltr_oppl oppr0.
  move => c1.
  case c2:(is_left_or_on_line q (vertex2 t) p).
    have vc12p:=vertices_to_triangle_correct v12p'.
    move:vc12p => [v1t [v2t vp]].  
    exists (vertices_to_triangle (vertex1 t) (vertex2 t) p);split;first by apply /fset1UP;left.
    rewrite /in_triangle_w_edges;apply/andP;split;try (apply/andP;split);
    rewrite /vertex1 /vertex2 /vertex3;
    try rewrite -!vp;
    try rewrite -!v1t;
    try rewrite -!v2t=> //=.
    rewrite oriented_surface_circular in c1.
    by apply is_lof_imply_is_lor_on_line in c1.
    move:c2;rewrite /is_left_or_on_line => /negP /negP;rewrite -ltrNge.
    rewrite oriented_surface_change1 -oriented_surface_circular ltr_oppl oppr0.
    move => c2.
    case c3 :(is_left_or_on_line p q (vertex3 t)).
      have vcp23:=vertices_to_triangle_correct vp23'.
      move:vcp23 => [vp [v2t v3t]].  
      exists(vertices_to_triangle p (vertex2 t) (vertex3 t));split;
        first by apply /fset1UP;right;apply/fset2P;left.
    by rewrite /in_triangle_w_edges;apply/andP;split;try (apply/andP;split);
    rewrite /vertex1 /vertex2 /vertex3;
    try rewrite -!vp;
    try rewrite -!v3t;
    try rewrite -!v2t;
    try apply is_lof_imply_is_lor_on_line in c2.
  move:c3;rewrite /is_left_or_on_line => /negP /negP;
  rewrite -ltrNge oriented_surface_change1 ltr_oppl oppr0 => c3.
  have islor1:is_left_or_on_line (vertex3 t) q (vertex1 t).
    apply:(@is_left_or_line_trans2 p q (vertex3 t) (vertex2 t) (vertex1 t));easygeo.
  have islor2:is_left_or_on_line (vertex2 t) q (vertex3 t).
    apply:(@is_left_or_line_trans2 p q (vertex2 t) (vertex1 t) (vertex3 t));easygeo.
  have abs1 : is_on_line (vertex3 t) q (vertex1 t).
      rewrite /is_on_line;apply/eqP; symmetry;apply/eqP;rewrite eqr_le.
      rewrite /is_left_or_on_line in islor1.
      apply/andP;split => //=.
      by rewrite /is_left_or_on_line oriented_surface_change1 ler_oppr
              -oriented_surface_circular oppr0 in v1q3.
  have abs2 :is_on_line (vertex2 t) q (vertex3 t) .
      rewrite /is_on_line;apply/eqP; symmetry;apply/eqP;rewrite eqr_le.
      rewrite /is_left_or_on_line  in islor2.
      apply/andP;split => //=.
      by rewrite /is_left_or_on_line oriented_surface_change1 ler_oppr
              oriented_surface_circular oppr0 in vq23.
  rewrite is_on_line_sym is_on_line_circular in abs2.
  case t3q : (vertex3 t == q).
    exists (vertices_to_triangle (vertex1 t) p (vertex3 t)).
    split; first by rewrite !inE eqxx !orbT.
    apply vert_in_triangle_w_edges.
      move/andP: intp => [_ it]; rewrite /oriented_triangle.
      rewrite vertex1_vertices_to_triangle // vertex3_vertices_to_triangle //.
      by rewrite vertex2_vertices_to_triangle.
    move: (@vertices_to_triangle_correct2
                  (vertex1 t) p (vertex3 t) _ (erefl _)).
    by rewrite (eqP t3q); move => [_ [_ it]].
  have abs := is_on_line_trans (negbT t3q) abs1 abs2.
  move:abs;rewrite /is_on_line - oriented_surface_circular => /eqP abs.
  have tne := triangle_not_empty intp.
  by rewrite /oriented_triangle_strict abs ltrr in tne.
have ve12p := vertices_to_triangle_correct v12p'.
rewrite /vertex1 /vertex2 /vertex3 in v12p'.
move:ve12p => [v112p [v212p v312p]].
have vep23 := vertices_to_triangle_correct vp23'.
rewrite /vertex1 /vertex2 /vertex3 in vp23'.
move:vep23 => [v1p23 [v2p23 v3p23]].
have ve1p3 := vertices_to_triangle_correct v1p3'.
rewrite /vertex1 /vertex2 /vertex3 in v1p3'.
move:ve1p3 => [v11p3 [v21p3 v31p3]].
move => [t1 []] => /fset1UP [|/fset2P []] -> /andP [] /andP [];
rewrite /vertex1 /vertex2 /vertex3;
[rewrite -v112p -v212p -v312p|rewrite -v1p23 -v2p23 -v3p23|
rewrite -v11p3 -v21p3 -v31p3] => islor1 islor2 islor3;
rewrite /in_triangle_w_edges;apply/andP;split;try (apply/andP;split) => //=;
move:(intp) => /andP [] /andP [] /is_lof_imply_is_lor_on_line islof12p;
have islor123 :=(is_lof_imply_is_lor_on_line (triangle_not_empty intp));
move:(islor123);rewrite is_left_or_on_line_circular => islor312;
move:(islor123);rewrite -is_left_or_on_line_circular => islor231;
move => /is_lof_imply_is_lor_on_line islofp23 /is_lof_imply_is_lor_on_line islof1p3;easygeo.
          by apply:(is_left_or_line_trans islor123 islof12p islor1).
        rewrite is_left_or_on_line_circular.
        rewrite is_left_or_on_line_circular in islof12p.
        by apply:(is_left_or_line_trans2 islor312 islof12p);easygeo.
      by apply:(is_left_or_line_trans2 islor123 islofp23);easygeo.
    rewrite -is_left_or_on_line_circular.
    rewrite -is_left_or_on_line_circular in islofp23.
    by apply: (is_left_or_line_trans islor231 islofp23);easygeo.
  rewrite is_left_or_on_line_circular in islof1p3.
  rewrite is_left_or_on_line_circular.
  by apply:(is_left_or_line_trans islor312 islof1p3);easygeo.
rewrite -is_left_or_on_line_circular.
rewrite -is_left_or_on_line_circular in islof1p3.
by apply:(is_left_or_line_trans2 islor231 islof1p3);easygeo.
Qed.

Lemma split_aux_in_triangle t p :
in_triangle t p -> forall t1, t1 \in split_triangle_aux t p 
                            -> forall q, in_triangle t1 q -> in_triangle t q.
Proof.
move => intp; move:(intp) => /andP [] /andP [] islo12p islop23 islo1p3 t1.
have islor12p := is_lof_imply_is_lor_on_line islo12p.
have islorp23 := is_lof_imply_is_lor_on_line islop23.
have islor1p3 := is_lof_imply_is_lor_on_line islo1p3.
have oriented_abc := triangle_not_empty intp.
rewrite /oriented_triangle_strict in oriented_abc.
move => /fset1UP [|/fset2P []] ->q /andP [] /andP [];
[have vc := vertices_to_triangle_correct islor12p|
have vc := vertices_to_triangle_correct islorp23|
have vc := vertices_to_triangle_correct islor1p3];
move:vc => [v1 [v2 v3]];rewrite /vertex1 /vertex2 /vertex3;
(try rewrite -v1);(try rewrite -v2);(try rewrite -v3) => islof1 islof2 islo3;
rewrite /in_triangle;apply/andP;split;try (apply/andP;split);easygeo;
[apply:(@is_left_of_trans (vertex1 t) (vertex2 t) (vertex3 t) p q);easygeo|
rewrite is_left_of_circular;
apply:(@is_left_of_trans2 (vertex2 t) (vertex1 t) (vertex3 t) p q);easygeo|
apply:(@is_left_of_trans2 (vertex3 t) (vertex2 t) (vertex1 t) p q);easygeo|
rewrite -is_left_of_circular;
apply:(@is_left_of_trans (vertex2 t) (vertex3 t) (vertex1 t) p q);easygeo|
rewrite is_left_of_circular;
apply:(@is_left_of_trans (vertex3 t) (vertex1 t) (vertex2 t) p q);easygeo|
rewrite -is_left_of_circular;
apply:(@is_left_of_trans2 (vertex1 t) (vertex3 t) (vertex2 t) p q);easygeo].
Qed.

Lemma ord30_inj : forall (j : (0 < 3)%N), Ordinal j = ord30.
Proof. by move => j; apply/val_inj. Qed.

Lemma ord31_inj : forall (j : (1 < 3)%N), Ordinal j = ord31.
Proof. by move => j; apply/val_inj. Qed.

Lemma ord32_inj : forall (j : (2 < 3)%N), Ordinal j = ord32.
Proof. by move => j; apply/val_inj. Qed.

Lemma ord30p1 : ord30 + 1 = ord31.
Proof. by apply/val_inj. Qed.

Lemma ord31p1 : ord31 + 1 = ord32.
Proof. by apply/val_inj. Qed.

Lemma ord32p1 : ord32 + 1 = ord30.
Proof. by apply/val_inj. Qed.

Lemma ord30p2 : ord30 + 2%:R = ord32.
Proof. by apply/val_inj. Qed.

Lemma ord31p2 : ord31 + 2%:R = ord30.
Proof. by apply/val_inj. Qed.

Lemma ord32p2 : ord32 + 2%:R = ord31.
Proof. by apply/val_inj. Qed.

Lemma add3K (x : 'I_3) : x + 1 + 1 + 1 = x.
Proof. by rewrite -!addrA (_ : 1 + (1 + 1) = 0) ?addr0 //; apply/val_inj. Qed.

Definition mod3rules :=
  (ord30_inj, (ord31_inj, (ord32_inj, (ord30p1, (ord31p1, (ord32p1, (ord30p2,
   (ord31p2, (ord32p2, add3K))))))))).

Lemma on_edge_split_triangle t p :
  in_triangle t p -> forall t0, t0 \in split_triangle_aux t p ->
  forall e, e \in edges_set t0 -> forall q, on_edge e q ->
      (in_triangle t q \/ (exists e0, e0 \in edges_set t /\ on_edge e0 q)).
Proof.
move => intp t'.
have otst : oriented_triangle_strict t by apply: triangle_not_empty intp.
have eq_to_imp (a b : bool) : a = b -> a -> b by move ->.
have step x y z := eq_to_imp _ _ (is_left_of_circular x y z).
have step' x y z := eq_to_imp _ _ (Logic.eq_sym (is_left_of_circular x y z)).
case/andP: (intp) => /andP [/step o1 o2] /step' o3 t'split.
have lofpj : forall j, is_left_of p (vertex t j) (vertex t (j + 1)).
  by case => [ [ | [ | [ | j]]] pj] //; rewrite ?mod3rules.
have lofj : forall j, is_left_of (vertex t j) (vertex t (j + 1))
              (vertex t (j + 2%:R)).
  by move => [[ | [ | [ | j]]] pj] //; rewrite !mod3rules //
       is_left_of_circular // is_left_of_circular.
have edge_to_triangle : forall j,
   forall q, on_edge (vertices_to_edge (vertex t j) p) q -> in_triangle t q.
  move => j q qe.
  rewrite /in_triangle (is_left_of_circular _ _ q) -(is_left_of_circular q).
  case: (on_edge_on_line (step' _ _ _ (lofpj j)) qe) => _.
  rewrite !(is_left_of_circular _ _ q) => [][A B].
  have lofpjp1 : is_left_of p (vertex t (j + 1)) (vertex t (j + 2%:R)).
    by rewrite addrA.
  have qj1j2 := is_left_of_trans (lofj j) (step' _ _ _ (lofpj j))
      (step' _ _ _ A) B lofpjp1.
  have := (on_edge_on_line (lofpj (j + 2%:R))).
  rewrite vertices_to_edge_sym !addrA mod3rules.
  move/(_ _ qe) => [] _ [] A' /step B'.
  case: j A B' qj1j2 {qe B lofpjp1 A'} => [[ | [ | [ | j]]] pj] //;
  by rewrite !mod3rules => -> -> ->.
move => e et'.
have [j pj] :
   exists j, e = vertices_to_edge (vertex t j) (vertex t (j + 1)) \/
                     e = vertices_to_edge (vertex t j) p.
  have tmp := (step _ _ _ o3).
  by move: t'split et'; rewrite !inE => /orP [/eqP -> | /orP [/eqP -> | /eqP ->]];
  rewrite edges_set_vertices_to_triangle // ?(vertices_to_edge_sym p)
  ?(vertices_to_edge_sym (vertex2 t) (vertex1 t))
  ?(vertices_to_edge_sym (vertex3 t) (vertex2 t))
  ?(vertices_to_edge_sym (vertex1 t) (vertex3 t)) ?inE;
  try (case /orP => [/orP [/eqP -> |/eqP -> ] | /eqP ->];
  rewrite /vertex1 /vertex2 /vertex3;
  try match goal with |- context[vertices_to_edge (vertex t ?x) _ = _] =>
     exists x; rewrite !mod3rules; auto
  end); apply/step'.
case: pj => [pjt | -> ]; last by move => q /edge_to_triangle; left.
move => q qe; right; exists e; split; last by [].
rewrite (all_triangles_oriented otst) edges_set_vertices_to_triangle //.
rewrite (vertices_to_edge_sym (vertex1 t) (vertex3 t)) !inE /vertex1 /vertex2
  /vertex3 pjt {pjt}.
by case: j => [[ | [ | [ | j]]] pj] //; rewrite !mod3rules eqxx ?orbT.
Qed.

Lemma split_triangle_aux_oriented t p:
in_triangle t p -> forall t1, t1 \in split_triangle_aux t p ->
                               oriented_triangle_strict t1.
move => intp t1.
move:intp => /andP [] /andP [] islof1 islof2 islof3.
by rewrite /split_triangle_aux => /fset1UP [-> | /fset2P [] ->];
rewrite /oriented_triangle_strict;
[have vc := vertices_to_triangle_correct (is_lof_imply_is_lor_on_line islof1)|
have vc := vertices_to_triangle_correct (is_lof_imply_is_lor_on_line islof2)|
have vc := vertices_to_triangle_correct (is_lof_imply_is_lor_on_line islof3)];
move:vc => [vc1 [vc2 vc3]];rewrite /vertex1 /vertex2 /vertex3 -vc1 -vc2 -vc3.
Qed.

Lemma split_aux_in_triangle_we t p:
 in_triangle t p -> forall t1, t1 \in split_triangle_aux t p 
                 -> forall q, in_triangle_w_edges t1 q 
                 ->      in_triangle_w_edges t q.
move => intp t1 t1_spl q.
rewrite in_triangle_w_edge_edges.
have or_t := triangle_not_empty intp.
move => [q_t1 | [int1q|e_t1]];last first.
    move :e_t1 => [e [e_t1 e_q]].
    have test :=on_edge_split_triangle intp t1_spl e_t1 e_q.
    rewrite (in_triangle_w_edge_edges or_t).
    move:test => [|];first by move => ->;right; left.
    by right;right.
  rewrite (in_triangle_w_edge_edges or_t);right;left.
  by apply:(split_aux_in_triangle intp t1_spl int1q).
move:q_t1;move:t1_spl => /fset1UP [|/fset2P []] ->;
rewrite vertex_set_vertices_to_triangle => /fsetUP [/fset2P[]|/fset1P] ->;
rewrite (in_triangle_w_edge_edges or_t);
[left|left|right;left|right;left|left|left|left|right;left|left] => //=;
apply/imfsetP;[exists ord30|exists ord31|exists ord31|exists ord32|exists ord30|exists ord32] => //=.
by apply:(split_triangle_aux_oriented intp).
Qed.


Hypothesis surface_non_empty : forall p1 p2 p3,
  oriented_surface p1 p2 p3 > 0 -> 
  exists p', in_triangle (vertices_to_triangle p1 p2 p3) p'.




Lemma vertex_in_split_triangle t p:
in_triangle t p -> forall t0, t0 \in split_triangle_aux t p ->
forall q, q \in vertex_set t0 -> (q \in vertex_set t \/ q=p).
move => intp t0 t0_spl q qvt0.
move:t0_spl => /fset1UP.
move=>[H|/fset2P [H|H]].
    have t_oriented : is_left_or_on_line (vertex1 t) (vertex2 t) p.
      move:(intp) => /andP [/andP [islo12p _] _].
      by apply is_lof_imply_is_lor_on_line in islo12p.
    have vertex_disj := vertices_to_triangle_correct t_oriented.
    move:vertex_disj => [v1t [v2t vp]].
    move:qvt0=>/imfsetP [[[|[|[|x']]] px] _] qvt0x=>//=;
    [pose ordx:=ord30|pose ordx:=ord31|pose ordx:=ord32];
    have temp:q = vertex t0 ordx
      by rewrite qvt0x;congr ((vertex t0) _);apply ord_inj.
        rewrite H -v1t in temp;left;apply/imfsetP;exists ord30=>//=.
      rewrite H -v2t in temp;left;apply/imfsetP;exists ord31=>//=.
    by rewrite H -vp in temp;right.
  have t_oriented : is_left_or_on_line p (vertex2 t) (vertex3 t).
    move:intp => /andP [/andP [_ islop23] _].
    by apply is_lof_imply_is_lor_on_line in islop23.
  have vertex_disj := vertices_to_triangle_correct t_oriented.
  move:vertex_disj => [vp [v2t v3t]].
  move:qvt0=>/imfsetP [[[|[|[|x']]] px] _] qvt0x=>//=;
           [pose ordx:=ord30|pose ordx:=ord31|pose ordx:=ord32];
    have temp:q = vertex t0 ordx
    by rewrite qvt0x;congr ((vertex t0) _);apply ord_inj.
      by rewrite H -vp in temp;right.
    by rewrite H -v2t in temp;left;apply/imfsetP;exists ord31.
  by rewrite H -v3t in temp;left;apply/imfsetP;exists ord32.
have t_oriented : is_left_or_on_line (vertex1 t) p (vertex3 t).
  move:intp => /andP [_ islo1p3]. 
  by apply is_lof_imply_is_lor_on_line in islo1p3.
have vertex_disj := vertices_to_triangle_correct t_oriented.
move:vertex_disj => [v1t [vp v3t]].
move:qvt0=>/imfsetP [[[|[|[|x']]] px] _] qvt0x=>//=;
         [pose ordx:=ord30|pose ordx:=ord31|pose ordx:=ord32];
  have temp:q = vertex t0 ordx
  by rewrite qvt0x;congr ((vertex t0) _);apply ord_inj.
    by rewrite H -v1t in temp;left;apply/imfsetP;exists ord30.
  by rewrite H -vp in temp;right.
by rewrite H -v3t in temp;left;apply/imfsetP;exists ord32.
Qed.



Lemma hull_add_point p d q: p \notin d -> hull d p ->
   hull (p |` d ) q -> hull d q.
Proof.
move => npd [b [b_x [b_y [bsum [bpos dne]]]]] [a [a_x [a_y [asum [apos _]]]]].
have dpd : d `<=` (p |` d) by exact: fsubsetU1.
have ppd : [fset p] `<=` (p |` d) by exact: fsubsetUl.
have pp : p \in [fset p] by exact:fset11.
case /fset0Pn : (dne) => p1 p1_in_d.
set p' := FSetSub (fset1U1 p d).
pose c := (fun (i : d) => (a (fincl dpd i)) + (a p') * (b i)).
have cpos : forall i, 0 <= c i.
  by   move => i; apply: addr_ge0 => //; apply: mulr_ge0.  
set h := fun i => fincl dpd i.
(* maybe start of useless part. *)
have codomh_np': {subset codom h <= [pred i | i != p']}.
  move => j /codomP [w Pw]; rewrite Pw.
  apply/negP => /eqP jeqp'; case /negP: npd.
  by rewrite -[p]/(val p') -jeqp' {Pw jeqp'}; case: w.
(* end of potentially useless part. *)
have np'_codomh: {subset [pred i | i != p'] <= codom h}.
  move => [j Pj]; case/fset1UP: (Pj).
    move => abs.  move : Pj. rewrite abs => Pp.
    by case/negP; apply/eqP; apply /val_inj.
  by move => jd _;  apply/codomP; exists [` jd ]; apply /val_inj.
have bijh : {on [pred i | i != p'], bijective h}.
  apply/(subon_bij np'_codomh)/bij_on_codom; last by exact: [` p1_in_d].
  by exact: fincl_inj.
have reindex_h: xpredT =1 (fun x => h x != p').
  move => [j pj]; symmetry; apply/negP => /eqP abs.
  by case: npd; rewrite -[p]/(val p') -abs /= pj.
  pose c' := fun i : p |` d => c (insubd [` p1_in_d] (val i)).
  have fun_d_p_coord : forall f,  f p == \sum_i b i * f (val i) ->
                             f q == \sum_i a i * f (val i) ->
                             f q == \sum_i c i * f (val i).



move => f f_b f_a.  

  rewrite (eq_big _ (fun i : d => c' (h i) * f (val (h i))) (reindex_h));
    first last.
    move => i _; rewrite /c'.
    case hv : (h i == p').
      by case/negP: npd; rewrite -[p]/(val p') -(eqP hv) {hv}; case: i.
    congr (c _ * _).
    by apply/val_inj; rewrite val_insubd /= {hv}; case: i  => /= i' ->.
  set F := fun i => c' i * f (val i).
  rewrite -(@reindex _ _ _ _ _ h (fun x => x != p') F) /F /c' /c {F c' cpos c}
   //=.
  rewrite (eq_bigr
             (fun i => a (fincl dpd (insubd [` p1_in_d] (val i))) *
                f (val i) +
                a p' * (b (insubd [` p1_in_d] (val i)) *
                f (val i)))); last by move => i inp; rewrite mulrDl mulrA.
  rewrite big_split /= addrC -(big_distrr (a p')) /=.
  set vp := (X in _ == _ * X + _).
  have vp_eq : vp = f p.
    rewrite (eqP f_b).
    rewrite (eq_big _ (fun i : d => b (insubd [` p1_in_d] (val (h i))) *
               f(val (h i))) (reindex_h)); first last.
      move => [i ip] _ /=; congr (b _ * _).
      by  apply /val_inj; rewrite val_insubd ip.
    by apply: reindex.
  rewrite vp_eq (eqP f_a) (bigD1 p') //=; apply/eqP; congr (_ + _).
  apply: eq_bigr; move => [i ip] inp; congr (a _ * _); rewrite /=.
  apply val_inj => /=; rewrite val_insubd.
  case/fset1UP: (ip); last by move => ->.
  by move => abs; case/negP: inp; apply/eqP/val_inj => /=.
exists c; split; first by apply:fun_d_p_coord.
split; first by apply:fun_d_p_coord.
split.
  rewrite big_split /= addrC -big_distrr /= (eqP bsum) mulr1.
  rewrite (eq_big (fun i => true && (h i != p'))(fun i => a (h i))(reindex_h));
    last by [].
  rewrite -(@reindex _ _ _ _ _ h (fun x => x != p') a bijh).
  rewrite -(@bigD1 _ _ _ _ _ xpredT) //.

split;last by [].
move => i.
rewrite /c.
apply:addr_ge0 => //=.
by apply:mulr_ge0 => //=.
Qed.

                                                                   
                                           

(* Remarque Yves: la solution pour a est :
    a i = oriented_surface (vertex t (i.+1 mod 3)) (vertex t (i.+2 mod 3)) p /
          oriented_surface (vertex t 0) (vertex t 1) (vertex t 2) *)
Hypothesis in_triangle_barycentre : forall t, forall p, in_triangle_w_edges t p <-> 
              exists a : 'I_3 -> R, ((forall i, (a i) >= 0%R) /\ \sum_i a i = 1 /\
              xCoord p = \sum_i ((a i)*xCoord (vertex t i)) /\
              yCoord p = \sum_i ((a i)*yCoord (vertex t i))). 


Lemma hull_from_triangle d tr t p:
  d != fset0 -> triangulation tr d -> t \in tr -> in_triangle t p -> hull d p.
Proof.
move => dne tr_d t_tr intp.
move:tr_d =>[tr3v [covh_tr_d [covv_tr_d nps_tr_d]]].   
have inwetp : in_triangle_w_edges t p by apply:in_triangle_imply_w_edges.
move:inwetp => /in_triangle_barycentre [a [apos [aun [a_x a_y]]]].
have fun_sum_ord3 : forall f, \sum_i ((a i)*(f (vertex t i))) =
                         (a ord30)*(f (vertex t ord30))+
                         (a ord31)*(f (vertex t ord31))+
                         (a ord32)*(f (vertex t ord32)).
  move => f. 
  rewrite (bigD1 ord30) => //=.
  rewrite (bigD1 ord31) => //=.
  rewrite (bigD1 ord32) => //=.
  have H: (forall i, ((i != ord30) && (i != ord31) && (i != ord32) -> false)).
  move =>i cond.
  case test0:(i==ord30);case test1:(i==ord31);case test2:(i==ord32) => //=;
  rewrite test0 in cond;rewrite test1 in cond; rewrite test2 in cond => //=.
  have imply_ord : (forall i, (i != ord30) -> (i != ord31) -> (i = ord32))
    by move => [[|[|[|j]]] pi]; move => * //=; apply val_inj.
  have abs : (i=ord32).
  apply imply_ord; apply /negP; first by rewrite test0;last move.
    by rewrite test1.
  by rewrite abs in test2.
  rewrite (eq_bigl (fun i => false ));last by move =>i;
  case abs:((i != ord30) && (i != ord31) && (i != ord32)); first apply H in abs. 
  rewrite big_pred0_eq.
  rewrite addr0.
  by rewrite addrA.
have vert_t_i :forall i, vertex t i \in d.
  move =>i;apply covv_tr_d;exists t;split;move => //=.
   by rewrite /vertex_set; apply:in_imfset.
have vert_0_d : vertex t ord30 \in d by apply vert_t_i.
have vert_1_d : vertex t ord31 \in d by apply vert_t_i.
have vert_2_d : vertex t ord32 \in d by apply vert_t_i.
have not_2_1 : ([` vert_2_d] != [` vert_1_d]).
  case abs:([` vert_2_d] == [` vert_1_d])=> //=.
  move:abs => /eqP abs.
  have abs2:(val [` vert_2_d] = val [` vert_1_d]) by rewrite abs.
  have injvt: (injective (vertex t)) by apply tr3v.
  by move:abs2 => /= abs2; apply injvt in abs2.   
have not_2_0 : ([` vert_2_d] != [` vert_0_d]).
  case abs:([` vert_2_d] == [` vert_0_d])=> //=.
  move:abs => /eqP abs.
  have abs2:(val [` vert_2_d] = val [` vert_0_d]) by rewrite abs.
  have injvt: (injective (vertex t)) by apply tr3v.
  by move:abs2 => /= abs2; apply injvt in abs2.
have not_1_0 : ([` vert_1_d] != [` vert_0_d]).
  case abs:([` vert_1_d] == [` vert_0_d])=> //=.
  move:abs => /eqP abs.
  have abs2:(val [` vert_1_d] = val [` vert_0_d]) by rewrite abs.
  have injvt: (injective (vertex t)) by apply tr3v.
  by move:abs2 => /= abs2; apply injvt in abs2.   
rewrite fun_sum_ord3 in a_x;rewrite fun_sum_ord3 in a_y; move :fun_sum_ord3 =>_.
pose a' : d -> R := fun i => (if i ==  [`vert_0_d] then a ord30 else
                              if i == [`vert_1_d] then a ord31 else
                                   if i == [`vert_2_d] then a ord32 else 0).
exists a'.
have a'0 : a' [`vert_0_d] = a ord30 by rewrite /a' => /=; rewrite eq_refl.
have a'1 : a' [`vert_1_d] = a ord31. rewrite /a' => /=.
  case abs : ([`vert_1_d] == [`vert_0_d]);last by rewrite eq_refl.
  move:abs => /eqP abs.
  have val_v01: val [` vert_1_d] = val [` vert_0_d] by rewrite abs.
  have injvt: (injective (vertex t)) by apply tr3v.
  by move:val_v01 => /= val_v01; apply injvt in val_v01.
have a'2 : a' [`vert_2_d] = a ord32. rewrite /a' => /=.
  case abs : ([`vert_2_d] == [`vert_0_d] ); move:abs => /eqP abs.
  have val_v20: val [` vert_2_d] = val [` vert_0_d] by rewrite abs.
  have injvt: (injective (vertex t)) by apply tr3v.
  by move:val_v20 => /= val_v20; apply injvt in val_v20.    
  case abs2 :([`vert_2_d] == [`vert_1_d]);last by rewrite eq_refl.
  move:abs2 => /eqP abs2.
  have injvt: (injective (vertex t)) by apply tr3v.
  have val_v21: val [` vert_2_d] = val [` vert_1_d] by rewrite abs2.
  by move:val_v21 => /= val_v21; apply injvt in val_v21.
have sum0_f : forall f, \sum_(i | (i != [` vert_0_d]) && (i != [` vert_1_d])
                                            && (i != [` vert_2_d]))
               a' i * f (fsval i) = 0.
  move => f;apply big1;move => i not_vert.
  have a'i0 : a' i = 0;first rewrite /a' => /=.
    case inv0:(i == [`vert_0_d]); rewrite inv0 in not_vert;
    case inv1:(i == [`vert_1_d]); rewrite inv1 in not_vert;
    case inv2:(i == [`vert_2_d]); rewrite inv2 in not_vert;move:not_vert=> _ //=.
  by rewrite a'i0; apply mul0r.

  have fun_sump : forall f, f p = a ord30 * f ((vertex t) ord30) + 
                             a ord31 * f ((vertex t) ord31) +
                             a ord32 * f ((vertex t) ord32) ->
                       f p == \sum_i a' i * f (val i).
  move => f f_hyp.
  rewrite (bigD1 [` vert_0_d])=> //=.
  rewrite (bigD1 [` vert_1_d])=> //=.
  rewrite  (bigD1 [` vert_2_d]) =>//=;last by rewrite not_2_1 not_2_0.        
  by rewrite  a'0 a'1 a'2 sum0_f addr0 f_hyp addrA.
split;first by apply:fun_sump.
split;first by apply:fun_sump.
have sum0 : \sum_(i | (i != [` vert_0_d]) && (i != [` vert_1_d])
                                            && (i != [` vert_2_d]))
               a' i = 0.
  apply big1;move => i not_vert.
  have a'i0 : a' i = 0;first rewrite /a' => /=.
    case inv0:(i == [`vert_0_d]); rewrite inv0 in not_vert;
    case inv1:(i == [`vert_1_d]); rewrite inv1 in not_vert;
    case inv2:(i == [`vert_2_d]); rewrite inv2 in not_vert;move:not_vert=> _ //=.
  by rewrite a'i0.
split.
  rewrite (bigD1 [` vert_0_d])=> //=.
  rewrite (bigD1 [` vert_1_d])=> //=.
  rewrite (bigD1 [` vert_2_d]) =>//=;last by rewrite not_2_1 not_2_0.        
  rewrite a'1 a'0 a'2 sum0 addr0 addrA.
  move:aun.
  rewrite (bigD1 ord30) => //=.
  rewrite (bigD1 ord31) => //=.
  rewrite (bigD1 ord32) => //=.
  have sum_0_ord : (\sum_(i < 3 | (i != ord30) && (i != ord31) && (i != ord32)) a i = 0).
    rewrite (eq_bigl (fun i => false)); first by apply big_pred0_eq.
    by move=>[[|[|[|i']]] pi].
  by rewrite sum_0_ord addrA addr0 => ->.
split;last by [].
move => i.
rewrite /a'.
case (i == [` vert_0_d]); case (i == [` vert_1_d]);
case (i == [` vert_2_d]) => //=.
Qed.


Lemma in_vertex_set p A B C:
    is_true (p \in (vertex_set (vertices_to_triangle A B C))) 
          <-> (p == A \/ p==B \/ p == C).
Proof.
rewrite vertex_set_vertices_to_triangle.
split.
  by move => /fsetUP [/fset2P [->|->]| /fset1P ->];
  [left|right;left|right;right].
by move => [/eqP -> | [/eqP -> | /eqP ->]];
apply /fsetUP;[left|left|by right;apply /fset1P];
apply/fset2P;[left|right].
Qed.

Lemma triangulation_tr3v tr t p d:
  d != fset0 -> p \notin d -> triangulation tr d -> t \in tr ->
  in_triangle t p -> triangle_3vertices_tr (split_triangle tr t p).

Proof.
move => dne p_nin_d tr_d t_tr intp.
move:(tr_d) => [tr3v [covh_tr_d [covv_tr_d [nci_tr_d nps_tr_d]]]].
move => t0 insplt0.
have vert_n_p : forall i, vertex t i != p.
  move => i.
  case abs:(vertex t i == p) => //=.
  move:abs => /eqP abs.
  have n_vtit:=(in_triangle_not_vert intp);move:n_vtit=>/negbTE;rewrite-abs=>n_vtit.
  have vtivt:(vertex t i \in vertex_set t) by apply:in_imfset.
  by rewrite n_vtit in vtivt.
have p_n_vert : forall i, p != vertex t i by move => i; rewrite eq_sym;apply vert_n_p.
move:insplt0 => /fsetUP [t0spl | t0tr];last first.
  move:t0tr => /fsetD1P [_ t0tr];by apply tr3v.

have triangle_inj_vert_to_triangle : 
forall (p:P), forall (q:P), forall (r:P), p!=q -> p!=r -> q !=r -> 
                           is_left_or_on_line p q r  ->
                           t0 = vertices_to_triangle p q r ->
                           injective (vertex t0).
move => p1 p2 p3 p12 p13 p23 t_oriented t0vert.
by move => [[|[|[|a]]] pa] [[|[|[|b]]] pb] vt0ab => //=;
try apply ord_inj=>//=;
rewrite t0vert in vt0ab;
have p123 := vertices_to_triangle_correct t_oriented;
move:p123=>[v1t [v2t v3t]];
[have ordpa : Ordinal pa =ord30|have ordpa : Ordinal pa =ord30|
have ordpa : Ordinal pa =ord31|have ordpa : Ordinal pa =ord31|
have ordpa : Ordinal pa =ord32|have ordpa : Ordinal pa =ord32];
try apply ord_inj => //=;rewrite ordpa in vt0ab;move:ordpa=> _;
[have ordpb : Ordinal pb =ord31|have ordpb : Ordinal pb =ord32|
 have ordpb : Ordinal pb =ord30|have ordpb : Ordinal pb =ord32|
 have ordpb : Ordinal pb =ord30|have ordpb : Ordinal pb =ord31];
try apply ord_inj => //=;rewrite ordpb in vt0ab;move:ordpb=> _;
[rewrite -v1t in vt0ab|rewrite -v1t in vt0ab|
 rewrite -v1t in vt0ab|rewrite -v3t in vt0ab|
 rewrite -v1t in vt0ab|rewrite -v3t in vt0ab];
[rewrite -v2t in vt0ab|rewrite -v3t in vt0ab|
 rewrite -v2t in vt0ab|rewrite -v2t in vt0ab|
 rewrite -v3t in vt0ab|rewrite -v2t in vt0ab];
[move:p12|move:p13|move:p12|move:p23|move:p13|move:p23];
 rewrite vt0ab; move => /eqP.  
move:(intp) => /andP[/andP [islo1 islo2] islo3].
apply is_lof_imply_is_lor_on_line in islo1.
apply is_lof_imply_is_lor_on_line in islo2.
apply is_lof_imply_is_lor_on_line in islo3.
move:t0spl=> /fset1UP [t0spl | t0spl];last move:t0spl=> /fset2P [t0spl|t0spl].

    move:t0spl;apply triangle_inj_vert_to_triangle;
      try apply vert_n_p;rewrite /is_left_or_on_line => //=.
    have ord301 : ord30 != ord31 by [].
    move:ord301;have tr3v_ttr := (tr3v t t_tr).
    rewrite /injective in tr3v_ttr.
    have vt01_01 := (tr3v_ttr ord30 ord31).
    apply contraNneq =>vt.
    by apply /eqP; apply vt01_01.
  move:t0spl;apply triangle_inj_vert_to_triangle;
    try apply p_n_vert;rewrite /is_left_or_on_line => //=.
  have ord312 : ord31 != ord32 by [].
  move:ord312;have injvt := (tr3v t t_tr).
  rewrite /injective in injvt.
  have ord12_12 := (injvt ord31 ord32).
  apply contraNneq =>vt.
  by apply /eqP; apply ord12_12.
move:t0spl;apply triangle_inj_vert_to_triangle;
    try apply p_n_vert;try apply vert_n_p;rewrite /is_left_or_on_line => //=.    
have ord302 : ord30 != ord32 by [].
move:ord302;have injvt := (tr3v t t_tr).
rewrite /injective in injvt.
have ord02_02 := (injvt ord30 ord32).
apply contraNneq =>vt.
by apply /eqP; apply ord02_02.
Qed.

Lemma triangulation_nci tr t p d:
  d != fset0 -> p \notin d -> triangulation tr d -> t \in tr ->
   in_triangle t p -> no_cover_intersection (split_triangle tr t p) (p |` d).
Proof.
move => dne p_nin_d tr_d t_tr intp.
move:(tr_d) => [tr3v [covh_tr_d [covv_tr_d [nci_tr_d [nps_tr_d [tne_tr_d or_tr_d]]]]]].
move => t1 t2 t1_spl t2_spl q int1q int2q.
move:t1_spl => /fsetUP;  move => [t1_spl|t1_spl];
move:t2_spl=> /fsetUP;move=>[t2_spl|t2_spl];last first.
      move:t1_spl => /fsetD1P [t1nt t1_tr].
      move:t2_spl => /fsetD1P [t2nt t2_tr].
      rewrite /no_cover_intersection in nci_tr_d.
      have nci_t1_t2:=(nci_tr_d t1 t2).
      apply:(nci_t1_t2) => //=.
      apply int1q.
      apply int2q.
    move:t1_spl => /fsetD1P [t1nt t1_tr].
    have intwet2q := (in_triangle_imply_w_edges int2q).
    have :(t2 \in split_triangle_aux t p /\ in_triangle_w_edges t2 q)=>//= _.
    have tr3c := (three_triangles_cover_one intp q).
    have intwetq : in_triangle_w_edges t q by apply tr3c;exists t2.
    rewrite /no_cover_intersection in nci_tr_d.
    have intq := (split_aux_in_triangle intp t2_spl int2q).
    have abs := (nci_tr_d t1 t t1_tr t_tr q int1q intq).
    rewrite abs in t1nt.
    by move :t1nt => /eqP.  
  move:t2_spl => /fsetD1P [t2nt t2_tr].
  have intwet1q := (in_triangle_imply_w_edges int1q).
  have :(t1 \in split_triangle_aux t p /\ in_triangle_w_edges t1 q)=>//= _.
  have tr3c := (three_triangles_cover_one intp q).
  have intwetq : in_triangle_w_edges t q by apply tr3c;exists t1.
  rewrite /no_cover_intersection in nci_tr_d.
  have intq := (split_aux_in_triangle intp t1_spl int1q).
  have abs := (nci_tr_d t2 t t2_tr t_tr q int2q intq).
  rewrite abs in t2nt.
  by move :t2nt => /eqP.  
  
case t1_t2 : (t2==t1);last move:t1_t2 => /eqP t1_n_t2.
  by move :t1_t2 => /eqP => ->.
move:(intp) => /andP [/andP [islo1 islo2] islo3].
apply is_lof_imply_is_lor_on_line in islo1.
apply is_lof_imply_is_lor_on_line in islo2.
apply is_lof_imply_is_lor_on_line in islo3.
have vc12p := vertices_to_triangle_correct islo1.
have vcp23 := vertices_to_triangle_correct islo2.
have vc1p3 := vertices_to_triangle_correct islo3.
move:islo1 islo2 islo3 => _ _ _.
move:t1_spl=> /fset1UP [vt1 |t1_spl];last move:t1_spl=> /fset2P [vt1|vt1];
move:t2_spl => /fset1UP [vt2|t2_spl];try move:t2_spl=> /fset2P [vt2|vt2];
rewrite vt1 vt2 in t1_n_t2 => //=.
          move:int1q => /andP [/andP [_ islo] _].
          rewrite -vt1 in vc12p.
          move:vc12p => [v1t1 [v2t1 v3t1]].
          rewrite /vertex2 /vertex3 -v3t1 -v2t1  in islo.
          move:int2q => /andP [/andP [islor _] _].
          rewrite -vt2 in vcp23.
          move:vcp23 => [v1t2 [v2t2 v3t2]].
          rewrite /vertex1 /vertex2 /vertex3 -v1t2 -v2t2  in islor.           
          rewrite is_left_of_change is_left_or_on_line_circular in islor.
          apply is_lof_imply_is_lor_on_line in islo.
          by rewrite islo in islor.
        move:int1q => /andP [/andP _ islo].
        rewrite -vt1 in vc12p.
        move:vc12p => [v1t1 [v2t1 v3t1]].
        rewrite /vertex1 /vertex3 -v3t1 -v1t1  in islo.
        move:int2q => /andP [/andP [islor _] _].
        rewrite -vt2 in vc1p3.
        move:vc1p3 => [v1t2 [v2t2 v3t2]].
        rewrite /vertex1 /vertex2 /vertex3 -v1t2 -v2t2  in islor.           
        rewrite is_left_of_change -is_left_or_on_line_circular in islor.
        apply is_lof_imply_is_lor_on_line in islo.
        by rewrite islo in islor.
      move:int1q => /andP [/andP [islo _] _].
      rewrite -vt1 in vcp23.
      move:vcp23 => [v1t1 [v2t1 v3t1]].
      rewrite /vertex1 /vertex2 -v1t1 -v2t1  in islo.
      move:int2q => /andP [/andP [_ islor] _].
      rewrite -vt2 in vc12p.
      move:vc12p => [v1t2 [v2t2 v3t2]].
      rewrite /vertex1 /vertex2 /vertex3 -v3t2 -v2t2  in islor.           
      rewrite is_left_of_change is_left_or_on_line_circular in islor.
      apply is_lof_imply_is_lor_on_line in islo.
      by rewrite islo in islor.
    move:int1q => /andP [/andP _ islo].
    rewrite -vt1 in vcp23.
    move:vcp23 => [v1t1 [v2t1 v3t1]].
    rewrite /vertex1 /vertex3 -v3t1 -v1t1  in islo.
    move:int2q => /andP [/andP [_ islor] _].
    rewrite -vt2 in vc1p3.
    move:vc1p3 => [v1t2 [v2t2 v3t2]].
    rewrite /vertex1 /vertex2 /vertex3 -v3t2 -v2t2  in islor.           
    rewrite is_left_of_change  in islor.
    apply is_lof_imply_is_lor_on_line in islo.
    by rewrite islo in islor.
  move:int1q => /andP [/andP [islo _] _].
  rewrite -vt1 in vc1p3.
  move:vc1p3=> [v1t1 [v2t1 v3t1]].
  rewrite /vertex1 /vertex2 /vertex3 -v2t1 -v1t1  in islo.
  move:int2q => /andP [/andP [_ _] islor].
  rewrite -vt2 in vc12p.
  move:vc12p => [v1t2 [v2t2 v3t2]].
  rewrite /vertex1 /vertex2 /vertex3 -v1t2 -v3t2  in islor.           
  rewrite is_left_of_change -is_left_or_on_line_circular in islor.
  apply is_lof_imply_is_lor_on_line in islo.
  by rewrite islo in islor.
move:int1q => /andP [/andP [_ islo] _].
rewrite -vt1 in vc1p3.
move:vc1p3 => [v1t1 [v2t1 v3t1]].
rewrite /vertex1 /vertex2 /vertex3 -v3t1 -v2t1  in islo.
move:int2q => /andP [/andP [_ _] islor].
rewrite -vt2 in vcp23.
move:vcp23 => [v1t2 [v2t2 v3t2]].
rewrite /vertex1 /vertex2 /vertex3 -v3t2 -v1t2  in islor.           
rewrite is_left_of_change  in islor.
apply is_lof_imply_is_lor_on_line in islo.
by rewrite islo in islor.
Qed.

Lemma triangulation_nps tr t p d:
d != fset0 -> p \notin d -> triangulation tr d -> t \in tr ->
in_triangle t p ->no_point_on_segment (split_triangle tr t p) (p |` d).
Proof.
move => dne p_nin_d tr_d t_tr intp.
move:(tr_d) => [tr3v [covh_tr_d [covv_tr_d [nci_tr_d [nps_tr_d [tne_tr_d or_tr_d]]]]]].
have injvt : forall t1, t1 \in split_triangle tr t p -> injective (vertex t1).
  move => t0 insplt0.
  have vert_n_p : forall i, vertex t i != p.
    move => i.
    case abs:(vertex t i == p) => //=.
    move:abs => /eqP abs.
    have nvt:=(in_triangle_not_vert intp);move:nvt=>/negbTE;rewrite-abs=>nvt.
    have vtivt:(vertex t i \in vertex_set t) by apply:in_imfset.
    by rewrite nvt in vtivt.
  have p_n_vert : forall i, p != vertex t i 
        by move => i; rewrite eq_sym;apply vert_n_p.
  move:insplt0 => /fsetUP [t0spl | t0tr];last first.
    move:t0tr => /fsetD1P [_ t0tr].
    by apply tr3v.
have tr3v_tr := triangulation_tr3v dne p_nin_d tr_d t_tr intp.
apply (triangulation_tr3v dne p_nin_d tr_d t_tr intp).
by apply/fsetUP;left.

move => t1 t2 t1_spl t2_spl q qvt1 intwet2q.
move:t1_spl => /fsetUP; move => [t1_spl|t1_spl];
move:t2_spl => /fsetUP; move=>[t2_spl|t2_spl];last first.
      move:t1_spl => /fsetD1P [t1_nt t1_tr].
      move:t2_spl => /fsetD1P [t2_nt t2_tr].
      rewrite /no_point_on_segment in nps_tr_d.
      by apply (nps_tr_d t1 t2 t1_tr t2_tr q qvt1).
    have intwetq := (split_aux_in_triangle_we intp t2_spl intwet2q).
    move:t1_spl => /fsetD1P [t1_nt t1_tr].
    have q_vt := (nps_tr_d t1 t t1_tr t_tr q qvt1 intwetq).
    have or_t2 := split_triangle_aux_oriented intp t2_spl.
    have test:= (in_triangle_w_edge_edges or_t2 q). 
    move:(intwet2q) => /test q_disj.
    move:q_disj => [q_vt2 | [int2q | t2e]] => //=.
      have abs := in_triangle_not_vert (split_aux_in_triangle intp t2_spl int2q).
      by rewrite q_vt in abs.
    move:t2e => [e [e_t2 int2e]].   
    have abs := (on_edge_split_triangle intp t2_spl e_t2 int2e).
    move:abs => [intq|abs].
      have abs := in_triangle_not_vert intq.
      by rewrite q_vt in abs. 
    move:abs=>[e0 [e0_t q_e0]].
      by have abs:=(vert_not_on_edges (is_lof_imply_is_lor_on_line (or_tr_d t t_tr)) q_vt e0_t q_e0).

  have oriented_t1 : oriented_triangle t1.
    move:t1_spl;rewrite /split_triangle_aux => /fset1UP [|/fset2P []] ->;
    apply:vertices_to_triangle_oriented.

  have intwet1q := (vert_in_triangle_w_edges oriented_t1 qvt1).
  have intwetq := (split_aux_in_triangle_we intp t1_spl intwet1q).
  have q_disj := (vertex_in_split_triangle intp t1_spl qvt1).  
  move:t2_spl=>/fsetD1P [t2_nt t2_tr].
  move:q_disj => [qvt | q_p].
    by have test:= (nps_tr_d t t2 t_tr t2_tr q qvt intwet2q).
  have test:= (in_triangle_w_edge_edges (or_tr_d t2 t2_tr) q).
  move:(intwet2q) => /test q_disj.
  move:q_disj => [q_vt2 | [int2q | t2e]] => //=.
    rewrite /no_cover_intersection in  nci_tr_d.
    rewrite q_p in int2q.
    by rewrite (nci_tr_d t t2 t_tr t2_tr p intp int2q) in t2_nt;
      move:t2_nt => /eqP.
  move:t2e => [e [e_t2 int2e]].
  have t2_3vertex : (#|` vertex_set t2| = 3).

  have test3 : (#|` [fset (vertex t2) x | x in 'I_3]| = #|` finset 'I_3|).
    apply:card_in_imfset.
    move => x y px py.
    have injvt2 : (injective (vertex t2)).
      apply injvt.
      apply /fsetUP;right.
      apply /fsetD1P=>//=.
    apply injvt2 .
  by rewrite test3 card_finset card_ord.
  have t2_nempty := tne_tr_d t2 t2_tr.
  rewrite q_p in int2e.
  have intq_int2q := in_triangle_on_edge intp t2_nempty e_t2 int2e.
  move:intq_int2q => [q' [intq' int2q']].
  rewrite /no_cover_intersection in nci_tr_d.
  have abs := nci_tr_d t t2 t_tr t2_tr q' intq' int2q'.
  by move:t2_nt ;rewrite abs => /eqP.



have spl_p_in_vset: forall t3, t3 \in split_triangle_aux t p -> p \in vertex_set t3.
  move:(intp) => /andP [/andP [islo1 islo2] islo3].
  apply is_lof_imply_is_lor_on_line in islo1.
  apply is_lof_imply_is_lor_on_line in islo2.
  apply is_lof_imply_is_lor_on_line in islo3.
  have vc12p := vertices_to_triangle_correct islo1.
  have vcp23 := vertices_to_triangle_correct islo2.
  have vc1p3 := vertices_to_triangle_correct islo3.
  move:islo1 islo2 islo3 => _ _ _.
  by move => t3 /fset1UP [vt3 | /fset2P [vt3|vt3]];
  [move:vc12p => [_ [_ temp]]|move:vcp23=> [temp _]|move:vc1p3 => [_ [temp _]]];
  rewrite temp;apply /imfsetP;
  [exists ord32|exists ord30|exists ord31]=> //=;rewrite vt3.

case t1_t2 : (t2==t1);last move:t1_t2 => /eqP t1_n_t2.
  by move :t1_t2 => /eqP => ->.

move:(intp) => /andP [/andP [islo1 islo2] islo3].
apply is_lof_imply_is_lor_on_line in islo1.
apply is_lof_imply_is_lor_on_line in islo2.
apply is_lof_imply_is_lor_on_line in islo3.
have vc12p := vertices_to_triangle_correct islo1.
have vcp23 := vertices_to_triangle_correct islo2.
have vc1p3 := vertices_to_triangle_correct islo3.
move:islo1 islo2 islo3 => _ _ _.

move:t1_spl=> /fset1UP [vt1 |t1_spl];last move:t1_spl=> /fset2P [vt1|vt1];
rewrite vt1 in qvt1;move:(qvt1) => /in_vertex_set [valq | [valq | valq]];
move:valq => /eqP valq;rewrite valq;
move:t2_spl => /fset1UP [vt2|t2_spl];try move:t2_spl=> /fset2P [vt2|vt2];
rewrite vt1 vt2 in t1_n_t2 => //=;
have temp := (vertices_to_triangle_correct2 vt2);
move:temp => [temp1 [temp2 temp3]]=> //=;rewrite valq in intwet2q.

rewrite /in_triangle in intp.
          move:(intp) => /andP[/andP [islo _] _].
          move:(intwet2q) => /andP [/andP [islor _] _].
          rewrite -vt2 in vcp23.
          move:vcp23 => [dp [dv2t2 _]].
          rewrite /vertex1 -dp /vertex2 -dv2t2 in islor.
          rewrite is_left_or_on_change is_left_of_circular in islor.
            by rewrite islo in islor.
        move:(intp) => /andP[/andP [islo _] _].
        move:(intwet2q) => /andP [/andP [islor _] _].
        rewrite -vt2 in vc1p3.
        move:vc1p3 => [dp [dv2t2 _]].
        rewrite /vertex1 -dp /vertex2 -dv2t2 in islor.
        rewrite is_left_or_on_change is_left_of_circular in islor.
        rewrite is_left_of_circular in islor.
          by rewrite islo in islor.
      move:(intp) => /andP[/andP [islo _] _].
      move:(intwet2q) => /andP [/andP [islor _] _].
      rewrite -vt2 in vc1p3.
      move:vc1p3 => [dp [dv2t2 _]].
      rewrite /vertex1 -dp /vertex2 -dv2t2 in islor.
      rewrite is_left_or_on_change -is_left_of_circular in islor.
        by rewrite islo in islor.   
    move:(intp) => /andP[/andP [_ islo] _].
    move:(intwet2q) => /andP [/andP [_ islor] _].
    rewrite -vt2 in vc12p.
    move:vc12p => [_ [dv2t2 dp]].
    rewrite /vertex2 /vertex3 -dp -dv2t2 in islor.
    rewrite is_left_or_on_change is_left_of_circular in islor.
      by rewrite islo in islor.
  move:(intp) => /andP[/andP [islo _] _].
  move:(intwet2q) => /andP [/andP [islor _] _].
  rewrite -vt2 in vcp23.
  move:vcp23 => [dp [dv2t2 _]].
  rewrite /vertex1 -dp /vertex2 -dv2t2 in islor.
  rewrite is_left_or_on_change is_left_of_circular in islor.
    by rewrite islo in islor.
move:(intp) => /andP[/andP [_ islo] _].
move:(intwet2q) => /andP [/andP [_ islor] _].
rewrite -vt2 in vc12p.
move:vc12p => [_ [dv2t2 dp]].
rewrite /vertex2 /vertex3 -dp -dv2t2 in islor.
rewrite is_left_or_on_change is_left_of_circular in islor.
  by rewrite islo in islor.
Qed.

Lemma triangulation_cvh:
  forall tr, forall t , forall p, forall d, d != fset0 -> p \notin d ->
                        triangulation tr d -> t \in tr ->
                        in_triangle t p ->
                        covers_hull (split_triangle tr t p) (p |` d).
Proof.
move => tr t p d dne p_nin_d tr_d t_tr intp.
move:(tr_d) => [tr3v [covh_tr_d [covv_tr_d [nci_tr_d nps_tr_d]]]].
move => q hull_pdq.  
have hull_d_q : hull d q.
  move:(p_nin_d)=>/hull_add_point temp.
  apply temp;move:temp => _.
  move:(dne)=>/hull_from_triangle temp.
  move:(tr_d)=>/temp temp2.
  by apply (temp2 t).
  by [].
  apply covh_tr_d in hull_d_q as [t0 [t0_tr intwe_to_q]].
  case t_t0 : (t0 == t).
    move:t_t0 => /eqP t_t0.
    have temp:(forall p0 : P,in_triangle_w_edges t p0 ->
                        exists t1 : T,
                          t1 \in split_triangle_aux t p /\
                                 in_triangle_w_edges t1 p0)
      by apply three_triangles_cover_one.
    have temp2 :(exists t1 : T, t1 \in split_triangle_aux t p /\
                                  in_triangle_w_edges t1 q)
    by apply temp;rewrite -t_t0.
    move:temp => _. move:temp2 => [t1 [split_aux_t1_tp intwe_t1_q]].
    exists t1;split=>//=.
  by apply /fsetUP;left.    
exists t0.
split=>//=.
apply /fsetUP;right.
apply /fsetD1P.
split;first apply/eqP;move:t_t0=>/eqP //=.
Qed.

Lemma triangulation_cvv tr t p d :
   d != fset0 -> p \notin d -> triangulation tr d -> t \in tr ->
     in_triangle t p -> covers_vertices (split_triangle tr t p) (p |` d).
Proof.
move => dne p_nin_d tr_d t_tr intp.
move:(tr_d) => [tr3v [covh_tr_d [covv_tr_d [nci_tr_d nps_tr_d]]]].
move => q.
split.
  move=>q_in_p.
  case p_q:(q==p);move:p_q=>/eqP p_q.
    pose t0 := (vertices_to_triangle (vertex1 t) (vertex2 t) p); exists t0.
    split;first by apply /fsetUP;left;apply/fset1UP;left.
    rewrite /t0.
    have temp : (t0 = vertices_to_triangle (vertex1 t) (vertex2 t) p) by [].
    apply vertices_to_triangle_correct2 in temp.
      by rewrite p_q; move:temp => [_ [_ temp]].
  move:q_in_p => /fset1UP q_in_d.
  move:q_in_d => [q_p|q_in_d]; first  by rewrite q_p in p_q.
  apply covv_tr_d in q_in_d;move:q_in_d=>[t1 [t1_tr v_t1]].
  case t_t1:(t==t1);move:t_t1=> /eqP t_t1.
    pose t0 := (vertices_to_triangle (vertex1 t) (vertex2 t) p).
    pose t2 := vertices_to_triangle p (vertex2 t) (vertex3 t).
    have t0_spl : t0 \in split_triangle tr t p
      by apply/fsetUP;left;apply/fset1UP;left.
    have t2_spl : t2  \in split_triangle tr t p
      by apply/fsetUP;left;apply/fset1UP;right;apply/fset2P;left.
    move:v_t1 => /imfsetP [[[|[|[|x']]] px] _] x_v => //=.
      exists t0.
      split=> //=.
      have v1_t0 :vertex1 t \in vertex_set t0.
        have temp:t0 = t0 by [].
        apply vertices_to_triangle_correct2 in temp.
        by move:temp=>[temp _].
      have q_v1t : (q = vertex1 t).
        rewrite x_v t_t1.
        congr(vertex t1 _).
        by apply ord_inj.
      by rewrite q_v1t.
    exists t0.
    split=> //=.
    have v2_t0 :vertex2 t \in vertex_set t0.
      have temp:t0 = t0 by [].
      apply vertices_to_triangle_correct2 in temp.
      by move:temp=>[_ [temp _]].
    have q_v2t : (q = vertex2 t).
      rewrite x_v t_t1.
      congr(vertex t1 _).
      by apply ord_inj.
    by rewrite q_v2t.
  exists t2.
  split=> //=.
  have v3_t0 :vertex3 t \in vertex_set t2.
    have temp:t2 = t2 by [].
    apply vertices_to_triangle_correct2 in temp.
    by move:temp=>[_ [_ temp]].
  have q_v3t : (q = vertex3 t).
    rewrite x_v t_t1.
    congr(vertex t1 _).
    by apply ord_inj.
  by rewrite q_v3t.
    
rewrite /split_triangle /split_triangle_aux.

exists t1;split=>//=;apply /fsetUP;right.
by apply /fsetD1P;split=>//=; move:t_t1=>/eqP t_t1; rewrite eq_sym.
move=> [t0 [spl_t0 v_t0]].  
move:spl_t0 => /fsetUP H.
move:H => [H|H].
  have vert_set:q = p \/ q=vertex1 t \/ q = vertex2 t \/ q = vertex3 t.  
     move:(intp) => /andP [/andP [islo1 islo2] islo3].
     apply is_lof_imply_is_lor_on_line in islo1.
     apply is_lof_imply_is_lor_on_line in islo2.
     apply is_lof_imply_is_lor_on_line in islo3.
     have vc12p := vertices_to_triangle_correct islo1.
     have vcp23 := vertices_to_triangle_correct islo2.
     have vc1p3 := vertices_to_triangle_correct islo3.
     move:islo1 islo2 islo3 => _ _ _.
     rewrite in_fset1U in H; move:H => /predU1P H;rewrite in_fset2 in H;
     move:H => [H|H];last move :H => /predU1P [H|/eqP H].
         rewrite -H in vc12p.
         move:vc12p v_t0=> [temp1 [temp2 temp3]] /imfsetP.
         move => [[[|[|[|x']]] px] _] v_t0 => //=;
         [right;left|right;right;left|left];rewrite v_t0;
         [rewrite temp1|rewrite temp2|rewrite temp3];
         by congr((vertex t0) _);apply ord_inj.
       rewrite -H in vcp23.
       move:vcp23 v_t0=> [temp1 [temp2 temp3]] /imfsetP.
       move => [[[|[|[|x']]] px] _] v_t0 => //=;
       [left|right;right;left|right;right;right]; rewrite v_t0;
       [rewrite temp1|rewrite temp2|rewrite temp3];
       by congr((vertex t0) _);apply ord_inj.
     rewrite -H in vc1p3.
     move:vc1p3 v_t0=> [temp1 [temp2 temp3]] /imfsetP.
     move => [[[|[|[|x']]] px] _] v_t0 => //=;
     [right;left|left|right;right;right]; rewrite v_t0;
     [rewrite temp1|rewrite temp2|rewrite temp3];
       by congr((vertex t0) _);apply ord_inj.
  by move:vert_set=>[vt|[vt|[vt|vt]]];rewrite vt; apply/fset1UP;
  first left=>//=;right; apply covv_tr_d;exists t;split=>//=;
  apply/imfsetP;[exists ord30|exists ord31|exists ord32].
have t0_tr :t0 \in tr by move:H => /fsetD1P [_ H].
rewrite /covers_vertices in covv_tr_d.
have temp: t0 \in tr /\ q \in vertex_set t0 by [].
apply/fset1UP;right.
apply covv_tr_d.
by exists t0.
Qed.


Lemma triangulation_tne:
  forall tr, forall t , forall p, forall d, d != fset0 -> p \notin d ->
                        triangulation tr d -> t \in tr ->
                        in_triangle t p ->
                        triangles_nempty (split_triangle tr t p).
Proof. 
move => tr t p d dne p_nin_d tr_d t_tr intp t' t'_spl.
move:(tr_d) => [tr3v [covh_tr_d [covv_tr_d [nci_tr_d [nps_tr_d tne_tr_d ]]]]].
move:t'_spl => /fsetUP [t'_spl|t'_trt];last first.
  by move:t'_trt => /fsetD1P [t'_nt t'_tr];apply tne_tr_d.
move:(intp) => /andP [/andP [intp1 intp2] intp3].
by move:(t'_spl) => /fset1UP [Ht' | /fset2P [Ht' |Ht']];
rewrite Ht'; apply surface_non_empty.
Qed. 

Lemma triangulation_or:
  forall tr, forall t , forall p, forall d, d != fset0 -> p \notin d ->
                        triangulation tr d -> t \in tr ->
                        in_triangle t p ->
                        oriented_triangle_triangulation
                          (split_triangle tr t p).
Proof. 
move => tr t p d dne p_nin_d tr_d t_tr intp t' t'_spl.
move:(tr_d) => [tr3v [covh_tr_d [covv_tr_d [nci_tr_d [nps_tr_d [tne_tr_d or_tr_d]]]]]].
move:t'_spl;rewrite /split_triangle => /fsetUP [];
   last by move => /fsetD1P [] _;apply:or_tr_d.
move:intp => /andP [] /andP [] islof1 islof2 islof3.
by rewrite /split_triangle_aux => /fset1UP [-> | /fset2P [] ->];
rewrite /oriented_triangle_strict;
[have vc := vertices_to_triangle_correct (is_lof_imply_is_lor_on_line islof1)|
have vc := vertices_to_triangle_correct (is_lof_imply_is_lor_on_line islof2)|
have vc := vertices_to_triangle_correct (is_lof_imply_is_lor_on_line islof3)];
move:vc => [vc1 [vc2 vc3]];rewrite /vertex1 /vertex2 /vertex3 -vc1 -vc2 -vc3.
Qed.
    
Theorem triangulation_split_triangle:
  forall tr, forall t , forall p, forall d, d != fset0 -> p \notin d ->
                        triangulation tr d -> t \in tr ->
                        in_triangle t p ->
                        triangulation (split_triangle tr t p) (p |` d).
move => tr t p d dne p_nin_d tr_d t_tr intp.
move:(tr_d) => [tr3v [covh_tr_d [covv_tr_d [nci_tr_d nps_tr_d]]]].  
split;first by apply:triangulation_tr3v dne p_nin_d tr_d t_tr intp.
split;first by apply triangulation_cvh.
split;first by apply triangulation_cvv.
split;first by apply triangulation_nci.
split;first by apply:triangulation_nps.
split;first by apply:(triangulation_tne dne).
apply:triangulation_or => //=.
by apply dne.
by apply p_nin_d.
by apply tr_d.
Qed.

(* This is probably a lemma that can already be proved: TODO *)

Hypothesis vertex_set_eq_in_triangle:
  forall t1, forall t2, oriented_triangle t1 -> oriented_triangle t2 ->
              vertex_set t1 = vertex_set t2 -> 
        forall p , in_triangle t1 p -> in_triangle t2 p.

Hypothesis vertex_set_eq_in_triangle_w_edges :
  forall t1, forall t2, oriented_triangle t1 -> oriented_triangle t2 ->
              vertex_set t1 = vertex_set t2 -> 
        forall p , in_triangle_w_edges t1 p -> in_triangle_w_edges t2 p.


Lemma in_vert_to_triangle_in_triangle a b c :
  is_left_of a b c -> forall t, a \in vertex_set t ->
  oriented_triangle t -> b \in vertex_set t -> c \in vertex_set t ->
  {subset in_triangle (vertices_to_triangle a b c) <= in_triangle t}.
Proof.
move=> islo_abc t a_t or_t b_t c_t.
apply: vertex_set_eq_in_triangle => //=.
rewrite vertex_set_vertices_to_triangle.
move: islo_abc.
have [->|b_na] := eqVneq a b.
  by rewrite /is_left_of oriented_surface_x_x ltrr.
have [->|b_nc] := eqVneq b c.
  by rewrite -is_left_of_circular /is_left_of oriented_surface_x_x ltrr.
have [->|c_na] := eqVneq a c.
  by rewrite is_left_of_circular /is_left_of oriented_surface_x_x ltrr.
move=> islo_abc; apply /eqP; rewrite eqEfcard; apply/andP; split.
  by apply /fsubsetP=> x /fsetUP [/fset2P [] ->|/fset1P ->].
suff card_fset3 : #|` [fset a; b; c] | = 3%N.
  rewrite card_fset3 (leq_trans (leq_imfset_card _ _)) //.
  by rewrite card_finset card_ord.
rewrite !cardfsU !cardfs1 fsetI1 !inE [b == a]eq_sym (negPf b_na) cardfs0.
by rewrite fsetI1 !inE ![c == _]eq_sym (negPf b_nc) (negPf c_na) /= cardfs0.
Qed.

Lemma vertices_to_triangle_oriented_strict a b c:
  is_left_of a b c -> oriented_triangle_strict (vertices_to_triangle a b c).
Proof.
move => islo_abc.
have vc := vertices_to_triangle_correct (is_lof_imply_is_lor_on_line islo_abc).
move:vc => [v1 [v2 v3]].
by rewrite /oriented_triangle_strict /vertex1 /vertex2 /vertex3 -v1 -v2 -v3.
Qed.

Lemma in_vert_to_triangle_in_triangle_w_edges a b c:
   is_left_of a b c ->
      forall t,  oriented_triangle_strict t ->
            a \in vertex_set t -> b \in vertex_set t -> c \in vertex_set t ->
      forall q, in_triangle_w_edges (vertices_to_triangle a b c) q -> in_triangle_w_edges t q.
Proof.
move => islo_abc t or_t a_t b_t c_t q intwq.

have invt := in_vert_to_triangle_in_triangle islo_abc a_t (is_lof_imply_is_lor_on_line or_t) b_t c_t.
apply (in_triangle_w_edge_edges (vertices_to_triangle_oriented_strict islo_abc)) in intwq.
apply (in_triangle_w_edge_edges or_t).  
move:intwq => [q_vt| [intq|q_et]];[left|right;left|right;right];
[rewrite vertex_set_vertices_to_triangle in q_vt|by apply invt|move];
first by move:q_vt => /fsetUP [/fset2P [] |/fset1P] ->.
move:q_et => [e [e_abc e_q]];exists e;split => //=.
by move:e_abc; rewrite (edges_set_vertices_to_triangle islo_abc)
=> /fsetUP [/fset2P []| /fset1P] ->;
apply vertex_set_edge_triangle => //=;
move:islo_abc; [have [|//=] := eqVneq a b|
have [|//=] := eqVneq a c| have [|//=] := eqVneq b c] => ->;
[move|rewrite is_left_of_circular|rewrite -is_left_of_circular];
rewrite /is_left_of oriented_surface_x_x ltrr.
Qed.


Lemma vertices_to_triangle_circular_w_edges :
  forall a b c p, is_left_of a b c ->
    in_triangle_w_edges (vertices_to_triangle a b c) p ->
    in_triangle_w_edges (vertices_to_triangle c a b) p. 
Proof.
  move => a b c p islo_abc intabcp.
  pose t := vertices_to_triangle c a b.
  have t_abc : t = vertices_to_triangle c a b by [].
  have vc_cab := vertices_to_triangle_correct2 t_abc.
  move:vc_cab => [c_cab [a_cab b_cab]].
  rewrite /t in c_cab.
  rewrite /t in a_cab.
  rewrite /t in b_cab.
  (apply:in_vert_to_triangle_in_triangle_w_edges; first apply islo_abc;
    rewrite is_left_of_circular in islo_abc;
  first apply (vertices_to_triangle_oriented_strict islo_abc)) => //=.
Qed.
  
Definition flip_edge_aux a b c d :=
let new_t1 := vertices_to_triangle a b d in
let new_t2 := vertices_to_triangle b c d in
new_t1 |` [fset new_t2].

Definition flip_edge tr t1 t2 a b c d := 
(flip_edge_aux a b c d) `|` ((tr `\ t1) `\ t2) .

Lemma is_left_abs1 :
  forall a b c, (0< oriented_surface a b c) -> (0 <= oriented_surface a c b -> false).
Proof.
move => a b c oriented_abc oriented_acb.
rewrite oriented_surface_change1 in oriented_acb.
rewrite oppr_ge0 in oriented_acb.
have : oriented_surface a b c < oriented_surface a b c.
by apply:ler_lt_trans oriented_acb oriented_abc.
by rewrite ltrr. 
Qed.



Lemma is_on_line_imply_is_lor : 
  forall a b c, is_on_line a b c -> is_left_or_on_line a b c.
Proof.
move => a b c isonl_abc.
rewrite /is_on_line in isonl_abc.
rewrite /is_left_or_on_line.
by move:isonl_abc => /eqP ->.
Qed.



Lemma flip_edge_covers_aux tr data:  triangulation tr data -> 
                                    forall t1, forall t2, t1 != t2 -> t1 \in tr->t2 \in tr ->
                                    forall a, forall c, a != c -> a \in vertex_set t1 ->
                                     a \in vertex_set t2 ->
                                     c \in vertex_set t1 -> c \in vertex_set t2 ->
                                    forall b, b \in vertex_set t1 -> b != a -> b != c ->
                                     is_left_of a b c ->
                                    forall d, d \in vertex_set t2 -> d != a -> d != c ->
                                     is_left_of a c d -> 
                                     is_left_of b c d ->
                                     is_left_of a b d ->
                                     forall q, in_triangle_w_edges t1 q ->
                                     exists t3, (t3 \in flip_edge_aux a b c d /\
                                            in_triangle_w_edges t3 q).
Proof.
move => tr_d t1 t2 t1_nt2 t1_tr t2_tr a c a_nc a_t1 a_t2 c_t1 c_t2.
move => b b_t1 b_na b_nc oriented_abc d d_t2 d_na d_nc.
move => islo_acd islo_bcd islo_abd q intwet1q.
rewrite /in_triangle_w_edges  in intwet1q.

have islo_and : is_left_or_on_line a b q &&
                is_left_or_on_line q b c &&
                is_left_or_on_line a q c.
move:(intwet1q) => /andP [/andP [islor12q islorq23] islor1q3].
move:(tr_d) => [_  [_ [_ [_ [_ [_ or_tr_d]]]]]].
  move:(a_t1) => /imfsetP [[[|[|[|x1']]] px1] _] a_vt1 => //=;
  move:(b_t1) => /imfsetP [[[|[|[|x2']]] px2] _] b_vt1 => //=;
  move:(c_t1) => /imfsetP [[[|[|[|x3']]] px3] _] c_vt1 => //=;
  (try have x1_x2:Ordinal px1 = Ordinal px2 by apply ord_inj);
  (try (rewrite x1_x2 in a_vt1;
  rewrite a_vt1 b_vt1 in b_na;
  move:b_na => /eqP //=));
  (try have x1_x3:Ordinal px1 = Ordinal px3 by apply ord_inj);
  (try (rewrite x1_x3 in a_vt1;
  rewrite a_vt1 c_vt1 in a_nc;
  move:a_nc => /eqP //=));
  (try have x2_x3:Ordinal px2 = Ordinal px3 by apply ord_inj);
  (try (rewrite x2_x3 in b_vt1;
  rewrite b_vt1 c_vt1 in b_nc;
  move:b_nc => /eqP //=));
  (try have ord1 : Ordinal px1 = ord30 by apply ord_inj);
  (try have ord1 : Ordinal px1 = ord31 by apply ord_inj);
  (try have ord1 : Ordinal px1 = ord32 by apply ord_inj);
  (try have ord2 : Ordinal px2 = ord30 by apply ord_inj);
  (try have ord2 : Ordinal px2 = ord31 by apply ord_inj);
  (try have ord2 : Ordinal px2 = ord32 by apply ord_inj);
  (try have ord3 : Ordinal px3 = ord30 by apply ord_inj);
  (try have ord3 : Ordinal px3 = ord31 by apply ord_inj);
  (try have ord3 : Ordinal px3 = ord32 by apply ord_inj);
  
  rewrite ord1 in a_vt1;rewrite ord2 in b_vt1;rewrite ord3 in c_vt1;
  have oriented_t1 := is_lof_imply_is_lor_on_line (or_tr_d t1 t1_tr);
  rewrite /is_left_or_on_line  /vertex1 /vertex2 /vertex3 -a_vt1 -b_vt1 -c_vt1 in oriented_t1;
  rewrite /vertex1 /vertex2 /vertex3 -a_vt1 -b_vt1 -c_vt1 in intwet1q => //=;
  move:intwet1q => /andP [/andP [islo1 islo2] islo3];
  [move|rewrite -oriented_surface_circular in oriented_t1|move|move|
   rewrite oriented_surface_circular in oriented_t1];
  (try have temp := (is_left_abs1 oriented_abc oriented_t1) => //=).
    apply/andP;split;try (apply/andP;split);
    rewrite is_left_or_on_line_circular => //=.
  by apply/andP;split;try (apply/andP;split);
  rewrite -is_left_or_on_line_circular.
 
  case islo_qbd : (is_left_or_on_line q b d).
    exists (vertices_to_triangle a b d).
    split; first by apply /fset1UP;left.
    have oriented_abd:(is_left_or_on_line a b d).
      by apply is_lof_imply_is_lor_on_line.
    have vc_abc := vertices_to_triangle_correct oriented_abd.
    move:vc_abc => [va [vb vd]].
    rewrite /in_triangle_w_edges /vertex1 /vertex2 /vertex3 -va -vb -vd.
    apply/andP.
    have islo_abq : is_left_or_on_line a b q 
        by move:islo_and => /andP [/andP [test _] _].
    split;first apply/andP;first split => //=.
    move:islo_qbd;rewrite -is_left_or_on_line_circular => islo_bdq.
    move:islo_abd => islof_abd. 
    move:(islof_abd) => /is_lof_imply_is_lor_on_line islo_abd.

    rewrite is_left_or_on_line_circular.
    rewrite is_left_of_circular in islof_abd.
    apply is_lof_imply_is_lor_on_line in islof_abd.
    apply is_lof_imply_is_lor_on_line in oriented_abc.
    rewrite is_left_or_on_line_circular in oriented_abc.
    
    apply:(is_left_or_line_trans2 islof_abd oriented_abc).
        by rewrite is_left_or_on_line_circular in islo_abq.
          by move:islo_and => /andP [_ temp];
           rewrite is_left_or_on_line_circular in temp.
    by apply is_lof_imply_is_lor_on_line in islo_acd;
    rewrite is_left_or_on_line_circular in islo_acd.
    
  exists (vertices_to_triangle b c d).
  split;first by apply/fset2P ;right.
  have oriented_bcd : is_left_or_on_line b c d.
    by apply is_lof_imply_is_lor_on_line.
  have vc_bcd := vertices_to_triangle_correct oriented_bcd.
  move:vc_bcd => [vb [vc vd]].
  rewrite /in_triangle_w_edges /vertex1 /vertex2 /vertex3 -vb -vc -vd. 
  apply/andP.
  have islo_bcq : is_left_or_on_line b c q.
    move:islo_and => /andP [/andP [_ temp _]];
    by rewrite -is_left_or_on_line_circular in temp.
  rewrite /is_left_or_on_line in islo_qbd.
  move:islo_qbd => /negP /negP;
  rewrite -ltrNge oriented_surface_change1 oppr_lt0.
  move => /is_lof_imply_is_lor_on_line;
  rewrite is_left_or_on_line_circular => islor_bqd.
  split => //= ;first apply/andP;first split => //=.
  rewrite - is_left_or_on_line_circular.
  move:islo_bcd => islof_bcd.
  move:(islof_bcd) => /is_lof_imply_is_lor_on_line islo_bcd.
  rewrite is_left_or_on_line_circular.
  move:oriented_abc => islo_bca.
  apply is_lof_imply_is_lor_on_line in islo_bca.
  rewrite -is_left_or_on_line_circular in islo_bca.

  apply:(is_left_or_line_trans islo_bcd islo_bca islo_bcq).
    by move:islo_and=>/andP [_ temp];
      rewrite -is_left_or_on_line_circular in temp.
  by apply is_lof_imply_is_lor_on_line in islo_acd.
Qed.




Lemma vertices_vt : forall a b, b != a -> forall c, b != c -> a != c -> 
                        forall t, injective (vertex t) ->    
                             a \in vertex_set t ->
                             b \in vertex_set t ->
                             c \in vertex_set t ->
                               a |` [fset b;c] =i vertex_set t.
Proof.
move => a b a_nb c b_nc a_nc t injvt a_t b_t c_t.
have card_abc: #|` a |` [fset b;c] | = 3.        
  rewrite cardfsU1.
  have a_nin_bc :(a \notin [fset b; c]).
    apply/fset2P.
    apply /Decidable.not_or_iff.
    split => temp.
      by rewrite temp in a_nb;move:a_nb => /eqP.
    by rewrite temp in a_nc;move:a_nc => /eqP.
  by rewrite a_nin_bc cardfs2 b_nc.
have card_vt : #|` vertex_set t | = #|` finset 'I_3 |.
  by apply:card_imfset=> //=.
rewrite card_finset card_ord in card_vt.
have card_abc_vt : #|` a |` [fset b; c]| = #|` vertex_set t|
  by rewrite card_abc.
have abc_incl_vt :  a |` [fset b; c] `<=` vertex_set t.
  apply/fsubsetP.
  by move => x /fset1UP [-> //= | /fset2P [-> | ->] ].
apply fsubset_cardP in card_abc_vt.
by apply /card_abc_vt.
Qed.







Theorem in_flip_edge_aux tr data:
   triangulation tr data -> 
  forall t1, forall t2, t1 != t2 -> t1 \in tr->t2 \in tr ->
  forall a, forall c, a != c -> a \in vertex_set t1 -> a \in vertex_set t2 ->
                     c \in vertex_set t1 -> c \in vertex_set t2 ->
  forall b, b \in vertex_set t1 -> b != a -> b != c -> is_left_of a b c ->
  forall d, d \in vertex_set t2 -> d != a -> d != c ->
       is_left_of a c d -> is_left_of b c d -> is_left_of a b d ->
  forall t, t \in flip_edge_aux a b c d -> forall q, in_triangle t q -> 
  (in_triangle (vertices_to_triangle a b c) q \/
   in_triangle (vertices_to_triangle a c d) q \/
   on_edge (vertices_to_edge a c) q).
Proof.


move => tr_d t1 t2 t1_nt2 t1_tr t2_tr a c a_nc a_t1 a_t2 c_t1 c_t2.
move => b b_t1 b_na b_nc oriented_abc d d_t2 d_na d_nc oriented_acd islo_bcd islo_abd.
move:(tr_d) => [tr3v_tr_d [cvh_tr_d [cvv_tr_d [nci_tr_d nps_tr_d]]]].
move => t t_fl q intq.

have vc_abc := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line oriented_abc).
have vc_acd := vertices_to_triangle_correct
                 (is_lof_imply_is_lor_on_line oriented_acd).
move : (vc_abc) => [a_abc [b_abc c_abc]].
move : (vc_acd) => [a_acd [c_acd d_acd]].
have vc_abd := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line islo_abd).
have vc_bcd := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line islo_bcd).
move : (vc_abd) => [a_abd [b_abd d_abd]].
move : (vc_bcd) => [b_bcd [c_bcd d_bcd]].

have not_in_both_triangles:forall p, in_triangle (vertices_to_triangle a b d) p ->
       in_triangle (vertices_to_triangle b c d) p -> false.
  move => p p_abd p_bcd.
  rewrite /in_triangle /vertex1 /vertex2 /vertex3
  -a_abd -b_abd -d_abd in p_abd.
  move:p_abd => /andP [/andP[islo_abp islo_pbd] islo_apd].
  rewrite /in_triangle /vertex1 /vertex2 /vertex3
  -b_bcd -c_bcd -d_bcd in p_bcd.
  move:p_bcd => /andP [/andP[islo_bcp islo_pcd] islo_bpd].
  rewrite  is_left_of_change in islo_bpd.
  apply is_lof_imply_is_lor_on_line in islo_pbd.
    by rewrite islo_pbd in islo_bpd.

move:t_fl => /fset2P [Ht|Ht];
rewrite Ht /in_triangle /vertex1 /vertex2 /vertex3 in intq;    
[rewrite -a_abd -b_abd -d_abd in intq|
 rewrite -b_bcd -c_bcd -d_bcd in intq];
move:intq => /andP[/andP [intq1 intq2] intq3];
case islo_acq:(is_left_of a q c);
(try (move:islo_acq => /negP /negP; rewrite -is_left_or_on_change;move => islo_acq;
 rewrite -is_left_or_on_line_circular in islo_acq));
(try apply is_left_or_on_split in islo_acq);
(try move:islo_acq => [islo_acq|is_on_acq]);
[left|right;right|right;left|left|right;right|right;left];
rewrite /in_triangle /vertex1 /vertex2 /vertex3;
(try rewrite -a_abc -b_abc -c_abc);
(try rewrite -a_acd -c_acd -d_acd);
(try (apply/andP;split=> //=;(try apply/andP;try split) => //=));
(try( by rewrite is_left_of_circular in intq1)).
          apply:(is_left_of_trans oriented_abc islo_abd intq1 intq2).
            by rewrite is_left_of_circular in islo_bcd.

        have islo_bcq : is_left_of b c q.
          rewrite is_left_of_circular.
          rewrite is_left_of_circular in islo_bcd. 
          by apply:(is_left_of_trans oriented_abc islo_abd).
        apply:(on_line_on_edge oriented_abc islo_acq intq1 islo_bcq).
      rewrite -is_left_of_circular.
      apply:is_left_of_trans2.
      rewrite -is_left_of_circular in oriented_acd.
      apply oriented_acd.
      rewrite -is_left_of_circular in islo_abd.
      apply islo_abd.
      by rewrite is_left_of_circular.
      by rewrite -is_left_of_circular in intq2.
      by rewrite -is_left_of_circular in islo_bcd.
    rewrite is_left_of_circular in intq1.
    rewrite is_left_of_circular in islo_bcd.
    rewrite is_left_of_circular in intq3.
    by apply:(is_left_of_trans2 oriented_abc islo_bcd intq1 intq3).
  apply:(on_line_on_edge oriented_abc islo_acq) => //=.
  rewrite is_left_of_circular in islo_bcd.
  rewrite is_left_of_circular in intq1.
  rewrite is_left_of_circular in intq3.
  by apply:(is_left_of_trans2 oriented_abc islo_bcd).
rewrite -is_left_of_circular.
rewrite -is_left_of_circular in oriented_acd.
rewrite -is_left_of_circular in islo_bcd.
rewrite -is_left_of_circular in intq2.
rewrite -is_left_of_circular in intq3.
rewrite -is_left_of_circular in islo_abd.
by apply:(is_left_of_trans oriented_acd islo_bcd intq2 intq3).
Qed.

Theorem in_flip_edge_aux_oriented :
  forall tr, forall data, triangulation tr data -> 
  forall t1, forall t2, t1 != t2 -> t1 \in tr->t2 \in tr ->
  forall a, forall c, a != c -> a \in vertex_set t1 -> a \in vertex_set t2 ->
                     c \in vertex_set t1 -> c \in vertex_set t2 ->
  forall b, b \in vertex_set t1 -> b != a -> b != c -> is_left_of a b c ->
  forall d, d \in vertex_set t2 -> d != a -> d != c ->
       is_left_of a c d -> is_left_of b c d -> is_left_of a b d ->
  forall t, t \in flip_edge_aux a b c d -> oriented_triangle_strict t.
Proof.

move => tr data tr_d t1 t2 t1_nt2 t1_tr t2_tr a c a_nc a_t1 a_t2 c_t1 c_t2.
move => b b_t1 b_na b_nc oriented_abc d d_t2 d_na d_nc oriented_acd.
move =>islo_bcd islo_abd t.
move => /fset2P[]->;apply vertices_to_triangle_oriented_strict;easygeo.
Qed.


Theorem in_flip_edge_aux_we :
  forall tr, forall data, triangulation tr data -> 
  forall t1, forall t2, t1 != t2 -> t1 \in tr->t2 \in tr ->
  forall a, forall c, a != c -> a \in vertex_set t1 -> a \in vertex_set t2 ->
                     c \in vertex_set t1 -> c \in vertex_set t2 ->
  forall b, b \in vertex_set t1 -> b != a -> b != c -> is_left_of a b c ->
  forall d, d \in vertex_set t2 -> d != a -> d != c ->
       is_left_of a c d -> is_left_of b c d -> is_left_of a b d ->
  forall t, t \in flip_edge_aux a b c d -> forall q, in_triangle_w_edges t q -> 
  (in_triangle_w_edges (vertices_to_triangle a b c) q \/
   in_triangle_w_edges (vertices_to_triangle a c d) q).
Proof.


move => tr data tr_d t1 t2 t1_nt2 t1_tr t2_tr a c a_nc a_t1 a_t2 c_t1 c_t2.
move => b b_t1 b_na b_nc oriented_abc d d_t2 d_na d_nc oriented_acd.
move =>islo_bcd islo_abd.
move:(tr_d) => [tr3v_tr_d [cvh_tr_d [cvv_tr_d [nci_tr_d nps_tr_d]]]].
move => t t_fl q intq.

have vc_abc := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line oriented_abc).
have vc_acd := vertices_to_triangle_correct
                 (is_lof_imply_is_lor_on_line oriented_acd).
move : (vc_abc) => [a_abc [b_abc c_abc]].
move : (vc_acd) => [a_acd [c_acd d_acd]].
have vc_abd := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line islo_abd).
have vc_bcd := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line islo_bcd).
move : (vc_abd) => [a_abd [b_abd d_abd]].
move : (vc_bcd) => [b_bcd [c_bcd d_bcd]].
apply in_triangle_w_edge_edges in intq;last first.
  apply:(in_flip_edge_aux_oriented tr_d t1_nt2 t1_tr t2_tr a_nc a_t1 a_t2 c_t1 c_t2
        b_t1 b_na b_nc oriented_abc d_t2 d_na d_nc oriented_acd)=> //=.
have or_abc := vertices_to_triangle_oriented_strict oriented_abc.
have or_acd := vertices_to_triangle_oriented_strict oriented_acd.
move : intq => [q_t | [intq | q_e]].
    by move:t_fl=> /fset2P [Ht|Ht];rewrite Ht in q_t;
    apply in_vertex_set in q_t;move:q_t => [/eqP ->|[/eqP ->|/eqP ->]];
    [left|left|right|left|left|right];
    apply in_triangle_w_edge_edges => //=; left;
    apply in_vertex_set;
    [left|right;left|right;right|right;left|right;right|right;right].
  have Hq := in_flip_edge_aux tr_d t1_nt2 t1_tr t2_tr a_nc a_t1 a_t2 c_t1 c_t2
               b_t1 b_na b_nc oriented_abc d_t2 d_na d_nc oriented_acd islo_bcd 
               islo_abd t_fl intq.
  move:Hq => [/in_triangle_imply_w_edges q_abc | 
             [/in_triangle_imply_w_edges q_acd| q_ac]];
  [by left|by right|left].
  apply (in_triangle_w_edge_edges or_abc) ;right;right.
  exists (vertices_to_edge a c).
  split => //=.
  by apply vertex_set_edge_triangle => //=;
     have : (vertices_to_triangle a b c) = (vertices_to_triangle a b c) by [];
     apply vertices_to_triangle_correct2.
move:q_e => [e [e_t q_e]].
move:t_fl => /fset2P [Ht|Ht]; 
rewrite Ht in e_t;rewrite edges_set_vertices_to_triangle in e_t => //=;
move:e_t => /fsetUP[/fset2P [He|He] | /fset1P He];
[left|right|move|left|move|right];
try (apply (in_triangle_w_edge_edges or_abc);right;right);
try (apply (in_triangle_w_edge_edges or_acd);right;right);
try (exists e;split => //=;rewrite edges_set_vertices_to_triangle) => //=;
try (apply /fsetUP); try (by right;apply /fset1P);
try (left;apply /fset2P);[by left|by right|move|move]; move:Ht => _.


move:(q_e) => Hq;rewrite He in Hq.
apply (on_edge_on_line islo_bcd) in Hq.
move:Hq => [_ [islo_bcq islo_cdq]].
move:(q_e) => Hq;rewrite He in Hq.
rewrite is_left_of_circular in islo_abd.
rewrite vertices_to_edge_sym in Hq.
apply (on_edge_on_line islo_abd) in Hq.
move:Hq => [_ [islo_daq islo_abq]].
rewrite is_left_of_circular in islo_cdq.
rewrite -is_left_of_circular in islo_daq.
case islo_acq : (is_left_of a c q);
last (move:islo_acq => /negP /negP; rewrite -is_left_or_on_change;
                                   move => islor_caq);
[right;apply in_triangle_imply_w_edges|left].
  rewrite/in_triangle.
  rewrite /vertex1 /vertex2 /vertex3 -a_acd -c_acd -d_acd.
  by apply/andP;split => //=;apply/andP;split.
apply is_lof_imply_is_lor_on_line in islo_abq.
rewrite is_left_of_circular in islo_bcq.
apply is_lof_imply_is_lor_on_line in islo_bcq.
rewrite -is_left_or_on_line_circular in islor_caq.
rewrite /in_triangle_w_edges /vertex1 /vertex2 /vertex3 -a_abc -b_abc -c_abc.
by apply /andP;split => //=;apply/andP;split.

move:(q_e) => Hq;rewrite He in Hq.
apply (on_edge_on_line islo_bcd) in Hq.
move:Hq => [_ [islo_bcq islo_cdq]].
move:(q_e) => Hq;rewrite He in Hq.
rewrite is_left_of_circular in islo_abd.
rewrite vertices_to_edge_sym in Hq.
apply (on_edge_on_line islo_abd) in Hq.
move:Hq => [_ [islo_daq islo_abq]].
rewrite is_left_of_circular in islo_cdq.
rewrite -is_left_of_circular in islo_daq.
case islo_acq : (is_left_of a c q);
last (move:islo_acq => /negP /negP; rewrite -is_left_or_on_change;
                                   move => islor_caq);
[right;apply in_triangle_imply_w_edges|left].
  rewrite/in_triangle.
  rewrite /vertex1 /vertex2 /vertex3 -a_acd -c_acd -d_acd.
  by apply/andP;split => //=;apply/andP;split.
apply is_lof_imply_is_lor_on_line in islo_abq.
rewrite is_left_of_circular in islo_bcq.
apply is_lof_imply_is_lor_on_line in islo_bcq.
rewrite -is_left_or_on_line_circular in islor_caq.
rewrite /in_triangle_w_edges /vertex1 /vertex2 /vertex3 -a_abc -b_abc -c_abc.
by apply /andP;split => //=;apply/andP;split.
Qed.


Theorem flip_edge_tr3v tr data: triangulation tr data -> 
                                    forall t1, forall t2, t1 != t2 -> t1 \in tr->t2 \in tr ->
                                    forall a, forall c, a != c -> a \in vertex_set t1 ->
                                     a \in vertex_set t2 ->
                                     c \in vertex_set t1 -> c \in vertex_set t2 ->
                                    forall b, b \in vertex_set t1 -> b != a -> b != c ->
                                     is_left_of a b c ->
                                     forall d, d \in vertex_set t2 -> d != a -> d != c ->
                                     is_left_of a c d -> 
                                     is_left_of b c d ->
                                     is_left_of a b d ->
                                     triangle_3vertices_tr (flip_edge tr t1 t2 a b c d).
Proof.
move => tr_d t1 t2 t1_nt2 t1_tr t2_tr a c a_nc a_t1 a_t2 c_t1 c_t2.
move => b b_t1 b_na b_nc oriented_abc d d_t2 d_na d_nc oriented_acd islo_bcd islo_abd.
move:(tr_d) => [tr3v_tr_d [cvh_tr_d [cvv_tr_d [nci_tr_d nps_tr_d]]]].
have vc_abd := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line islo_abd).
have vc_bcd := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line islo_bcd).
move : (vc_abd) => [a_abd [b_abd d_abd]].
move : (vc_bcd) => [b_bcd [c_bcd d_bcd]].
move => t t_fl.
move:t_fl => /fsetUP [Ht|/fsetD1P [_ /fsetD1P[_ t_tr]]];last first.
  by apply:tr3v_tr_d.
by move:Ht=> /fset2P[Ht|Ht];
move => [[|[|[|x']]] px] [[|[|[|y']]] py] => vtx_vty //=;
try (by apply ord_inj);
try (have ordpx :Ordinal px = ord30 by apply ord_inj);
try (have ordpx :Ordinal px = ord31 by apply ord_inj);
try (have ordpx :Ordinal px = ord32 by apply ord_inj);
try (have ordpy :Ordinal py = ord30 by apply ord_inj);
try (have ordpy :Ordinal py = ord31 by apply ord_inj);
try (have ordpy :Ordinal py = ord32 by apply ord_inj);
rewrite ordpx ordpy Ht in vtx_vty;
try(rewrite -a_abd in vtx_vty);
try(rewrite -b_abd in vtx_vty);
try(rewrite -d_abd in vtx_vty);
try(rewrite -b_bcd in vtx_vty);
try(rewrite -c_bcd in vtx_vty);
try(rewrite -d_bcd in vtx_vty);
[rewrite vtx_vty in b_na;move:b_na => /eqP|
rewrite vtx_vty in d_na;move:d_na => /eqP|
rewrite vtx_vty in b_na;move:b_na => /eqP|
move|
rewrite vtx_vty in d_na;move:d_na => /eqP|
move|
rewrite vtx_vty in b_nc;move:b_nc => /eqP|
move|
rewrite vtx_vty in b_nc;move:b_nc => /eqP|
rewrite vtx_vty in d_nc;move:d_nc => /eqP|
move|
rewrite vtx_vty in d_nc;move:d_nc => /eqP]=>//=;
move:islo_bcd;
rewrite  is_left_of_circular /is_left_of vtx_vty oriented_surface_x_x ltrr.
Qed.


Theorem flip_edge_cvh tr data:  triangulation tr data -> 
                                forall t1, forall t2, t1 != t2 -> t1 \in tr->t2 \in tr ->
                                forall a, forall c, a != c -> a \in vertex_set t1 ->
                                a \in vertex_set t2 ->
                                c \in vertex_set t1 -> c \in vertex_set t2 ->
                                forall b, b \in vertex_set t1 -> b != a -> b != c ->
                                is_left_of a b c ->
                                forall d, d \in vertex_set t2 -> d != a -> d != c ->
                                is_left_of a c d -> is_left_of b c d ->
                                is_left_of a b d ->
                                covers_hull (flip_edge tr t1 t2 a b c d) data.
Proof.
move => tr_d t1 t2 t1_nt2 t1_tr t2_tr a c a_nc a_t1 a_t2 c_t1 c_t2.
move => b b_t1 b_na b_nc oriented_abc d d_t2 d_na d_nc oriented_acd islo_bcd islo_abd.
move:(tr_d) => [tr3v_tr_d [cvh_tr_d [cvv_tr_d [nci_tr_d nps_tr_d]]]].
have vc_abd := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line islo_abd).
have vc_bcd := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line islo_bcd).
move : (vc_abd) => [a_abd [b_abd d_abd]].
move : (vc_bcd) => [b_bcd [c_bcd d_bcd]].
move => p hull_d_p.
move:(hull_d_p) => /cvh_tr_d [t [t_tr intwetp]]. 
case t_t1 : (t==t1);case t_t2 : (t==t2);
move:t_t1 => /eqP t_t1;move:t_t2 => /eqP t_t2.
      rewrite t_t1 in t_t2.
      by rewrite t_t2 in t1_nt2;move:t1_nt2 => /eqP.
    rewrite t_t1 in intwetp.  
    have flip_aux:= (flip_edge_covers_aux tr_d t1_nt2 t1_tr t2_tr a_nc a_t1 a_t2
           c_t1 c_t2 b_t1 b_na b_nc oriented_abc d_t2 d_na d_nc oriented_acd
           islo_bcd islo_abd intwetp). 
    move:(flip_aux) => [t3 [flip_aux_t3 intwet3p]].
    by exists t3;split => //=;apply /fsetUP;left.
  rewrite t_t2 in intwetp.  
  rewrite eq_sym in t1_nt2;rewrite eq_sym in a_nc.
  rewrite -is_left_of_circular in oriented_acd.
  rewrite is_left_of_circular in oriented_abc.
  rewrite is_left_of_circular in  islo_abd.
  rewrite -is_left_of_circular in  islo_bcd.
  have flip_aux:= (flip_edge_covers_aux tr_d t1_nt2 t2_tr t1_tr a_nc c_t2 
                   c_t1 a_t2 a_t1 d_t2 d_nc d_na oriented_acd b_t1 b_nc b_na
                   oriented_abc islo_abd islo_bcd intwetp).
  move:(flip_aux) => [t3 [flip_aux_t3 intwet3p]].
    move:flip_aux_t3 => /fset2P [H|H];
    rewrite H in intwet3p.
      apply (vertices_to_triangle_circular_w_edges islo_bcd) in intwet3p.
      exists (vertices_to_triangle b c d) ;split => //=;apply /fsetUP;left;
      by apply /fset2P;right.
    apply (vertices_to_triangle_circular_w_edges islo_abd) in intwet3p.
    apply vertices_to_triangle_circular_w_edges in intwet3p.
      exists (vertices_to_triangle a b d);split => //= ;apply /fsetUP;left;
      by apply /fset2P;left.
    by rewrite is_left_of_circular in islo_abd.
exists t.
split => //=.
apply/fsetUP;right;apply/fsetD1P;split;first by apply/eqP.
by apply/fsetD1P; split;first apply /eqP.
Qed.


Theorem flip_edge_cvv tr data: triangulation tr data -> 
                                forall t1, forall t2, t1 != t2 -> t1 \in tr->t2 \in tr ->
                                forall a, forall c, a != c -> a \in vertex_set t1 ->
                                a \in vertex_set t2 ->
                                c \in vertex_set t1 -> c \in vertex_set t2 ->
                                forall b, b \in vertex_set t1 -> b != a -> b != c ->
                                is_left_of a b c ->
                                forall d, d \in vertex_set t2 -> d != a -> d != c ->
                                is_left_of a c d -> 
                                is_left_of b c d ->
                                is_left_of a b d ->
                                covers_vertices (flip_edge tr t1 t2 a b c d) data.
Proof.
move => tr_d t1 t2 t1_nt2 t1_tr t2_tr a c a_nc a_t1 a_t2 c_t1 c_t2.
move => b b_t1 b_na b_nc oriented_abc d d_t2 d_na d_nc oriented_acd islo_bcd islo_abd.
move:(tr_d) => [tr3v_tr_d [cvh_tr_d [cvv_tr_d [nci_tr_d nps_tr_d]]]].
have vc_abd := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line islo_abd).
have vc_bcd := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line islo_bcd).
move : (vc_abd) => [a_abd [b_abd d_abd]].
move : (vc_bcd) => [b_bcd [c_bcd d_bcd]].

 move => p.
    split.
      move => p_d.
      move:(p_d) => /cvv_tr_d [t [t_tr p_vt]].
      case t_t1 : (t==t1);case t_t2 : (t==t2);
        move:t_t1 => /eqP t_t1;move:t_t2 => /eqP t_t2.
          rewrite t_t1 in t_t2.
            by rewrite t_t2 in t1_nt2;move:t1_nt2 => /eqP.
          have injvt1 := tr3v_tr_d t1 t1_tr.
          have abc_vt1 := (vertices_vt b_na b_nc a_nc injvt1 a_t1 b_t1 c_t1).
          rewrite t_t1 -abc_vt1 in p_vt.
        pose u1 := vertices_to_triangle a b d;
        pose u2 := vertices_to_triangle b c d;
        have u1_v : u1 = vertices_to_triangle a b d by [];
        have u2_v : u2 = vertices_to_triangle b c d by [];
        apply vertices_to_triangle_correct2 in u1_v;
        apply vertices_to_triangle_correct2 in u2_v;
        move:u1_v => [u1_v1 [u1_v2 u1_v3]];
        move:u2_v => [u2_v1 [u2_v2 u2_v3]].
        move:p_vt => /fset1UP [-> | /fset2P [-> | ->]];
        [exists u1 | exists u1 | exists u2];split => //=; apply /fsetUP;left;
        apply /fset1UP;rewrite /u1;[left|left|right] => //=.
        by apply /fset1P.
      have injvt2 := tr3v_tr_d t2 t2_tr.
      rewrite eq_sym in a_nc.
      rewrite eq_sym in d_nc.
      rewrite eq_sym in d_na.
      have abc_vt2 := (vertices_vt a_nc d_nc d_na injvt2 a_t2 c_t2 d_t2).
      rewrite t_t2 -abc_vt2 in p_vt.
      pose u1 := vertices_to_triangle a b d;
      pose u2 := vertices_to_triangle b c d;
      have u1_v : u1 = vertices_to_triangle a b d by [];
      have u2_v : u2 = vertices_to_triangle b c d by [];
      apply vertices_to_triangle_correct2 in u1_v;
      apply vertices_to_triangle_correct2 in u2_v;
      move:u1_v => [u1_v1 [u1_v2 u1_v3]];
      move:u2_v => [u2_v1 [u2_v2 u2_v3]].
      move:p_vt => /fset1UP [-> | /fset2P [-> | ->]];
      [exists u1 | exists u2 | exists u2];split => //=; apply /fsetUP;left;
      apply /fset1UP;rewrite /u1;[left|right|right] => //=;by apply /fset1P.
    exists t.
    split => //=.
    apply/fsetUP;right;apply/fsetD1P;split;first by apply/eqP.
    by apply/fsetD1P; split;first apply /eqP.
  move => [t [t_spl p_vset_t]].

move:t_spl=>/fsetUP [Ht |  /fsetD1P [t_nt2 /fsetD1P [t_nt1 t_tr]]];apply cvv_tr_d.
  move:vc_abd => [abd0 [abd1 abd2]].
  move:vc_bcd => [bcd0 [bcd1 bcd2]].
  by move : Ht => /fset2P [t_v | t_v];rewrite t_v in p_vset_t;
  move:p_vset_t => /imfsetP [[[|[|[|x']]] px] _] p_vx => //=;
  [have ordpx:Ordinal px = ord30|have ordpx:Ordinal px = ord31|
   have ordpx:Ordinal px = ord32|have ordpx:Ordinal px = ord30|
   have ordpx:Ordinal px = ord31|have ordpx:Ordinal px = ord32];
  (try  apply ord_inj) => //=; rewrite ordpx in p_vx;
  [exists t1 | exists t1 | exists t2 |exists t1|exists t1|exists t2];split => //=;
  rewrite p_vx;
  [rewrite -abd0|rewrite -abd1|rewrite -abd2|
   rewrite -bcd0|rewrite -bcd1|rewrite -bcd2].
exists t;split => //=.
Qed.

Theorem flip_edge_nci tr data: triangulation tr data -> 
                               forall t1, forall t2, t1 != t2 -> t1 \in tr->t2 \in tr ->
                               forall a, forall c, a != c -> a \in vertex_set t1 ->
                               a \in vertex_set t2 ->
                               c \in vertex_set t1 -> c \in vertex_set t2 ->
                               forall b, b \in vertex_set t1 -> b != a -> b != c ->
                               is_left_of a b c ->
                               forall d, d \in vertex_set t2 -> d != a -> d != c ->
                               is_left_of a c d -> is_left_of b c d ->
                               is_left_of a b d ->
                               no_cover_intersection (flip_edge tr t1 t2 a b c d) data.
Proof.
move => tr_d t1 t2 t1_nt2 t1_tr t2_tr a c a_nc a_t1 a_t2 c_t1 c_t2.
move => b b_t1 b_na b_nc oriented_abc d d_t2 d_na d_nc oriented_acd islo_bcd islo_abd.
move:(tr_d) => [tr3v_tr_d [cvh_tr_d [cvv_tr_d [nci_tr_d [nps_tr_d [tne_tr_d or_tr_d]]]]]].
have vc_abd := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line islo_abd).
have vc_bcd := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line islo_bcd).
move : (vc_abd) => [a_abd [b_abd d_abd]].
move : (vc_bcd) => [b_bcd [c_bcd d_bcd]].
move => t3 t4 t3_spl t4_spl p int3p int4p.
have not_in_both_triangles:in_triangle (vertices_to_triangle a b d) p ->
       in_triangle (vertices_to_triangle b c d) p -> false.
  move => p_abd p_bcd.
  rewrite /in_triangle /vertex1 /vertex2 /vertex3
  -a_abd -b_abd -d_abd in p_abd.
  move:p_abd => /andP [/andP[islo_abp islo_pbd] islo_apd].
  rewrite /in_triangle /vertex1 /vertex2 /vertex3
  -b_bcd -c_bcd -d_bcd in p_bcd.
  move:p_bcd => /andP [/andP[islo_bcp islo_pcd] islo_bpd].
  rewrite  is_left_of_change in islo_bpd.
  apply is_lof_imply_is_lor_on_line in islo_pbd.
  by rewrite islo_pbd in islo_bpd.

have vc_abc := vertices_to_triangle_correct
                       (is_lof_imply_is_lor_on_line oriented_abc).
have vc_acd := vertices_to_triangle_correct
                       (is_lof_imply_is_lor_on_line oriented_acd).
move : (vc_abc) => [a_abc [b_abc c_abc]].
move : (vc_acd) => [a_acd [c_acd d_acd]].

have infl := in_flip_edge_aux tr_d t1_nt2 t1_tr t2_tr a_nc a_t1 a_t2 c_t1 c_t2
b_t1 b_na b_nc oriented_abc d_t2 d_na d_nc oriented_acd islo_bcd islo_abd.

move:t3_spl => /fsetUP [Ht3 | /fsetD1P [t3_nt2 /fsetD1P [t3_nt1 t3_tr]]];
move:t4_spl => /fsetUP [Ht4 | /fsetD1P [t4_nt2 /fsetD1P [t4_nt1 t4_tr]]].
move:Ht3 => /fset2P [Ht3|Ht3];move:Ht4=>/fset2P [Ht4|Ht4];
    (try by rewrite Ht3 Ht4); rewrite Ht3 in int3p;rewrite Ht4 in int4p.
        by have:false by apply not_in_both_triangles.
      by have temp:=(not_in_both_triangles int4p int3p).

    have temp := infl t3 Ht3 p int3p.
    move:temp => [Htp|[Htp|Htp]];
    try have intxp := (in_vert_to_triangle_in_triangle oriented_abc
                      a_t1 (is_lof_imply_is_lor_on_line (or_tr_d t1 t1_tr)) b_t1 c_t1 Htp);
    try have intxp := (in_vert_to_triangle_in_triangle oriented_acd
                      a_t2 (is_lof_imply_is_lor_on_line (or_tr_d t2 t2_tr)) c_t2 d_t2 Htp);
    try have abst1 := nci_tr_d t1 t4 t1_tr t4_tr p intxp int4p;
    try have abst2 := nci_tr_d t2 t4 t2_tr t4_tr p intxp int4p;
    [move:t4_nt1|move:t4_nt2|move];try rewrite -abst1;try rewrite -abst2;
    try move /eqP => //=.
    have ac_edge_t1 := vertex_set_edge_triangle a_t1 c_t1 a_nc.
    have temp := in_triangle_on_edge int4p (tne_tr_d t1 t1_tr) ac_edge_t1 Htp.
    move:temp => [q [int4q int1q]].
    have abs := nci_tr_d t1 t4 t1_tr t4_tr q int1q int4q.
    by move:t4_nt1;rewrite abs;move => /eqP.
  have temp := infl t4 Ht4 p int4p.
  move:temp => [Htp|[Htp|Htp]];
  try have intxp := (in_vert_to_triangle_in_triangle oriented_abc
                      a_t1 (is_lof_imply_is_lor_on_line (or_tr_d t1 t1_tr)) b_t1 c_t1 Htp);
  try have intxp := (in_vert_to_triangle_in_triangle oriented_acd
                      a_t2 (is_lof_imply_is_lor_on_line (or_tr_d t2 t2_tr)) c_t2 d_t2 Htp);
  try have abst1 := nci_tr_d t1 t3 t1_tr t3_tr p intxp int3p;
  try have abst2 := nci_tr_d t2 t3 t2_tr t3_tr p intxp int3p;
  [move:t3_nt1|move:t3_nt2|move];try rewrite -abst1;try rewrite -abst2;
  try move /eqP => //=.
  have ac_edge_t1 := vertex_set_edge_triangle a_t1 c_t1 a_nc.
  have temp := in_triangle_on_edge int3p (tne_tr_d t1 t1_tr) ac_edge_t1 Htp.
  move:temp => [q [int3q int1q]].
  have abs := nci_tr_d t1 t3 t1_tr t3_tr q int1q int3q.
  by move:t3_nt1;rewrite abs;move => /eqP.
apply:nci_tr_d => //=.
apply int3p => //=.
by [].
Qed.


Theorem flip_edge_nps tr data : triangulation tr data -> 
                                forall t1, forall t2, t1 != t2 -> t1 \in tr->t2 \in tr ->
                                forall a, forall c, a != c -> a \in vertex_set t1 ->
                                a \in vertex_set t2 ->
                                c \in vertex_set t1 -> c \in vertex_set t2 ->
                                forall b, b \in vertex_set t1 -> b != a -> b != c ->
                                 is_left_of a b c ->
                                 forall d, d \in vertex_set t2 -> d != a -> d != c ->
                                 is_left_of a c d -> is_left_of b c d ->
                                 is_left_of a b d ->
                       no_point_on_segment (flip_edge tr t1 t2 a b c d) data.
Proof.
move => tr_d t1 t2 t1_nt2 t1_tr t2_tr a c a_nc a_t1 a_t2 c_t1 c_t2.
move => b b_t1 b_na b_nc oriented_abc d d_t2 d_na d_nc oriented_acd islo_bcd islo_abd.
move:(tr_d) => [tr3v_tr_d [cvh_tr_d [cvv_tr_d [nci_tr_d [nps_tr_d [tne_tr_d or_tr_d]]]]]].
have vc_abd := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line islo_abd).
have vc_bcd := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line islo_bcd).
move : (vc_abd) => [a_abd [b_abd d_abd]].
move : (vc_bcd) => [b_bcd [c_bcd d_bcd]].
move => t3 t4 t3_fl t4_fl p p_t3 int4p.


move:t3_fl => /fsetUP [Ht3 | /fsetD1P [t3_nt2 /fsetD1P [t3_nt1 t3_tr]]];
move:t4_fl => /fsetUP [Ht4 | /fsetD1P [t4_nt2 /fsetD1P [t4_nt1 t4_tr]]];
last first.
      by apply:(nps_tr_d t3 t4 t3_tr t4_tr p).
    have intp := in_flip_edge_aux_we tr_d t1_nt2 t1_tr t2_tr
      a_nc a_t1 a_t2 c_t1 c_t2 b_t1 b_na b_nc oriented_abc 
      d_t2 d_na d_nc oriented_acd islo_bcd islo_abd Ht4 int4p.
    have v_abc_t1 :  vertex_set (vertices_to_triangle a b c)= vertex_set t1.
      rewrite vertex_set_vertices_to_triangle.
      apply /eqP.
      have card_fset3 : #|` [fset a; b; c] | = 3%N.
        have card_fset2 : #|` [fset a; b] | = 2%N.
          rewrite cardfs2.
          move:b_na => /negP. rewrite eq_sym. by move => /negP -> .
        have abIc0: [fset a; b] `&` [fset c] = fset0.
            apply disjoint_fsetI0.
            rewrite fdisjointX1.
            apply /negP.
            case abs:(c \in [fset a;b])=> //=.
            move:abs => /fset2P [abs|abs];
            [rewrite abs in a_nc|rewrite abs in b_nc];
            [move:a_nc => /negP |move:b_nc => /negP] => //=.
        have card_abIc0:#|` [fset a; b] `&` [fset c]| = 0%N.
          rewrite abIc0.
          by apply cardfs0.
        
        by rewrite cardfsU card_fset2 cardfs1 card_abIc0.
      have injvt1 := tr3v_tr_d t1 t1_tr.
      have cardvt1 : (#|` [fset (vertex t1) x | x in 'I_3]| = #|` finset 'I_3|).
        apply:card_in_imfset.
        move => x y px py.
        apply:injvt1.
      have card_eq : #|` [fset a; b; c] | = #|` vertex_set t1 |.
        by rewrite card_fset3 cardvt1 card_finset card_ord.
      have fsubset_cardvt1P := (fsubset_cardP card_eq).
      apply /eqP. apply fsetP.
      apply /fsubset_cardvt1P.
      apply /fsubsetP.
      move => x.
      by move=>/fsetUP [/fset2P [->|->]|/fset1P ->  //=].

    have v_acd_t2 :  vertex_set (vertices_to_triangle a c d)= vertex_set t2.
      rewrite vertex_set_vertices_to_triangle.
      apply /eqP.
      have card_fset3 : #|` [fset a; c; d] | = 3%N.
        have card_fset2 : #|` [fset a; c] | = 2%N.
          rewrite cardfs2.
          move:a_nc => /negP. rewrite eq_sym. by move => /negP -> .
        have abIc0: [fset a; c] `&` [fset d] = fset0.
            apply disjoint_fsetI0.
            rewrite fdisjointX1.
            apply /negP.
            case abs:(d \in [fset a;c])=> //=.
            move:abs => /fset2P [abs|abs];
            [rewrite abs in d_na|rewrite abs in d_nc];
            [move:d_na => /negP |move:d_nc => /negP] => //=.
        have card_abIc0:#|` [fset a; c] `&` [fset d]| = 0%N.
          rewrite abIc0.
          by apply cardfs0.
        by rewrite cardfsU card_fset2 cardfs1 card_abIc0.
      have injvt2 := tr3v_tr_d t2 t2_tr.
      have cardvt2 : (#|` [fset (vertex t2) x | x in 'I_3]| = #|` finset 'I_3|).
        apply:card_in_imfset.
        move => x y px py.
        apply:injvt2.
      have card_eq : #|` [fset a; c; d] | = #|` vertex_set t2 |.
        by rewrite card_fset3 cardvt2 card_finset card_ord.
      have fsubset_cardvt2P := (fsubset_cardP card_eq).
      apply /eqP. apply fsetP.
      apply /fsubset_cardvt2P.
      apply /fsubsetP.
      move => x.
      by move=>/fsetUP [/fset2P [->|->]|/fset1P ->  //=].



    by move:intp => [Hintp|Hintp];
    [have intp : in_triangle_w_edges t1 p|have intp : in_triangle_w_edges t2 p];
      [by apply:(vertex_set_eq_in_triangle_w_edges (vertices_to_triangle_oriented a b c)
       (is_lof_imply_is_lor_on_line (or_tr_d t1 t1_tr)) v_abc_t1)|
       move|by apply:(vertex_set_eq_in_triangle_w_edges (vertices_to_triangle_oriented a c d)
       (is_lof_imply_is_lor_on_line (or_tr_d t2 t2_tr)) v_acd_t2)|move];
    [have p_t := nps_tr_d t3 t1 t3_tr t1_tr p p_t3 intp|
     have p_t := nps_tr_d t3 t2 t3_tr t2_tr p p_t3 intp];
    [rewrite -v_abc_t1 in p_t|rewrite -v_acd_t2 in p_t];
    apply in_vertex_set in p_t;move:p_t => [/eqP Hp|[/eqP Hp|/eqP Hp]];
    rewrite Hp;
    move:Ht4 => /fset2P [Ht4|Ht4];rewrite Ht4;apply in_vertex_set;
    [left|move|right;left|left|move|right;left|left|move|move|right;left|right;right|right;right]
    => //=; rewrite Hp in int4p;rewrite Ht4 in int4p;
    rewrite /in_triangle_w_edges /vertex1 /vertex2 /vertex3 in int4p;
    [rewrite -b_bcd -c_bcd -d_bcd in int4p|
     rewrite -a_abd -b_abd -d_abd in int4p|
     rewrite -b_bcd -c_bcd -d_bcd in int4p|
     rewrite -a_abd -b_abd -d_abd in int4p];
    move:int4p => /andP ;
    [move => [_ abs]|move => [/andP[_ abs] _]|
     move => [_ abs]|move => [/andP[_ abs] _] ];
    rewrite is_left_or_on_change in abs;
    try rewrite islo_abd in abs;
    try rewrite islo_bcd in abs.
  have p_t1_t2 : p\in vertex_set t1 \/ p\in vertex_set t2.
    by move:Ht3 => /fset2P [Ht3|Ht3];
    rewrite Ht3 in p_t3;apply in_vertex_set in p_t3;
    move:p_t3 => [/eqP ->|[/eqP ->|/eqP ->]];
    [left|left|right|left|left|right].
  move:p_t1_t2 => [Hp|Hp].
    by apply:(nps_tr_d t1 t4 t1_tr t4_tr).
  by apply:(nps_tr_d t2 t4 t2_tr t4_tr).
move:Ht3=>/fset2P[Ht3|Ht3];move:Ht4=>/fset2P[Ht4|Ht4];
[have t4_t3 :t4=t3 by rewrite Ht3 Ht4|move|move|
 have t4_t3:t4=t3 by rewrite Ht3 Ht4];
try by rewrite t4_t3.

  rewrite Ht3 in p_t3.
  apply in_vertex_set in p_t3; 
  move:p_t3 => [/eqP Hp | [/eqP Hp | /eqP Hp]];
  rewrite Ht4 Hp;  apply in_vertex_set;[move|left|right;right] => //=.
  rewrite Hp Ht4 in int4p.
  rewrite /in_triangle_w_edges /vertex1 /vertex2 /vertex3 in int4p.
  rewrite -b_bcd -c_bcd -d_bcd in int4p.
  move:int4p => /andP[_ abs].
  rewrite is_left_or_on_change in abs.
  by rewrite islo_abd in abs.
rewrite Ht3 in p_t3.
apply in_vertex_set in p_t3; 
move:p_t3 => [/eqP Hp | [/eqP Hp | /eqP Hp]];
rewrite Ht4 Hp;  apply in_vertex_set;[right;left|move|right;right] => //=.
rewrite Hp Ht4 in int4p.
rewrite /in_triangle_w_edges /vertex1 /vertex2 /vertex3 in int4p.
rewrite -a_abd -b_abd -d_abd in int4p.
move:int4p => /andP[/andP[_ abs] _].
rewrite is_left_or_on_change in abs.
by rewrite islo_bcd in abs.
Qed.

Theorem flip_edge_tne tr data : triangulation tr data -> 
                                forall t1, forall t2, t1 != t2 -> t1 \in tr->t2 \in tr ->
                                forall a, forall c, a != c -> a \in vertex_set t1 ->
                                 a \in vertex_set t2 ->
                                 c \in vertex_set t1 -> c \in vertex_set t2 ->
                                forall b, b \in vertex_set t1 -> b != a -> b != c ->
                                 is_left_of a b c ->
                                 forall d, d \in vertex_set t2 -> d != a -> d != c ->
                                 is_left_of a c d -> is_left_of b c d ->
                                 is_left_of a b d ->
                         triangles_nempty (flip_edge tr t1 t2 a b c d).
Proof.
move => tr_d t1 t2 t1_nt2 t1_tr t2_tr a c a_nc a_t1 a_t2 c_t1 c_t2.
move => b b_t1 b_na b_nc oriented_abc d d_t2 d_na d_nc oriented_acd islo_bcd islo_abd.
move:(tr_d) => [tr3v_tr_d [cvh_tr_d [cvv_tr_d [nci_tr_d [nps_tr_d [tne_tr_d or_tr_d]]]]]].


move => t t_fl.
move:t_fl => /fsetUP [Ht|/fsetD1P[t_nt2 /fsetD1P [t_nt1 t_tr]]];last first.
  by have temp := tne_tr_d t t_tr.
move:Ht => /fset2P [->|->];
by apply surface_non_empty.
Qed.

Theorem flip_edge_or tr data : triangulation tr data -> 
                               forall t1, forall t2, t1 != t2 -> t1 \in tr->t2 \in tr ->
                                    forall a, forall c, a != c -> a \in vertex_set t1 ->
                                     a \in vertex_set t2 ->
                                     c \in vertex_set t1 -> c \in vertex_set t2 ->
                                    forall b, b \in vertex_set t1 -> b != a -> b != c ->
                                     is_left_of a b c ->
                                     forall d, d \in vertex_set t2 -> d != a -> d != c ->
                                     is_left_of a c d -> 
                                     is_left_of b c d ->
                                     is_left_of a b d ->
                                     oriented_triangle_triangulation
                                       (flip_edge tr t1 t2 a b c d).
Proof.
move => tr_d t1 t2 t1_nt2 t1_tr t2_tr a c a_nc a_t1 a_t2 c_t1 c_t2.
move => b b_t1 b_na b_nc oriented_abc d d_t2 d_na d_nc oriented_acd islo_bcd islo_abd.
move:(tr_d) => [tr3v_tr_d [cvh_tr_d [cvv_tr_d [nci_tr_d [nps_tr_d [tne_tr_d or_tr_d]]]]]].
move => t.
rewrite /flip_edge.
move => /fsetUP [];last by move => /fsetD1P [] _ /fsetD1P [] _;apply or_tr_d.
rewrite /flip_edge_aux.
by move => /fset2P [] ->;
[have vc := vertices_to_triangle_correct (is_lof_imply_is_lor_on_line islo_abd)|
 have vc := vertices_to_triangle_correct (is_lof_imply_is_lor_on_line islo_bcd)];
move:vc => [v1[v2 v3]];rewrite /oriented_triangle_strict /vertex1 /vertex2 /vertex3 -v1 -v2 -v3.
Qed.

Theorem flip_edge_triangulation tr data : triangulation tr data -> 
                                    forall t1, forall t2, t1 != t2 -> t1 \in tr->t2 \in tr ->
                                    forall a, forall c, a != c -> a \in vertex_set t1 ->
                                     a \in vertex_set t2 ->
                                     c \in vertex_set t1 -> c \in vertex_set t2 ->
                                    forall b, b \in vertex_set t1 -> b != a -> b != c ->
                                     is_left_of a b c ->
                                     forall d, d \in vertex_set t2 -> d != a -> d != c ->
                                     is_left_of a c d -> 
                                     is_left_of b c d ->
                                     is_left_of a b d ->
                                     triangulation (flip_edge tr t1 t2 a b c d) data.
Proof.

move => tr_d t1 t2 t1_nt2 t1_tr t2_tr a c a_nc a_t1 a_t2 c_t1 c_t2.
move => b b_t1 b_na b_nc oriented_abc d d_t2 d_na d_nc oriented_acd islo_bcd islo_abd.
move:(tr_d) => [tr3v_tr_d [cvh_tr_d [cvv_tr_d [nci_tr_d nps_tr_d]]]].
have vc_abd := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line islo_abd).
have vc_bcd := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line islo_bcd).
move : (vc_abd) => [a_abd [b_abd d_abd]].
move : (vc_bcd) => [b_bcd [c_bcd d_bcd]].
split; first apply:flip_edge_tr3v => //=. apply tr_d.
split;first by apply flip_edge_cvh.
split;first by apply flip_edge_cvv.
split;first by apply flip_edge_nci.
split;first by apply flip_edge_nps.
split;first apply:flip_edge_tne => //=. apply tr_d.
apply:flip_edge_or => //=.
by apply tr_d.
Qed.

End Triangulation.
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

Open Scope ring_scope.

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

Variable vertices_to_edge : P -> P -> E.

Variable edge : T -> 'I_3 -> E.

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

Lemma vertices_to_triangle_correct' : forall a b c,
  is_left_or_on_line a b c ->
  exists i : 'I_3,
  a = vertex (vertices_to_triangle a b c) i /\
  b = vertex (vertices_to_triangle a b c) (i + 1) /\
  c = vertex (vertices_to_triangle a b c) (i + 2%:R).
Proof.
move => a b c abc; exists ord30; rewrite !mod3rules.
by apply:vertices_to_triangle_correct.
Qed.

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

Lemma is_left_or_on_change a b c :
        is_left_or_on_line a b c = ~~ is_left_of b a c.
Proof.
by rewrite /is_left_or_on_line /is_left_of oriented_surface_change1
oriented_surface_circular oppr_ge0 real_lerNgt => //=; apply: num_real.
Qed.

Lemma is_left_of_change a b c:
        is_left_of a b c = ~~ is_left_or_on_line b a c.
Proof.
rewrite /is_left_or_on_line /is_left_of.
rewrite oriented_surface_change1 oriented_surface_circular.
rewrite oppr_gt0.
by rewrite real_ltrNge => //=; apply: num_real.
Qed.

Lemma is_lof_imply_is_lor_on_line a b c :
    is_left_of a b c -> is_left_or_on_line a b c.
Proof.
by apply: ltrW.
Qed.

Hypothesis vertex_set_vertices_to_triangle :
  forall a b c, vertex_set (vertices_to_triangle a b c) = [fset a;b;c].

Definition in_triangle_p a b c p :=
  is_left_of a b p && is_left_of p b c && is_left_of a p c.

Definition in_triangle t p :=
  in_triangle_p (vertex1 t) (vertex2 t) (vertex3 t) p.

Hypothesis axiom4_knuth : forall a b c d, is_left_of a b d ->
                                     is_left_of b c d ->
                                     is_left_of c a d ->
                                     is_left_of a b c.

Definition in_triangle_w_edges_p a b c p :=
  is_left_or_on_line a b p && is_left_or_on_line p b c &&
  is_left_or_on_line a p c.

Definition in_triangle_w_edges t p :=
  in_triangle_w_edges_p (vertex1 t) (vertex2 t) (vertex3 t) p.

Lemma in_triangle_imply_w_edges t p : in_triangle t p ->
   in_triangle_w_edges t p.
Proof.
move => /andP [intp intp3];move:intp => /andP [intp1 intp2].
by apply/andP;split;first apply/andP;first split;apply: ltrW.
Qed.

Lemma in_triangle_circular a b c p :
   in_triangle_p a b c p = in_triangle_p b c a p.
Proof.
by rewrite /in_triangle_p andbC andbA andbC andbA !(is_left_of_circular _ p)
  !(is_left_of_circular _ _ p).
Qed.

Lemma in_triangle_w_edges_circular a b c p :
   in_triangle_w_edges_p a b c p = in_triangle_w_edges_p b c a p.
Proof.
by rewrite /in_triangle_w_edges_p andbC andbA andbC andbA
  !(is_left_or_on_line_circular _ p) !(is_left_or_on_line_circular _ _ p).
Qed.

Lemma in_triangle_w_edges_vertices_to_triangle a b c d :
  is_left_of a b c ->
  in_triangle_w_edges (vertices_to_triangle a b c) d =
  in_triangle_w_edges_p a b c d.
Proof.
move=> lof.
case: (vertices_to_triangle_correct' (is_lof_imply_is_lor_on_line lof)).
rewrite /in_triangle_w_edges /vertex1 /vertex2 /vertex3.
move => [[ | [ | [ | i]]] i3] //; rewrite !mod3rules => [[<- [<- <-]]] //.
  by rewrite in_triangle_w_edges_circular.
by rewrite -in_triangle_w_edges_circular.
Qed.

Hypothesis in_triangle_on_edge :
  forall t, forall p,   in_triangle t p ->
  forall t2, (exists p2, in_triangle t2 p2) ->
  forall e,  e \in edges_set t2 -> on_edge e p ->
  exists q,  in_triangle t q /\ in_triangle t2 q.

Hypothesis intersection_of_lines : forall a b c d,
  is_left_of a b c -> is_on_line a b d ->
  is_on_line a c d -> d = a.

(* This is Knuth's axiom 5. *)
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

Hypothesis is_left_or_line_trans2 : forall a b c d q, is_left_or_on_line c b a ->
                                           is_left_or_on_line d b a ->
                                           is_left_or_on_line q b a ->
                                           is_left_or_on_line d b q ->
                                           is_left_or_on_line c b d ->
                                           is_left_or_on_line c b q.


Lemma is_left_or_on_line_on_line a b c :
  is_left_or_on_line a b c -> is_left_or_on_line a c b -> is_on_line a b c.
Proof.
rewrite /is_left_or_on_line => Habc.
rewrite oriented_surface_change1 ler_oppr oppr0 => Habc2.
by rewrite /is_on_line;apply/eqP;symmetry;apply/eqP;
rewrite eqr_le Habc;apply/andP;split.
Qed.

Hypothesis vertex_set_edge_triangle :
  forall t, forall a, a \in vertex_set t ->  forall b, b \in vertex_set t -> a!=b ->
            (vertices_to_edge a b) \in edges_set t.

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
try (by apply: is_lof_imply_is_lor_on_line;easygeo_aux);
try (by apply: is_ol_imply_islor;easygeo_aux).

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
  [exists (vertices_to_edge (vertex3 t) (vertex1 t)); set u := vertex2 t|
   exists (vertices_to_edge (vertex2 t) (vertex3 t)); set u := vertex1 t|
   exists (vertices_to_edge (vertex1 t) (vertex2 t)); set u := vertex3 t];
  split => //=;
  try (apply: vertex_set_edge_triangle => //;apply/imfsetP;
  try (by exists ord30;rewrite/vertex1);
  try (by exists ord31;rewrite/vertex2);
  try (by exists ord32;rewrite/vertex3) => //=); rewrite vertices_to_edge_sym;
  apply: (@on_line_on_edge _ u); rewrite /u; easygeo.
move => [|[|]];try by apply: in_triangle_imply_w_edges.
  move: (is_lof_imply_is_lor_on_line or_t) => {or_t} or_t.
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
have [j pj] : exists j, e = vertices_to_edge (vertex t (j + 1)) (vertex t j).
  move: e_t; rewrite !inE => /orP [/orP [/eqP -> | /eqP ->] | /eqP ->].
     by exists ord30; rewrite vertices_to_edge_sym !mod3rules.
   by exists ord32; rewrite !mod3rules.
by exists ord31; rewrite vertices_to_edge_sym !mod3rules.
have lofj : is_left_of  (vertex t (j + 1)) (vertex t (j + 2%:R)) (vertex t j).
  by move: j {pj} =>  [[ | [ | [ | j]]] j3] => //; rewrite !mod3rules;
  [rewrite is_left_of_circular | rewrite -is_left_of_circular | ]; exact or_t.
have : in_triangle_w_edges_p
   (vertex t j) (vertex t (j + 1)) (vertex t (j + 2%:R)) p.
  move: (e_p); rewrite pj.
  move/on_edge_on_line: (lofj) => oe; move/oe; rewrite is_on_line_sym.
  rewrite /in_triangle_w_edges_p /vertex1 /vertex2 /vertex3.
  case => [/is_ol_imply_islor l1 [/is_lof_imply_is_lor_on_line l2
            /is_lof_imply_is_lor_on_line l3]].
  by rewrite (is_left_or_on_line_circular _ p)
         -(is_left_or_on_line_circular _ _ p) l1 l2 l3.
move: (vertices_to_triangle_correct' (is_lof_imply_is_lor_on_line or_t)).
rewrite /in_triangle_w_edges /vertex1 /vertex2 /vertex3.
by case => [[[ | [ | [ |i]]] i3]] //; rewrite !mod3rules => [[<- [ <- <-]]];
 case: j {pj lofj} => [[| [| [| j]]] j3]; rewrite ?mod3rules //
  in_triangle_w_edges_circular // in_triangle_w_edges_circular.
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
apply/andP;split;
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
(try have:Ordinal px = ord30 by apply: ord_inj);
(try have:Ordinal px = ord31 by apply: ord_inj);
(try have:Ordinal px = ord32 by apply: ord_inj) => ordpx;
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

Close Scope nat_scope.

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

Definition triangle_3vertices_tr (tr:{fset T}) :=
  forall t:T, t \in tr -> injective (vertex t).

Definition edge_disjoint_triangles (tr:{fset T}) :=
  forall t1:T, t1 \in tr -> forall e :E, e \in edges_set t1 -> forall p, on_edge e p ->
  forall t2:T, t2 \in tr -> ~(in_triangle t2 p).

Definition oriented_triangle_triangulation (tr:{fset T}) :=
  forall t:T, t \in tr -> oriented_triangle_strict t.

Lemma oriented_triangle_triangulation_3vertices tr :
  oriented_triangle_triangulation tr -> triangle_3vertices_tr tr.
Proof.
suff main: forall t, oriented_triangle_strict t -> injective (vertex t).
  by move => otr t; move/otr; apply:main.
have no_dup1 : forall a b, 0 < oriented_surface a a b = false.
  by move => a b; rewrite oriented_surface_x_x ltrr.
have no_dup2 : forall a b, 0 < oriented_surface a b a = false.
  by move => a b; rewrite oriented_surface_circular no_dup1.
have no_dup3 : forall a b, 0 < oriented_surface a b b = false.
  by move => a b; rewrite oriented_surface_circular no_dup2.
by move => t ot [[ | [ | [ | x]]] x3] [ [ | [ | [ | y]]] y3] vv ; move: vv ot;
  rewrite /oriented_triangle_strict /vertex1 /vertex2 /vertex3 ?mod3rules //;
  move => ->; rewrite ?no_dup1 ?no_dup2 ?no_dup3.
Qed.

Definition triangulation tr d := covers_hull tr d /\ covers_vertices tr d /\
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

Definition split_triangle tr t p := (split_triangle_aux t p ) `|` (tr `\ t).

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
      first apply/fset1UP.
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
      by apply: is_left_or_on_line_change1 c3.
    move:c2;rewrite /is_left_or_on_line => /negP /negP;rewrite -ltrNge.
    rewrite oriented_surface_change1 oriented_surface_circular ltr_oppl oppr0.
    move => c2.
    move:c3;rewrite /is_left_or_on_line => /negP /negP;rewrite -ltrNge.
    rewrite oriented_surface_change1 -oriented_surface_circular ltr_oppl oppr0.
    move => c3.
    move: (is_lof_imply_is_lor_on_line c2) => {c2} c2.
    move: (is_lof_imply_is_lor_on_line c3) => {c3} c3.
    have islor1 : is_left_or_on_line (vertex3 t) q (vertex1 t).
      apply: (@is_left_or_line_trans p q (vertex1 t) (vertex2 t) (vertex3 t));easygeo.
    have abs1 : is_on_line (vertex3 t) q (vertex1 t).
      rewrite /is_on_line;apply/eqP; symmetry;apply/eqP;rewrite eqr_le.
      rewrite /is_left_or_on_line in islor1.
      apply/andP;split => //=.
      by rewrite /is_left_or_on_line oriented_surface_change1 ler_oppr
              -oriented_surface_circular oppr0 in v1q3.
    have islor2 : is_left_or_on_line (vertex2 t) q (vertex3 t).
      apply: (@is_left_or_line_trans p q (vertex3 t) (vertex1 t) (vertex2 t));easygeo.
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
      apply: vert_in_triangle_w_edges.
        by [].
      by rewrite vertex_set_vertices_to_triangle !inE (eqP t3q) eqxx orbT.
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
    exists (vertices_to_triangle (vertex1 t) (vertex2 t) p);split;first by apply/fset1UP;left.
    rewrite /in_triangle_w_edges;apply/andP;split;try (apply/andP;split);
    rewrite /vertex1 /vertex2 /vertex3;
    try rewrite -!vp;
    try rewrite -!v1t;
    try rewrite -!v2t=> //=.
    rewrite oriented_surface_circular in c1.
    by apply: is_lof_imply_is_lor_on_line c1.
    move:c2;rewrite /is_left_or_on_line => /negP /negP;rewrite -ltrNge.
    rewrite oriented_surface_change1 -oriented_surface_circular ltr_oppl oppr0.
    move => c2.
    case c3 :(is_left_or_on_line p q (vertex3 t)).
      have vcp23:=vertices_to_triangle_correct vp23'.
      move:vcp23 => [vp [v2t v3t]].
      exists(vertices_to_triangle p (vertex2 t) (vertex3 t));split;
        first by apply/fset1UP;right;apply/fset2P;left.
    by rewrite /in_triangle_w_edges;apply/andP;split;try (apply/andP;split);
    rewrite /vertex1 /vertex2 /vertex3;
    try rewrite -!vp;
    try rewrite -!v3t;
    try rewrite -!v2t;
    try move: (is_lof_imply_is_lor_on_line c2) => {c2} c2.
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
    apply: vert_in_triangle_w_edges.
      by [].
    by rewrite vertex_set_vertices_to_triangle !inE (eqP t3q) eqxx orbT.
  have abs := is_on_line_trans (negbT t3q) abs1 abs2.
  move:abs;rewrite /is_on_line - oriented_surface_circular => /eqP abs.
  have tne := triangle_not_empty intp.
  by rewrite /oriented_triangle_strict abs ltrr in tne.
move=> [t1 [t1sp qt1]].
have [j pj] : exists j, 
       in_triangle_w_edges_p (vertex t j) (vertex t (j +1)) p q.
  by case/fset1UP:t1sp qt1 => [-> | /fset2P [ -> | -> ]];
  rewrite in_triangle_w_edges_vertices_to_triangle //
    /vertex1 /vertex2 /vertex3;
  [exists ord30; rewrite !mod3rules |
   exists ord31; rewrite !mod3rules -in_triangle_w_edges_circular |
   exists ord32; rewrite !mod3rules in_triangle_w_edges_circular ].
have orj12: is_left_of (vertex t j) (vertex t (j + 1)) (vertex t (j + 2%:R)).
  by case: j {pj} => [[ | [ | [ | j]]] j3] => //; rewrite !mod3rules;
  repeat (exact (triangle_not_empty intp) || rewrite is_left_of_circular).
have orj1p: is_left_of (vertex t j) (vertex t (j + 1)) p.
  by case: j {pj orj12} => [[ | [ | [ | j]]] j3] => //; rewrite !mod3rules;
  repeat (assumption || rewrite is_left_of_circular).
have orp12: is_left_of p (vertex t (j + 1)) (vertex t (j + 2%:R)).
  by case: j {pj orj12 orj1p} =>
      [[ | [ | [ | j]]] j3] => //; rewrite !mod3rules;
  repeat (assumption || rewrite is_left_of_circular).
have orjp2 : is_left_of (vertex t j) p (vertex t (j + 2%:R)).
  by case: j {pj orj12 orj1p orp12} =>
      [[ | [ | [ | j]]] j3] => //; rewrite !mod3rules;
  repeat (assumption || rewrite is_left_of_circular).
have q12 : is_left_or_on_line (vertex t (j + 1)) (vertex t (j + 2%:R)) q.
  rewrite is_left_or_on_line_circular.
  case/andP: pj => /andP [j1q q1p] jqp.
  by apply: (@is_left_or_line_trans (vertex t j) _
           _ p q) => //; apply: is_lof_imply_is_lor_on_line.
have q2j : is_left_or_on_line (vertex t (j + 2%:R)) (vertex t j) q.
  case/andP: pj => /andP [j1q q1p] jqp.
  by apply: (@is_left_or_line_trans2 (vertex t (j + 1)) _ _  p q);
    rewrite -is_left_or_on_line_circular //; apply: is_lof_imply_is_lor_on_line.
rewrite /in_triangle_w_edges /in_triangle_w_edges_p /vertex1 /vertex2 /vertex3.
move/andP: pj => [/andP [j1q _] _].
by case: j q12 q2j j1q {orj12 orj1p orjp2 orp12} => [[| [| [| j]]] j3] //;
  rewrite !mod3rules -(is_left_or_on_line_circular _ _ q)
      (is_left_or_on_line_circular _ q) => -> -> ->.
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
  rewrite /in_triangle /in_triangle_p (is_left_of_circular _ _ q)
        -(is_left_of_circular q).
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

Lemma vertex_in_split_triangle t p:
in_triangle t p -> forall t0, t0 \in split_triangle_aux t p ->
forall q, q \in vertex_set t0 -> (q \in vertex_set t \/ q=p).
move => intp t0 t0_spl q qvt0.
move:t0_spl => /fset1UP.
move=>[H|/fset2P [H|H]].
    have t_oriented : is_left_or_on_line (vertex1 t) (vertex2 t) p.
      move:(intp) => /andP [/andP [islo12p _] _].
      by apply: is_lof_imply_is_lor_on_line islo12p.
    have vertex_disj := vertices_to_triangle_correct t_oriented.
    move:vertex_disj => [v1t [v2t vp]].
    move:qvt0=>/imfsetP [[[|[|[|x']]] px] _] qvt0x=>//=;
    [pose ordx:=ord30|pose ordx:=ord31|pose ordx:=ord32];
    have temp:q = vertex t0 ordx
      by rewrite qvt0x;congr ((vertex t0) _);apply: ord_inj.
        rewrite H -v1t in temp;left;apply/imfsetP;exists ord30=>//=.
      rewrite H -v2t in temp;left;apply/imfsetP;exists ord31=>//=.
    by rewrite H -vp in temp;right.
  have t_oriented : is_left_or_on_line p (vertex2 t) (vertex3 t).
    move:intp => /andP [/andP [_ islop23] _].
    by apply: is_lof_imply_is_lor_on_line islop23.
  have vertex_disj := vertices_to_triangle_correct t_oriented.
  move:vertex_disj => [vp [v2t v3t]].
  move:qvt0=>/imfsetP [[[|[|[|x']]] px] _] qvt0x=>//=;
           [pose ordx:=ord30|pose ordx:=ord31|pose ordx:=ord32];
    have temp:q = vertex t0 ordx
    by rewrite qvt0x;congr ((vertex t0) _);apply: ord_inj.
      by rewrite H -vp in temp;right.
    by rewrite H -v2t in temp;left;apply/imfsetP;exists ord31.
  by rewrite H -v3t in temp;left;apply/imfsetP;exists ord32.
have t_oriented : is_left_or_on_line (vertex1 t) p (vertex3 t).
  move:intp => /andP [_ islo1p3].
  by apply: is_lof_imply_is_lor_on_line islo1p3.
have vertex_disj := vertices_to_triangle_correct t_oriented.
move:vertex_disj => [v1t [vp v3t]].
move:qvt0=>/imfsetP [[[|[|[|x']]] px] _] qvt0x=>//=;
         [pose ordx:=ord30|pose ordx:=ord31|pose ordx:=ord32];
  have temp:q = vertex t0 ordx
  by rewrite qvt0x;congr ((vertex t0) _);apply: ord_inj.
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
    by case/negP; apply/eqP; apply/val_inj.
  by move => jd _;  apply/codomP; exists [` jd ]; apply/val_inj.
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
      by  apply/val_inj; rewrite val_insubd ip.
    by apply: reindex.
  rewrite vp_eq (eqP f_a) (bigD1 p') //=; apply/eqP; congr (_ + _).
  apply: eq_bigr; move => [i ip] inp; congr (a _ * _); rewrite /=.
  apply: val_inj => /=; rewrite val_insubd.
  case/fset1UP: (ip); last by move => ->.
  by move => abs; case/negP: inp; apply/eqP/val_inj => /=.
exists c; split; first by apply:fun_d_p_coord.
split; first by apply:fun_d_p_coord.
split.
  rewrite big_split /= addrC -big_distrr /= (eqP bsum) mulr1.
  rewrite (eq_big (fun i => true && (h i != p'))(fun i => a (h i))(reindex_h));
    last by [].
  rewrite -(@reindex _ _ _ _ _ h (fun x => x != p') a bijh).
  by rewrite -(@bigD1 _ _ _ _ _ xpredT).
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
move:tr_d =>[covh_tr_d [covv_tr_d [_ [_ [_ or_tr_d]]]]].
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
    by move => [[| [| [| k]]] ck] //.
  rewrite (eq_bigl (fun i => false ));last by move => [[ | [ | [| i]]] ci] //.
  rewrite big_pred0_eq.
  rewrite addr0.
  by rewrite addrA.
have vert_t_i :forall i, vertex t i \in d.
  move =>i;apply /covv_tr_d;exists t;split;move => //=.
   by rewrite /vertex_set; apply:in_imfset.
have vert_0_d : vertex t ord30 \in d by apply: vert_t_i.
have vert_1_d : vertex t ord31 \in d by apply: vert_t_i.
have vert_2_d : vertex t ord32 \in d by apply: vert_t_i.
have not_2_1 : ([` vert_2_d] != [` vert_1_d]).
  case abs:([` vert_2_d] == [` vert_1_d])=> //=.
  move:abs => /eqP abs.
  have abs2:(val [` vert_2_d] = val [` vert_1_d]) by rewrite abs.
  have injvt: (injective (vertex t)).
    by apply/(oriented_triangle_triangulation_3vertices or_tr_d) .
  by move:abs2 => /= /injvt abs2.
have not_2_0 : ([` vert_2_d] != [` vert_0_d]).
  case abs:([` vert_2_d] == [` vert_0_d])=> //=.
  move:abs => /eqP abs.
  have abs2:(val [` vert_2_d] = val [` vert_0_d]) by rewrite abs.
  have injvt: (injective (vertex t)).
    by apply/(oriented_triangle_triangulation_3vertices or_tr_d).
  by move:abs2 => /= /injvt abs2.
have not_1_0 : ([` vert_1_d] != [` vert_0_d]).
  case abs:([` vert_1_d] == [` vert_0_d])=> //=.
  move:abs => /eqP abs.
  have abs2:(val [` vert_1_d] = val [` vert_0_d]) by rewrite abs.
  have injvt: (injective (vertex t)).
    by apply/(oriented_triangle_triangulation_3vertices or_tr_d).
  by move:abs2 => /= /injvt abs2.
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
  have injvt: (injective (vertex t)).
    by apply/(oriented_triangle_triangulation_3vertices or_tr_d).
  by move:val_v01 => /= /injvt val_v01.
have a'2 : a' [`vert_2_d] = a ord32. rewrite /a' => /=.
  case abs : ([`vert_2_d] == [`vert_0_d] ); move:abs => /eqP abs.
  have val_v20: val [` vert_2_d] = val [` vert_0_d] by rewrite abs.
  have injvt: (injective (vertex t)).
    by apply/(oriented_triangle_triangulation_3vertices or_tr_d).
  by move:val_v20 => /= /injvt val_v20.
  case abs2 :([`vert_2_d] == [`vert_1_d]);last by rewrite eq_refl.
  move:abs2 => /eqP abs2.
  have injvt: (injective (vertex t)).
    by apply/(oriented_triangle_triangulation_3vertices or_tr_d).
  have val_v21: val [` vert_2_d] = val [` vert_1_d] by rewrite abs2.
  by move:val_v21 => /= /injvt val_v21.
have sum0_f : forall f, \sum_(i | (i != [` vert_0_d]) && (i != [` vert_1_d])
                                            && (i != [` vert_2_d]))
               a' i * f (fsval i) = 0.
  move => f;apply: big1;move => i not_vert.
  have a'i0 : a' i = 0;first rewrite /a' => /=.
    case inv0:(i == [`vert_0_d]); rewrite inv0 in not_vert;
    case inv1:(i == [`vert_1_d]); rewrite inv1 in not_vert;
    case inv2:(i == [`vert_2_d]); rewrite inv2 in not_vert;move:not_vert=> _ //=.
  by rewrite a'i0; apply: mul0r.
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
  apply: big1;move => i not_vert.
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
    rewrite (eq_bigl (fun i => false)); first by apply: big_pred0_eq.
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
apply/fsetUP;[left|left|by right;apply/fset1P];
apply/fset2P;[left|right].
Qed.

Lemma triangulation_nci tr t p d:
  d != fset0 -> p \notin d -> triangulation tr d -> t \in tr ->
   in_triangle t p -> no_cover_intersection (split_triangle tr t p) (p |` d).
Proof.
move => dne p_nin_d tr_d t_tr intp.
move:(tr_d) => [covh_tr_d [covv_tr_d [nci_tr_d [nps_tr_d [tne_tr_d or_tr_d]]]]].
move => t1 t2 t1_spl t2_spl q int1q int2q.
move:t1_spl => /fsetUP;  move => [t1_spl|t1_spl];
move:t2_spl=> /fsetUP;move=>[t2_spl|t2_spl];last first.
      move:t1_spl => /fsetD1P [t1nt t1_tr].
      move:t2_spl => /fsetD1P [t2nt t2_tr].
      rewrite /no_cover_intersection in nci_tr_d.
      have nci_t1_t2:=(nci_tr_d t1 t2).
      apply:(nci_t1_t2) => //=.
      apply: int1q.
      apply: int2q.
    move:t1_spl => /fsetD1P [t1nt t1_tr].
    have intwet2q := (in_triangle_imply_w_edges int2q).
    have :(t2 \in split_triangle_aux t p /\ in_triangle_w_edges t2 q)=>//= _.
    have tr3c := (three_triangles_cover_one intp q).
    have intwetq : in_triangle_w_edges t q by apply /tr3c;exists t2.
    rewrite /no_cover_intersection in nci_tr_d.
    have intq := (split_aux_in_triangle intp t2_spl int2q).
    have abs := (nci_tr_d t1 t t1_tr t_tr q int1q intq).
    rewrite abs in t1nt.
    by move :t1nt => /eqP.
  move:t2_spl => /fsetD1P [t2nt t2_tr].
  have intwet1q := (in_triangle_imply_w_edges int1q).
  have :(t1 \in split_triangle_aux t p /\ in_triangle_w_edges t1 q)=>//= _.
  have tr3c := (three_triangles_cover_one intp q).
  have intwetq : in_triangle_w_edges t q by apply /tr3c;exists t1.
  rewrite /no_cover_intersection in nci_tr_d.
  have intq := (split_aux_in_triangle intp t1_spl int1q).
  have abs := (nci_tr_d t2 t t2_tr t_tr q int2q intq).
  rewrite abs in t2nt.
  by move :t2nt => /eqP.

case t1_t2 : (t2==t1);last move:t1_t2 => /eqP t1_n_t2.
  by move :t1_t2 => /eqP => ->.
move:(intp) => /andP [/andP 
 [/is_lof_imply_is_lor_on_line islo1 
  /is_lof_imply_is_lor_on_line islo2]
  /is_lof_imply_is_lor_on_line islo3].
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
          move: islo => /is_lof_imply_is_lor_on_line islo.
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
        move: islo => /is_lof_imply_is_lor_on_line islo.
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
      move: islo => /is_lof_imply_is_lor_on_line islo.
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
    move: islo => /is_lof_imply_is_lor_on_line islo.
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
  move: islo => /is_lof_imply_is_lor_on_line islo.
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
move: islo => /is_lof_imply_is_lor_on_line islo.
by rewrite islo in islor.
Qed.

Lemma triangulation_or tr t p d:
   triangulation tr d -> in_triangle t p ->
   oriented_triangle_triangulation (split_triangle tr t p).
Proof.
move => [_ [_ [_ [_ [_ or_tr_d]]]]] intp t' t'_spl.
move:t'_spl;rewrite /split_triangle => /fsetUP [];
   last by move => /fsetD1P [] _;apply:or_tr_d.
have [h g] := (is_lof_imply_is_lor_on_line, vertices_to_triangle_correct).
move:intp => /andP [] /andP [] islo1 islo2 islo3.
by rewrite /split_triangle_aux => /fset1UP [-> | /fset2P [] ->];
rewrite /oriented_triangle_strict;
[move/h/g:(islo1) => vc| move/h/g:(islo2) => vc| move/h/g:(islo3) => vc];
move:vc => [vc1 [vc2 vc3]];rewrite /vertex1 /vertex2 /vertex3 -vc1 -vc2 -vc3.
Qed.

Lemma triangulation_nps tr t p d:
d != fset0 -> p \notin d -> triangulation tr d -> t \in tr ->
in_triangle t p ->no_point_on_segment (split_triangle tr t p) (p |` d).
Proof.
move => dne p_nin_d tr_d t_tr intp.
move:(tr_d) =>
      [covh_tr_d [covv_tr_d [nci_tr_d [nps_tr_d [tne_tr_d or_tr_d]]]]].
have injvt : forall t1, t1 \in split_triangle tr t p -> injective (vertex t1).
  move => t0 int0; apply:(oriented_triangle_triangulation_3vertices _ int0).
  by apply/(triangulation_or tr_d intp).
move => t1 t2 t1_spl t2_spl q qvt1 intwet2q.
move/fsetUP : t1_spl => [t1_spl | /fsetD1P [t1_nt t1_tr]];
move/fsetUP : t2_spl => [t2_spl | /fsetD1P [t2_nt t2_tr]];last first.
      by apply: (nps_tr_d t1 t2 t1_tr t2_tr q qvt1).
    have intwetq := (split_aux_in_triangle_we intp t2_spl intwet2q).
    have q_vt := (nps_tr_d t1 t t1_tr t_tr q qvt1 intwetq).
    have or_t2 := split_triangle_aux_oriented intp t2_spl.
    move:(intwet2q) => /(in_triangle_w_edge_edges or_t2 q) q_disj.
    move:q_disj => [q_vt2 | [int2q | t2e]] => //=.
      move: (in_triangle_not_vert (split_aux_in_triangle intp t2_spl int2q)).
      by rewrite q_vt.
    move:t2e => [e [e_t2 int2e]].
    case: (on_edge_split_triangle intp t2_spl e_t2 int2e) =>
            [intq | [e0 [e0_t q_e0]]]; last first.
      have h := is_lof_imply_is_lor_on_line (or_tr_d t t_tr).
      by move:(vert_not_on_edges h q_vt e0_t q_e0).
    by move: (in_triangle_not_vert intq); rewrite q_vt.
  have oriented_t1 : oriented_triangle t1.
    by move:t1_spl => /fset1UP [|/fset2P []] ->;
         apply:vertices_to_triangle_oriented.
  have intwet1q := (vert_in_triangle_w_edges oriented_t1 qvt1).
  have intwetq : in_triangle_w_edges t q.
        by apply: (split_aux_in_triangle_we intp t1_spl).
  have [qvt | q_p] : q \in vertex_set t \/ q = p.
      by apply: (vertex_in_split_triangle intp t1_spl).
    by apply:(nps_tr_d t).
  move/(in_triangle_w_edge_edges (or_tr_d t2 t2_tr)):(intwet2q).
  move => [q_vt2 | [int2q | t2e]] //=.
    by rewrite q_p in int2q; rewrite (nci_tr_d t t2 _ _ p) // eqxx in t2_nt.
  move:t2e => [e [e_t2 int2e]].
  have t2_3vertex : (#|` vertex_set t2| = 3)%N.
    have test3 : (#|` [fset (vertex t2) x | x in 'I_3]| = #|` finset 'I_3|)%N.
      apply/card_in_imfset => x y _ _.
      by apply/injvt/fsetUP;right; apply/fsetD1P.
    by rewrite test3 card_finset card_ord.
  rewrite q_p in int2e.
  have [q' [intq' int2q']] : exists q', in_triangle t q' /\ in_triangle t2 q'.
    by apply:(in_triangle_on_edge intp _ e_t2) => //; apply/tne_tr_d.
  rewrite /no_cover_intersection in nci_tr_d.
  by case/eqP: t2_nt; apply: (nci_tr_d _ _ _ _ q').
have [h g] := (is_lof_imply_is_lor_on_line, vertices_to_triangle_correct).
case/andP: (intp) => /andP [/h /g vc12p /h /g vcp23] /h /g vc1p3 {h g}.
case/andP: intp => /andP [] islo1 islo2 islo3.
move:t1_spl qvt1=> /fset1UP [vt1 | /fset2P [vt1 |vt1]]; rewrite vt1;
move => /in_vertex_set [/eqP valq | [/eqP valq | /eqP valq]];
move:t2_spl => /fset1UP [vt2|/fset2P [vt2|vt2]]; rewrite vt2 => //=;
try (by rewrite valq vertex_set_vertices_to_triangle !inE eqxx ?orbT ?orTb).
          move:(intwet2q) => /andP [/andP [islor _] _]; move: islor.
          move:vcp23; rewrite /vertex1 /vertex2 -vt2 => [[<- [<- _]]].
          by rewrite valq is_left_or_on_change is_left_of_circular islo1.
        move:(intwet2q) => /andP [/andP [islor _] _]; move: islor.
        move:vc1p3; rewrite /vertex1 /vertex2 -vt2 => [ [<- [<- _]]].
        by rewrite valq is_left_or_on_change -is_left_of_circular islo1.
      move:(intwet2q) => /andP [/andP [islor _] _]; move: islor.
      move:vc1p3; rewrite /vertex1 /vertex2 -vt2 => [[<- [<- _]]].
      by rewrite valq is_left_or_on_change -is_left_of_circular islo1.
    move:(intwet2q) => /andP [/andP [_ islor] _]; move: islor.
    move:vc12p; rewrite /vertex2 /vertex3 -vt2 => [[_ [<- <-]]].
    by rewrite valq is_left_or_on_change is_left_of_circular islo2.
  move:(intwet2q) => /andP [/andP [islor _] _]; move:islor.
  move:vcp23; rewrite /vertex1 /vertex2 -vt2 => [[<- [<- _]]].
  by rewrite valq is_left_or_on_change is_left_of_circular islo1.
move:(intwet2q) => /andP [/andP [_ islor] _]; move: islor.
move: vc12p; rewrite /vertex2 /vertex3 -vt2 => [[_ [<- <-]]].
by rewrite valq is_left_or_on_change is_left_of_circular islo2.
Qed.

Lemma triangulation_cvh:
  forall tr, forall t , forall p, forall d, d != fset0 -> p \notin d ->
                        triangulation tr d -> t \in tr ->
                        in_triangle t p ->
                        covers_hull (split_triangle tr t p) (p |` d).
Proof.
move => tr t p d dne p_nin_d tr_d t_tr intp q hull_pdq.
move:(tr_d) => [covh_tr_d [_ [_ _]]].
have hull_d_q : hull d q.
  have h_d_p : hull d p by apply:(hull_from_triangle dne tr_d t_tr).
  by apply: (hull_add_point p_nin_d).
move/covh_tr_d: hull_d_q => [t0 [t0_tr intwe_to_q]].
case t_t0 : (t0 == t);
   first move/eqP:t_t0 t0_tr intwe_to_q => -> t0_tr intwe_to_q.
  have [t1 [sp intq]]:(exists t1 : T, t1 \in split_triangle_aux t p /\
                                  in_triangle_w_edges t1 q).
    by apply /three_triangles_cover_one.
  by exists t1; split => //; apply/fsetUP;left.
by exists t0; split=> //; apply/fsetUP/or_intror/fsetD1P; rewrite t_t0 t0_tr.
Qed.

Lemma triangulation_cvv tr t p d :
   d != fset0 -> p \notin d -> triangulation tr d -> t \in tr ->
     in_triangle t p -> covers_vertices (split_triangle tr t p) (p |` d).
Proof.
move => dne p_nin_d tr_d t_tr intp q.
move:(tr_d) => [covh_tr_d [covv_tr_d [nci_tr_d nps_tr_d]]].
split.
  move=> q_in_p.
  move: q_in_p => /fset1UP [q_p | q_in_d].
    pose t0 := (vertices_to_triangle (vertex1 t) (vertex2 t) p); exists t0.
    split;first by apply/fsetUP;left;apply/fset1UP;left.
    by rewrite /t0 vertex_set_vertices_to_triangle -q_p !inE eqxx ?orbT.
  move:q_in_d=>/covv_tr_d [t1 [t1_tr v_t1]].
  case t_t1 :(t==t1) v_t1;move:t_t1=> /eqP t_t1; first rewrite -t_t1 => v_t.
    pose t0 := (vertices_to_triangle (vertex1 t) (vertex2 t) p).
    pose t2 := vertices_to_triangle p (vertex2 t) (vertex3 t).
    have t0_spl : t0 \in split_triangle tr t p.
      by apply/fsetUP;left;apply/fset1UP;left.
    have t2_spl : t2  \in split_triangle tr t p.
      by apply/fsetUP;left;apply/fset1UP;right;apply/fset2P;left.
    move:v_t => /imfsetP [[[|[|[|x']]] px] _] x_v => //=.
        exists t0; split => //; rewrite /t0 vertex_set_vertices_to_triangle.
        by rewrite x_v mod3rules !inE eqxx.
      exists t0; split => //; rewrite /t0 vertex_set_vertices_to_triangle.
      by rewrite x_v mod3rules !inE eqxx ?orbT.
    exists t2; split=> //=; rewrite /t2 vertex_set_vertices_to_triangle.
    by rewrite x_v mod3rules !inE eqxx ?orbT.
  move => v_t1; rewrite /split_triangle /split_triangle_aux.
  exists t1;split=>//=;apply/fsetUP;right.
  by apply/fsetD1P;split=>//=; move:t_t1=>/eqP t_t1; rewrite eq_sym.
move=> [t0 [/fsetUP [H | H] v_t0]]; last first.
  have t0_tr : t0 \in tr by move:H => /fsetD1P [_ H].
  by apply/fset1UP; right; apply/covv_tr_d; exists t0.
case qp : (q == p); first by rewrite (eqP qp); apply/fset1UP; left.
have q_vt : q \in vertex_set t.
  move:H v_t0; rewrite !inE => /orP [/eqP -> | /orP [/eqP -> | /eqP ->]];
  rewrite vertex_set_vertices_to_triangle !inE qp ?orbF ?orFb
     => /orP [/eqP -> | /eqP ->]; apply/imfsetP;
    solve[exists ord30 => // | exists ord31 => // | exists ord32 => //].
by apply/fset1UP; right; apply/covv_tr_d; exists t.
Qed.

Hypothesis surface_non_empty : forall p1 p2 p3,
  oriented_surface p1 p2 p3 > 0 ->
  exists p', in_triangle (vertices_to_triangle p1 p2 p3) p'.

Lemma triangulation_tne:
  forall tr, forall t , forall p, forall d, d != fset0 -> p \notin d ->
                        triangulation tr d -> t \in tr ->
                        in_triangle t p ->
                        triangles_nempty (split_triangle tr t p).
Proof.
move => tr t p d dne p_nin_d tr_d t_tr intp t' t'_spl.
move:(tr_d) => [covh_tr_d [covv_tr_d [nci_tr_d [nps_tr_d tne_tr_d ]]]].
move:t'_spl => /fsetUP [t'_spl|t'_trt];last first.
  (* Here ssreflect apply fails, but standard apply succeeds. *)
  by move:t'_trt => /fsetD1P [t'_nt t'_tr];apply tne_tr_d.
move:(intp) => /andP [/andP [intp1 intp2] intp3].
by move:(t'_spl) => /fset1UP [Ht' | /fset2P [Ht' |Ht']];
rewrite Ht'; apply: surface_non_empty.
Qed.

Lemma triangulation_split_triangle:
  forall tr, forall t , forall p, forall d, d != fset0 -> p \notin d ->
                        triangulation tr d -> t \in tr ->
                        in_triangle t p ->
                        triangulation (split_triangle tr t p) (p |` d).
Proof.
move => tr t p d dne p_nin_d tr_d t_tr intp.
move:(tr_d) => [covh_tr_d [covv_tr_d [nci_tr_d nps_tr_d]]].
split;first by apply: triangulation_cvh.
split;first by apply: triangulation_cvv.
split;first by apply: triangulation_nci.
split;first by apply:triangulation_nps.
split;first by apply:(triangulation_tne dne).
by apply: (triangulation_or tr_d).
Qed.

Lemma oriented_strict_same_vertices t1 t2 :
  oriented_triangle_strict t1 -> oriented_triangle_strict t2 ->
  vertex_set t1 = vertex_set t2 ->
  exists i, vertex1 t2 = vertex t1 i /\ vertex2 t2 = vertex t1 (i + 1) /\
    vertex3 t2 = vertex t1 (i + 2%:R).
Proof.
move => otst1 otst2.
rewrite [X in vertex_set X = _ ](all_triangles_oriented otst1)
   [X in _ = vertex_set X](all_triangles_oriented otst2) => /fsetP vq.
have abs1 : forall j p, ~is_left_of (vertex t1 j) (vertex t1 j) p.
  by move=> j p; rewrite /is_left_of oriented_surface_x_x ltrr.
have abs2 : forall i, ~is_left_of (vertex t1 ord30) (vertex t1 ord32)
                            (vertex t1 i).
  move => [[ | [ | [ | i]]] pi] //.
      by rewrite is_left_of_circular ord30_inj; apply: abs1.
    move/is_lof_imply_is_lor_on_line.
    rewrite ord31_inj is_left_or_on_change -is_left_of_circular =>/negP.
    by move/(_ otst1).
  by rewrite ord32_inj -is_left_of_circular; apply: abs1.
have abs2' : forall i p j, is_left_of p (vertex t1 i) (vertex t1 j) ->
                  ~ p = vertex t1 (i + 1).
  move=> i p j lof pq; move: lof; rewrite pq {pq p}; move: i j.
  case => [[ | [ | [ | i]]] pi] //; rewrite !mod3rules //;
    case => [[ | [ | [ | j]]] pj] //; rewrite !mod3rules;
     (try by rewrite is_left_of_circular; (case/abs1 || case /abs2));
     by rewrite -is_left_of_circular; (case/abs1 || case/abs2).
have c2 : forall j, vertex t2 ord30 = vertex t1 j ->
         vertex t2 ord31 = vertex t1 (j + 1).
  move => j v2q; have:= vq (vertex t2 ord31).
  rewrite !vertex_set_vertices_to_triangle !inE eqxx ?(orbT, orTb).
  by case/orP=> [/orP [/eqP ha |/eqP ha] | /eqP ha ];
  case: j v2q => [ [ | [ | [ | j]]] pj] //; rewrite ?mod3rules => v2q;
  move: otst2;
    rewrite -[oriented_triangle_strict _]/
            (is_left_of (vertex t2 ord30) (vertex t2 ord31) (vertex t2 ord32));
  rewrite ha v2q;
    (try case/abs1) => //;
      try by move: (vq (vertex t2 ord32));
          rewrite !vertex_set_vertices_to_triangle !inE eqxx ?(orbT, orTb) =>
        /orP [/orP [/eqP -> | /eqP ->] | /eqP ->]; case/abs2';
        rewrite mod3rules.
have c3 : forall j, vertex t2 ord30 = vertex t1 j ->
             vertex t2 ord32 = vertex t1 (j + 2%:R).
  move => j v2q; have := vq (vertex t2 ord32).
  rewrite !vertex_set_vertices_to_triangle !inE eqxx ?(orbT, orTb).
  by case/orP => [/orP [/eqP ha | /eqP ha] | /eqP ha];
  case: j v2q => [ [ | [ | [ | j]]] pj] //; rewrite ?mod3rules => v1q;
  move: (c2 _ v1q); rewrite /vertex2 ?mod3rules => v2q //;
  move: otst2;
    rewrite -[oriented_triangle_strict _]/
                (is_left_of (vertex1 t2) (vertex2 t2) (vertex3 t2));
  rewrite /vertex1 /vertex2 /vertex3 ha v1q v2q;
  try (rewrite is_left_of_circular; case/abs1);
  (rewrite -is_left_of_circular; case/abs1).
have [j v1q] : exists j, vertex t2 ord30 = vertex t1 j.
  have:= (vq (vertex t2 ord30)); rewrite /vertex1 /vertex2 /vertex3
    !vertex_set_vertices_to_triangle !inE eqxx !orTb.
  by case/orP => [/orP [ha | ha] | ha]; eapply ex_intro; eapply (eqP ha).
exists j; rewrite /vertex1 /vertex2 /vertex3 v1q (c2 _ v1q) (c3 _ v1q) {v1q}.
by case: j => [[ | [ | [ | j]]] pj] //; rewrite ?mod3rules.
Qed.

Lemma vertex_set_eq_in_triangle:
  forall t1 t2, oriented_triangle_strict t1 -> oriented_triangle_strict t2 ->
   vertex_set t1 = vertex_set t2 -> {subset in_triangle t1 <= in_triangle t2}.
Proof.
move => t1 t2 otst1 otst2; rewrite /in_triangle.
case/oriented_strict_same_vertices=> // [i [-> [-> ->]]] p; rewrite !unfold_in.
by case: i => [[ | [ | [ | i]]] pi] //; rewrite !mod3rules //
    in_triangle_circular // in_triangle_circular.
Qed.

Lemma vertex_set_eq_in_triangle_w_edges t1 t2:
  oriented_triangle_strict t1 -> oriented_triangle_strict t2 ->
              vertex_set t1 = vertex_set t2 ->
        {subset in_triangle_w_edges t1 <= in_triangle_w_edges t2}.
Proof.
move => otst1 otst2; rewrite /in_triangle_w_edges.
case/oriented_strict_same_vertices=> // [i [-> [-> ->]]] p; rewrite unfold_in.
by case: i => [[ | [ | [ | i]]] pi] //; rewrite !mod3rules //
  in_triangle_w_edges_circular // in_triangle_w_edges_circular.
Qed.

Lemma is_left_of_oriented_strict a b c :
  is_left_of a b c -> oriented_triangle_strict (vertices_to_triangle a b c).
Proof.
move => islo_abc.
case:(vertices_to_triangle_correct'
               (is_lof_imply_is_lor_on_line islo_abc)) => [j pj].
rewrite /oriented_triangle_strict /vertex1 /vertex2 /vertex3.
by case: j pj => [[| [| [| j]]] j3] //; rewrite !mod3rules => [[<- [<- <-]]];
  rewrite // oriented_surface_circular // oriented_surface_circular.
Qed.

Lemma in_vert_to_triangle_in_triangle a b c :
  is_left_of a b c -> forall t, a \in vertex_set t ->
  oriented_triangle_strict t -> b \in vertex_set t -> c \in vertex_set t ->
  {subset in_triangle (vertices_to_triangle a b c) <= in_triangle t}.
Proof.
move=> islo_abc t a_t or_t b_t c_t.
apply: vertex_set_eq_in_triangle => //=.
  by apply: is_left_of_oriented_strict.
rewrite vertex_set_vertices_to_triangle.
move: islo_abc.
have [->|b_na] := eqVneq a b.
  by rewrite /is_left_of oriented_surface_x_x ltrr.
have [->|b_nc] := eqVneq b c.
  by rewrite -is_left_of_circular /is_left_of oriented_surface_x_x ltrr.
have [->|c_na] := eqVneq a c.
  by rewrite is_left_of_circular /is_left_of oriented_surface_x_x ltrr.
move=> islo_abc; apply/eqP; rewrite eqEfcard; apply/andP; split.
  by apply/fsubsetP=> x /fsetUP [/fset2P [] ->|/fset1P ->].
suff card_fset3 : (#|` [fset a; b; c] | = 3)%N.
  rewrite card_fset3 (leq_trans (leq_imfset_card _ _)) //.
  by rewrite card_finset card_ord.
rewrite !cardfsU !cardfs1 fsetI1 !inE [b == a]eq_sym (negPf b_na) cardfs0.
by rewrite fsetI1 !inE ![c == _]eq_sym (negPf b_nc) (negPf c_na) /= cardfs0.
Qed.

(* If this lemma was earlier, it would probably help a few proofs. *)
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
      forall q, in_triangle_w_edges (vertices_to_triangle a b c) q ->
    in_triangle_w_edges t q.
Proof.
move => islo_abc t or_t a_t b_t c_t q intwq.
have invt := in_vert_to_triangle_in_triangle islo_abc a_t or_t b_t c_t.
move: intwq => /(in_triangle_w_edge_edges
          (vertices_to_triangle_oriented_strict islo_abc)) intwq.
apply /(in_triangle_w_edge_edges or_t).
move:intwq => [q_vt| [intq|q_et]];[left|right;left|right;right];
[rewrite vertex_set_vertices_to_triangle in q_vt|by apply: invt|move];
first by move:q_vt => /fsetUP [/fset2P [] |/fset1P] ->.
move:q_et => [e [e_abc e_q]];exists e;split => //=.
by move:e_abc; rewrite (edges_set_vertices_to_triangle islo_abc)
=> /fsetUP [/fset2P []| /fset1P] ->;
apply: vertex_set_edge_triangle => //=;
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
  (apply:in_vert_to_triangle_in_triangle_w_edges; first apply: islo_abc;
    rewrite is_left_of_circular in islo_abc;
  first apply: (vertices_to_triangle_oriented_strict islo_abc)) => //=;
  by rewrite vertex_set_vertices_to_triangle !inE eqxx ?orbT ?orTb.
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
move:(tr_d) => [_ [_ [_ [_ [_ or_tr_d]]]]].
  move:(a_t1) => /imfsetP [[[|[|[|x1']]] px1] _] a_vt1 => //=;
  move:(b_t1) => /imfsetP [[[|[|[|x2']]] px2] _] b_vt1 => //=;
  move:(c_t1) => /imfsetP [[[|[|[|x3']]] px3] _] c_vt1 => //=;
  (try have x1_x2:Ordinal px1 = Ordinal px2 by apply: ord_inj);
  (try (rewrite x1_x2 in a_vt1;
  rewrite a_vt1 b_vt1 in b_na;
  move:b_na => /eqP //=));
  (try have x1_x3:Ordinal px1 = Ordinal px3 by apply: ord_inj);
  (try (rewrite x1_x3 in a_vt1;
  rewrite a_vt1 c_vt1 in a_nc;
  move:a_nc => /eqP //=));
  (try have x2_x3:Ordinal px2 = Ordinal px3 by apply: ord_inj);
  (try (rewrite x2_x3 in b_vt1;
  rewrite b_vt1 c_vt1 in b_nc;
  move:b_nc => /eqP //=));
  (try have ord1 : Ordinal px1 = ord30 by apply: ord_inj);
  (try have ord1 : Ordinal px1 = ord31 by apply: ord_inj);
  (try have ord1 : Ordinal px1 = ord32 by apply: ord_inj);
  (try have ord2 : Ordinal px2 = ord30 by apply: ord_inj);
  (try have ord2 : Ordinal px2 = ord31 by apply: ord_inj);
  (try have ord2 : Ordinal px2 = ord32 by apply: ord_inj);
  (try have ord3 : Ordinal px3 = ord30 by apply: ord_inj);
  (try have ord3 : Ordinal px3 = ord31 by apply: ord_inj);
  (try have ord3 : Ordinal px3 = ord32 by apply: ord_inj);
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
    split; first by apply/fset1UP;left.
    have oriented_abd:(is_left_or_on_line a b d).
      by apply: is_lof_imply_is_lor_on_line.
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
    move: islof_abd => /is_lof_imply_is_lor_on_line islof_abd.
    move: oriented_abc => /is_lof_imply_is_lor_on_line oriented_abc.
    rewrite is_left_or_on_line_circular in oriented_abc.
    apply:(is_left_or_line_trans2 islof_abd oriented_abc).
        by rewrite is_left_or_on_line_circular in islo_abq.
          by move:islo_and => /andP [_ temp];
           rewrite is_left_or_on_line_circular in temp.
    by move: islo_acd => /is_lof_imply_is_lor_on_line islo_acd;
    rewrite is_left_or_on_line_circular in islo_acd.
  exists (vertices_to_triangle b c d).
  split;first by apply/fset2P ;right.
  have oriented_bcd : is_left_or_on_line b c d.
    by apply: is_lof_imply_is_lor_on_line.
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
  move: islo_bca => /is_lof_imply_is_lor_on_line islo_bca.
  rewrite -is_left_or_on_line_circular in islo_bca.
  apply:(is_left_or_line_trans islo_bcd islo_bca islo_bcq).
    by move:islo_and=>/andP [_ temp];
      rewrite -is_left_or_on_line_circular in temp.
  by apply: is_lof_imply_is_lor_on_line islo_acd.
Qed.

Lemma vertices_vt : forall a b, b != a -> forall c, b != c -> a != c ->
                        forall t, injective (vertex t) ->
                             a \in vertex_set t ->
                             b \in vertex_set t ->
                             c \in vertex_set t ->
                               [fset a; b;c] =i vertex_set t.
Proof.
move => a b a_nb c b_nc a_nc t injvt a_t b_t c_t.
have card_abc: (#|` [fset a; b; c] | = 3)%N.
  rewrite cardfsU.
  have cnab :(c \notin [fset a; b]).
    by rewrite !inE; rewrite !(eq_sym c) negb_or a_nc b_nc.
  by rewrite fsetI1 (negbTE cnab) cardfs0 subn0 cardfs1 cardfs2 eq_sym a_nb.
have card_vt : (#|` vertex_set t | = #|` finset 'I_3 |)%N.
  by apply:card_imfset=> //=.
move: card_vt; rewrite card_finset card_ord => card_vt.
have abc_incl_vt :  [fset a; b; c] `<=` vertex_set t.
  apply/fsubsetP=> i.
  by rewrite !inE => /orP [/orP [/eqP -> | /eqP ->] | /eqP ->].
by apply/fsubset_cardP; first rewrite card_vt.
Qed.

Lemma in_flip_edge_aux tr data:
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
move:(tr_d) => [cvh_tr_d [cvv_tr_d [nci_tr_d nps_tr_d]]].
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
  move: islo_pbd => /is_lof_imply_is_lor_on_line islo_pbd.
    by rewrite islo_pbd in islo_bpd.
move:t_fl => /fset2P [Ht|Ht];
rewrite Ht /in_triangle /vertex1 /vertex2 /vertex3 in intq;
[rewrite -a_abd -b_abd -d_abd in intq|
 rewrite -b_bcd -c_bcd -d_bcd in intq];
move:intq => /andP[/andP [intq1 intq2] intq3];
case islo_acq:(is_left_of a q c);
(try (move:islo_acq => /negP /negP; rewrite -is_left_or_on_change;move => islo_acq;
 rewrite -is_left_or_on_line_circular in islo_acq));
(try move: islo_acq => /is_left_or_on_split islo_acq);
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
      apply: oriented_acd.
      rewrite -is_left_of_circular in islo_abd.
      apply: islo_abd.
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

Lemma in_flip_edge_aux_oriented :
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
move => /fset2P[]->;apply: vertices_to_triangle_oriented_strict;easygeo.
Qed.

Lemma in_flip_edge_aux_we :
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
have or_abc := vertices_to_triangle_oriented_strict oriented_abc.
have or_acd := vertices_to_triangle_oriented_strict oriented_acd.
case /in_triangle_w_edge_edges: intq => [| q_t | [intq | q_e ]].
  now apply:(in_flip_edge_aux_oriented tr_d t1_nt2 t1_tr t2_tr a_nc a_t1 a_t2 c_t1 c_t2
        b_t1 b_na b_nc oriented_abc d_t2 d_na d_nc oriented_acd)=> //=.
    by move:t_fl=> /fset2P [Ht|Ht];rewrite Ht in q_t;
    move/in_vertex_set:q_t => [/eqP ->|[/eqP ->|/eqP ->]];
    [left|left|right|left|left|right];
    apply /in_triangle_w_edge_edges => //=; left;
    apply /in_vertex_set;
    [left|right;left|right;right|right;left|right;right|right;right].
  have Hq := in_flip_edge_aux tr_d t1_nt2 t1_tr t2_tr a_nc a_t1 a_t2 c_t1 c_t2
               b_t1 b_na b_nc oriented_abc d_t2 d_na d_nc oriented_acd islo_bcd
               islo_abd t_fl intq.
  move:Hq => [/in_triangle_imply_w_edges q_abc |
             [/in_triangle_imply_w_edges q_acd| q_ac]];
  [by left|by right|left].
  apply /(in_triangle_w_edge_edges or_abc) ;right;right.
  exists (vertices_to_edge a c).
  split => //=.
  by apply: vertex_set_edge_triangle => //=;
    rewrite vertex_set_vertices_to_triangle !inE eqxx ?orbT ?orTb.
move:q_e => [e [e_t q_e]].
move:t_fl => /fset2P [Ht|Ht];
rewrite Ht in e_t;rewrite edges_set_vertices_to_triangle in e_t => //=;
move:e_t => /fsetUP[/fset2P [He|He] | /fset1P He];
[left|right|move|left|move|right];
try (apply (in_triangle_w_edge_edges or_abc);right;right);
try (apply (in_triangle_w_edge_edges or_acd);right;right);
try (exists e;split => //=;rewrite edges_set_vertices_to_triangle) => //=;
try (apply/fsetUP); try (by right;apply/fset1P);
try (left;apply/fset2P);[by left|by right|move|move]; move:Ht => _.
move:(q_e) => Hq;rewrite He in Hq.
move: Hq => /(on_edge_on_line islo_bcd) [_ [islo_bcq islo_cdq]].
move:(q_e) => Hq;rewrite He in Hq.
rewrite is_left_of_circular in islo_abd.
rewrite vertices_to_edge_sym in Hq.
move: Hq => /(on_edge_on_line islo_abd) [_ [islo_daq islo_abq]].
rewrite is_left_of_circular in islo_cdq.
rewrite -is_left_of_circular in islo_daq.
case islo_acq : (is_left_of a c q);
last (move:islo_acq => /negP /negP; rewrite -is_left_or_on_change;
                                   move => islor_caq);
[right;apply: in_triangle_imply_w_edges|left].
  rewrite/in_triangle.
  rewrite /vertex1 /vertex2 /vertex3 -a_acd -c_acd -d_acd.
  by apply/andP;split => //=;apply/andP;split.
move: islo_abq => /is_lof_imply_is_lor_on_line islo_abq.
rewrite is_left_of_circular in islo_bcq.
move: islo_bcq => /is_lof_imply_is_lor_on_line islo_bcq.
rewrite -is_left_or_on_line_circular in islor_caq.
rewrite /in_triangle_w_edges /vertex1 /vertex2 /vertex3 -a_abc -b_abc -c_abc.
by apply/andP;split => //=;apply/andP;split.
move:(q_e) => Hq;rewrite He in Hq.
move: Hq => /(on_edge_on_line islo_bcd) [_ [islo_bcq islo_cdq]].
move:(q_e) => Hq;rewrite He in Hq.
rewrite is_left_of_circular in islo_abd.
rewrite vertices_to_edge_sym in Hq.
move: Hq => /(on_edge_on_line islo_abd) [_ [islo_daq islo_abq]].
rewrite is_left_of_circular in islo_cdq.
rewrite -is_left_of_circular in islo_daq.
case islo_acq : (is_left_of a c q);
last (move:islo_acq => /negP /negP; rewrite -is_left_or_on_change;
                                   move => islor_caq);
[right;apply: in_triangle_imply_w_edges|left].
  rewrite/in_triangle.
  rewrite /vertex1 /vertex2 /vertex3 -a_acd -c_acd -d_acd.
  by apply/andP;split => //=;apply/andP;split.
move: islo_abq => /is_lof_imply_is_lor_on_line islo_abq.
rewrite is_left_of_circular in islo_bcq.
move:islo_bcq => /is_lof_imply_is_lor_on_line islo_bcq.
rewrite -is_left_or_on_line_circular in islor_caq.
rewrite /in_triangle_w_edges /vertex1 /vertex2 /vertex3 -a_abc -b_abc -c_abc.
by apply/andP;split => //=;apply/andP;split.
Qed.

Lemma flip_edge_cvh tr data:  triangulation tr data ->
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
move:(tr_d) => [cvh_tr_d [cvv_tr_d [nci_tr_d nps_tr_d]]].
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
    by exists t3;split => //=;apply/fsetUP;left.
  rewrite t_t2 in intwetp.
  rewrite eq_sym in t1_nt2;rewrite eq_sym in a_nc.
  rewrite -is_left_of_circular in oriented_acd.
  rewrite is_left_of_circular in oriented_abc.
  rewrite is_left_of_circular in  islo_abd.
  rewrite -is_left_of_circular in  islo_bcd.
  have flip_aux:= (flip_edge_covers_aux tr_d t1_nt2 t2_tr t1_tr a_nc c_t2
                   c_t1 a_t2 a_t1 d_t2 d_nc d_na oriented_acd b_t1 b_nc b_na
                   oriented_abc islo_abd islo_bcd intwetp).
  move:(flip_aux) => [t3 [/fset2P[H | H] intwet3p]].
    rewrite H in intwet3p.
    move: intwet3p => /(vertices_to_triangle_circular_w_edges islo_bcd) intwet3p.
    exists (vertices_to_triangle b c d) ;split => //=;apply/fsetUP;left;
      by apply/fset2P;right.
  rewrite H in intwet3p.
  move: intwet3p=> /(vertices_to_triangle_circular_w_edges islo_abd) intwet3p.
  move: intwet3p => /vertices_to_triangle_circular_w_edges intwet3p.
  have bda : is_left_of b d a.
    by rewrite is_left_of_circular in islo_abd.
  exists (vertices_to_triangle a b d);split; auto; 
    apply/fsetUP;left;by apply/fset2P;left.
exists t.
split => //=.
apply/fsetUP;right;apply/fsetD1P;split;first by apply/eqP.
by apply/fsetD1P; split;first apply/eqP.
Qed.

Lemma flip_edge_cvv tr data: triangulation tr data ->
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
move:(tr_d) => [_ [cvv_tr_d [_ [_ [_ or_tr_d]]]]].
have vc_abd := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line islo_abd).
have vc_bcd := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line islo_bcd).
move : (vc_abd) => [a_abd [b_abd d_abd]].
move : (vc_bcd) => [b_bcd [c_bcd d_bcd]].
move => p.
  split.
    pose u1 := vertices_to_triangle a b d;
    pose u2 := vertices_to_triangle b c d.
    move => p_d; move/cvv_tr_d:(p_d)=> [t [t_tr p_vt]].
    case t_t1 : (t==t1);case t_t2 : (t==t2);
      move:t_t1 => /eqP t_t1;move:t_t2 => /eqP t_t2.
        by move: t1_nt2; rewrite -t_t1 t_t2 eqxx.
      have injvt1 : injective (vertex t1).
        by apply/(oriented_triangle_triangulation_3vertices or_tr_d).
      have abc_vt1 := (vertices_vt b_na b_nc a_nc injvt1 a_t1 b_t1 c_t1).
      by move: p_vt; rewrite t_t1 -abc_vt1 !inE =>
           /orP [/orP [/eqP -> | /eqP ->] | /eqP ->];
      [exists u1 | exists u1 | exists u2];
      rewrite ?vertex_set_vertices_to_triangle !inE ?eqxx ?orbT ?orTb.
    have injvt2 : injective (vertex t2).
      by apply/(oriented_triangle_triangulation_3vertices or_tr_d).
    move: a_nc d_nc d_na; rewrite !(eq_sym d) (eq_sym a c) => a_nc d_nc d_na.
    have abc_vt2 := (vertices_vt a_nc d_nc d_na injvt2 a_t2 c_t2 d_t2).
    by move: p_vt; rewrite t_t2 -abc_vt2 !inE =>
        /orP [/orP [/eqP -> | /eqP ->] | /eqP ->];
      [exists u1 | exists u2 | exists u1];
      rewrite ?vertex_set_vertices_to_triangle !inE ?eqxx ?orbT ?orTb.
  exists t; split => //=.
  apply/fsetUP;right;apply/fsetD1P;split;first by apply/eqP.
  by apply/fsetD1P; split;first apply/eqP.
move => [t [t_spl p_vset_t]].
move:t_spl=>/fsetUP [Ht |  /fsetD1P [t_nt2 /fsetD1P [t_nt1 t_tr]]]; apply/ cvv_tr_d;
  last by exists t;split => //=.
by move : Ht p_vset_t => /fset2P [-> | ->];
  move/imfsetP => [[[|[|[|x']]] px] _]; rewrite ?mod3rules => -> //;
  [exists t1 | exists t1 | exists t2 |exists t1|exists t1|exists t2];split => //;
  [rewrite -a_abd|rewrite -b_abd|rewrite -d_abd|
   rewrite -b_bcd|rewrite -c_bcd|rewrite -d_bcd].
Qed.

Lemma flip_edge_nci tr data: triangulation tr data ->
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
move => b b_t1 b_na b_nc oriented_abc d d_t2 d_na d_nc oriented_acd
  islo_bcd islo_abd t3 t4 t3_spl t4_spl p int3p int4p.
move:(tr_d) => [_ [_ [nci_tr_d [_ [tne_tr_d or_tr_d]]]]].
have [a_abd [b_abd d_abd]] := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line islo_abd).
have [b_bcd [c_bcd d_bcd]] := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line islo_bcd).
have not_in_both_triangles:in_triangle (vertices_to_triangle a b d) p ->
       ~ in_triangle (vertices_to_triangle b c d) p.
  rewrite /in_triangle /vertex1 /vertex2 /vertex3
  -a_abd -b_abd -d_abd -b_bcd -c_bcd -d_bcd.
  move => /andP [/andP[islo_abp islo_pbd] islo_apd].
  move => /andP [/andP[islo_bcp islo_pcd] ].
  rewrite  is_left_of_change => /negP; apply.
  by apply/is_lof_imply_is_lor_on_line: islo_pbd.
have [a_abc [b_abc c_abc]] := vertices_to_triangle_correct
                       (is_lof_imply_is_lor_on_line oriented_abc).
have [a_acd [c_acd d_acd]] := vertices_to_triangle_correct
                       (is_lof_imply_is_lor_on_line oriented_acd).
have infl := in_flip_edge_aux tr_d t1_nt2 t1_tr t2_tr a_nc a_t1 a_t2 c_t1 c_t2
b_t1 b_na b_nc oriented_abc d_t2 d_na d_nc oriented_acd islo_bcd islo_abd.
move:t3_spl => /fsetUP [Ht3 | /fsetD1P [t3_nt2 /fsetD1P [t3_nt1 t3_tr]]];
move:t4_spl => /fsetUP [Ht4 | /fsetD1P [t4_nt2 /fsetD1P [t4_nt1 t4_tr]]].
move:Ht3 => /fset2P [Ht3|Ht3];move:Ht4=>/fset2P [Ht4|Ht4];
    (try by rewrite Ht3 Ht4); rewrite Ht3 in int3p;rewrite Ht4 in int4p;
     try by case: not_in_both_triangles.
    move:(infl t3 Ht3 p int3p) => [Htp|[Htp|Htp]];
    try have intxp := (in_vert_to_triangle_in_triangle oriented_abc
                      a_t1 (or_tr_d t1 t1_tr) b_t1 c_t1 Htp);
    try have intxp := (in_vert_to_triangle_in_triangle oriented_acd
                      a_t2 (or_tr_d t2 t2_tr) c_t2 d_t2 Htp);
    try have abst1 := nci_tr_d t1 t4 t1_tr t4_tr p intxp int4p;
    try have abst2 := nci_tr_d t2 t4 t2_tr t4_tr p intxp int4p;
    [move:t4_nt1|move:t4_nt2|]; rewrite -?abst1 -?abst2 ?eqxx //.
    have ac_edge_1 := vertex_set_edge_triangle a_t1 c_t1 a_nc.
    move: (in_triangle_on_edge int4p (tne_tr_d t1 t1_tr) ac_edge_1 Htp) t4_nt1.
    move => [q [int4q int1q]].
    by rewrite (nci_tr_d t1 t4 t1_tr t4_tr q int1q int4q) eqxx.
  move: (infl t4 Ht4 p int4p) => [Htp|[Htp|Htp]];
  try have intxp := (in_vert_to_triangle_in_triangle oriented_abc
                      a_t1 (or_tr_d t1 t1_tr) b_t1 c_t1 Htp);
  try have intxp := (in_vert_to_triangle_in_triangle oriented_acd
                      a_t2 (or_tr_d t2 t2_tr) c_t2 d_t2 Htp);
  try have abst1 := nci_tr_d t1 t3 t1_tr t3_tr p intxp int3p;
  try have abst2 := nci_tr_d t2 t3 t2_tr t3_tr p intxp int3p;
  [move:t3_nt1|move:t3_nt2|]; rewrite -?abst1 -?abst2 ?eqxx //.
  have ac_edge_1 := vertex_set_edge_triangle a_t1 c_t1 a_nc.
  move: (in_triangle_on_edge int3p (tne_tr_d t1 t1_tr) ac_edge_1 Htp) t3_nt1.
  move => [q [int3q int1q]].
  have abs := nci_tr_d t1 t3 t1_tr t3_tr q int1q int3q.
  by rewrite (nci_tr_d t1 t3 t1_tr t3_tr q int1q int3q) eqxx.
by apply:(nci_tr_d t3 t4 _ _ p).
Qed.

Lemma flip_edge_nps tr data : triangulation tr data ->
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
move => tr_d t1 t2 t1_nt2 t1_tr t2_tr a c a_nc a_t1 a_t2 c_t1 c_t2 b b_t1 b_na
   b_nc oriented_abc d d_t2 d_na d_nc oriented_acd islo_bcd islo_abd
   t3 t4 t3_fl t4_fl p p_t3 int4p.
move:(tr_d) => [_ [_ [_ [nps_tr_d [_ or_tr_d]]]]].
have [a_abd [b_abd d_abd]] := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line islo_abd).
have [b_bcd [c_bcd d_bcd]] := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line islo_bcd).
move:t3_fl => /fsetUP [Ht3 | /fsetD1P [t3_nt2 /fsetD1P [t3_nt1 t3_tr]]];
move:t4_fl => /fsetUP [Ht4 | /fsetD1P [t4_nt2 /fsetD1P [t4_nt1 t4_tr]]];
last first.
      by apply:(nps_tr_d t3 t4 t3_tr t4_tr p).
    have intp' := in_flip_edge_aux_we tr_d t1_nt2 t1_tr t2_tr
      a_nc a_t1 a_t2 c_t1 c_t2 b_t1 b_na b_nc oriented_abc
      d_t2 d_na d_nc oriented_acd islo_bcd islo_abd Ht4 int4p.
    have v_abc_t1 :  vertex_set (vertices_to_triangle a b c)= vertex_set t1.
      rewrite vertex_set_vertices_to_triangle.
      have card_fset3 : (#|` [fset a; b; c] | = 3)%N.
        have card_fset2 : (#|` [fset a; b] | = 2)%N.
          by rewrite cardfs2 eq_sym b_na.
        have abIc0: [fset a; b] `&` [fset c] = fset0.
            apply: disjoint_fsetI0.
            by rewrite fdisjointX1 !inE negb_or !(eq_sym c) a_nc b_nc.
        have card_abIc0: (#|` [fset a; b] `&` [fset c]| = 0)%N.
          by rewrite abIc0; apply: cardfs0.
        by rewrite cardfsU card_fset2 cardfs1 card_abIc0.
      have cardvt1 : (#|` vertex_set t1 | = #|` finset 'I_3|)%N.
        apply/card_in_imfset => x y px py.
        by apply/(oriented_triangle_triangulation_3vertices or_tr_d).
      have card_eq : (#|` [fset a; b; c] | = #|` vertex_set t1 |)%N.
        by rewrite card_fset3 cardvt1 card_finset card_ord.
      apply/fsetP/(fsubset_cardP card_eq)/fsubsetP => x.
      by move=>/fsetUP [/fset2P [->|->]|/fset1P ->].
    have v_acd_t2 :  vertex_set (vertices_to_triangle a c d)= vertex_set t2.
      rewrite vertex_set_vertices_to_triangle.
      have card_fset3 : (#|` [fset a; c; d] | = 3)%N.
        have card_fset2 : (#|` [fset a; c] | = 2)%N.
          by rewrite cardfs2 a_nc.
        have acId0: [fset a; c] `&` [fset d] = fset0.
            apply: disjoint_fsetI0.
            by rewrite fdisjointX1 !inE negb_or d_na d_nc.
          have card_acId0:(#|` [fset a; c] `&` [fset d]| = 0)%N.
            by rewrite acId0 cardfs0.
        by rewrite cardfsU card_fset2 cardfs1 card_acId0.
      have cardvt2 : (#|` vertex_set t2| = #|` finset 'I_3|)%N.
        apply/card_in_imfset => x y px py.
        by apply/(oriented_triangle_triangulation_3vertices or_tr_d).
      have card_eq : (#|` [fset a; c; d] | = #|` vertex_set t2 |)%N.
        by rewrite card_fset3 cardvt2 card_finset card_ord.
      apply/fsetP/(fsubset_cardP card_eq)/fsubsetP => x.
      by move=>/fsetUP [/fset2P [->|->]|/fset1P ->].
    have otstabc : oriented_triangle_strict (vertices_to_triangle a b c).
      by apply: is_left_of_oriented_strict.
    have otstacd : oriented_triangle_strict (vertices_to_triangle a c d).
      by apply: is_left_of_oriented_strict.
    have intp : in_triangle_w_edges t1 p \/ in_triangle_w_edges t2 p.
      case: intp'=>[ Hintp | Hintp];[left | right].
        by apply: (vertex_set_eq_in_triangle_w_edges _ (or_tr_d t1 t1_tr) _ Hintp).
      by apply: (vertex_set_eq_in_triangle_w_edges _ (or_tr_d t2 t2_tr) _ Hintp).
    have : (p \in vertex_set t1 \/ p \in vertex_set t2).
     by  case: intp => [intp | intp];
      [left; have p_t := nps_tr_d t3 t1 t3_tr t1_tr p p_t3 intp => {intp}|
       right; have p_t := nps_tr_d t3 t2 t3_tr t2_tr p p_t3 intp => {intp}].
    by case => [p_t | p_t];
    [rewrite -v_abc_t1 in p_t|rewrite -v_acd_t2 in p_t];
    move: p_t => /in_vertex_set [/eqP Hp|[/eqP Hp|/eqP Hp]];
    rewrite Hp;
    move:Ht4 => /fset2P [Ht4|Ht4];rewrite Ht4;apply/ in_vertex_set;
    [left| |right;left|left| |right;left|left| | |right;left|right;right|right;right]
    => //=; rewrite Hp in int4p;rewrite Ht4 in int4p;
    rewrite /in_triangle_w_edges /vertex1 /vertex2 /vertex3 in int4p;
    [rewrite -b_bcd -c_bcd -d_bcd in int4p|
     rewrite -a_abd -b_abd -d_abd in int4p|
     rewrite -b_bcd -c_bcd -d_bcd in int4p|
     rewrite -a_abd -b_abd -d_abd in int4p];
    move:int4p => /andP;
    [move => [_ abs]|move => [/andP[_ abs] _]|
     move => [_ abs]|move => [/andP[_ abs] _] ];
    rewrite is_left_or_on_change in abs;
    try rewrite islo_abd in abs;
    try rewrite islo_bcd in abs.
  have p_t1_t2 : p\in vertex_set t1 \/ p\in vertex_set t2.
    by move:Ht3 => /fset2P [Ht3|Ht3];
    rewrite Ht3 in p_t3;move: p_t3 => /in_vertex_set 
              [/eqP ->|[/eqP ->|/eqP ->]];
    [left|left|right|left|left|right].
  move:p_t1_t2 => [Hp|Hp].
    by apply:(nps_tr_d t1 t4 t1_tr t4_tr).
  by apply:(nps_tr_d t2 t4 t2_tr t4_tr).
move:Ht3=>/fset2P[Ht3|Ht3];move:Ht4=>/fset2P[Ht4|Ht4];
[have t4_t3 :t4=t3 by rewrite Ht3 Ht4|move|move|
 have t4_t3:t4=t3 by rewrite Ht3 Ht4];
try by rewrite t4_t3.
  rewrite Ht3 in p_t3.
  move:p_t3 => /in_vertex_set [/eqP Hp | [/eqP Hp | /eqP Hp]];
  rewrite Ht4 Hp;  apply /in_vertex_set;[move|left|right;right] => //=.
  rewrite Hp Ht4 in int4p.
  rewrite /in_triangle_w_edges /vertex1 /vertex2 /vertex3 in int4p.
  rewrite -b_bcd -c_bcd -d_bcd in int4p.
  move:int4p => /andP[_ abs].
  rewrite is_left_or_on_change in abs.
  by rewrite islo_abd in abs.
rewrite Ht3 in p_t3.
move:p_t3 => /in_vertex_set [/eqP Hp | [/eqP Hp | /eqP Hp]];
rewrite Ht4 Hp;  apply/in_vertex_set;[right;left|move|right;right] => //=.
rewrite Hp Ht4 in int4p.
rewrite /in_triangle_w_edges /vertex1 /vertex2 /vertex3 in int4p.
rewrite -a_abd -b_abd -d_abd in int4p.
move:int4p => /andP[/andP[_ abs] _].
rewrite is_left_or_on_change in abs.
by rewrite islo_bcd in abs.
Qed.

Lemma flip_edge_tne tr data : triangulation tr data ->
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
move => tr_d t1 t2 t1_nt2 t1_tr t2_tr a c a_nc a_t1 a_t2 c_t1 c_t2 b b_t1 b_na
    b_nc oriented_abc d d_t2 d_na d_nc oriented_acd islo_bcd islo_abd.
move:(tr_d) => [_ [_ [_ [_ [tne_tr_d _]]]]].
move => t t_fl.
move:t_fl => /fsetUP [Ht|/fsetD1P[t_nt2 /fsetD1P [_ t_tr]]];last first.
  by have := tne_tr_d t t_tr.
by move:Ht => /fset2P [->|->]; apply: surface_non_empty.
Qed.

Lemma flip_edge_or tr data : triangulation tr data ->
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
           oriented_triangle_triangulation (flip_edge tr t1 t2 a b c d).
Proof.
move => tr_d t1 t2 t1_nt2 t1_tr t2_tr a c a_nc a_t1 a_t2 c_t1 c_t2 b b_t1 b_na
    b_nc oriented_abc d d_t2 d_na d_nc oriented_acd islo_bcd islo_abd.
move:(tr_d) => [_ [_ [_ [_ [_ or_tr_d]]]]].
move => t.
rewrite /flip_edge.
move => /fsetUP [];last by move => /fsetD1P [] _ /fsetD1P [] _;apply: or_tr_d.
rewrite /flip_edge_aux.
by move => /fset2P [] ->;
[have vc := vertices_to_triangle_correct (is_lof_imply_is_lor_on_line islo_abd)|
 have vc := vertices_to_triangle_correct (is_lof_imply_is_lor_on_line islo_bcd)];
move:vc => [v1[v2 v3]];rewrite /oriented_triangle_strict /vertex1 /vertex2 /vertex3
      -v1 -v2 -v3.
Qed.

Lemma flip_edge_triangulation tr data : triangulation tr data ->
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
move => tr_d t1 t2 t1_nt2 t1_tr t2_tr a c a_nc a_t1 a_t2 c_t1 c_t2 b b_t1 b_na
    b_nc oriented_abc d d_t2 d_na d_nc oriented_acd islo_bcd islo_abd.
move:(tr_d) => [tr3v_tr_d [cvh_tr_d [cvv_tr_d [nci_tr_d nps_tr_d]]]].
have vc_abd := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line islo_abd).
have vc_bcd := vertices_to_triangle_correct
                         (is_lof_imply_is_lor_on_line islo_bcd).
move : (vc_abd) => [a_abd [b_abd d_abd]].
move : (vc_bcd) => [b_bcd [c_bcd d_bcd]].
split;first by apply: flip_edge_cvh.
split;first by apply: flip_edge_cvv.
split;first by apply: flip_edge_nci.
split;first by apply: flip_edge_nps.
split;first by apply:flip_edge_tne => //; apply: tr_d.
by apply:flip_edge_or => //=; apply: tr_d.
Qed.

End Triangulation.

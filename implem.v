From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple.
From mathcomp Require Import choice path finset finfun fintype bigop.
From mathcomp Require Import ssralg ssrnum matrix mxalgebra.
From mathcomp Require Import finmap.
From mathcomp Require Import vector perm.
Require Import triangulation.
Require Import determinant_complements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Local Scope nat_scope.

Definition ord10:=@Ordinal 1 0 isT.
(*Definition ord20:=@Ordinal 2 0 isT.
Definition ord21:=@Ordinal 2 1 isT.
Definition ord30:=@Ordinal 3 0 isT.
Definition ord31:=@Ordinal 3 1 isT.
Definition ord32:=@Ordinal 3 2 isT.*)
Import GRing.Theory Num.Theory.



Open Local Scope ring_scope.

Variable R : realDomainType.


Definition my_type := GRing.Zmodule.sort (Num.RealDomain.zmodType R).
Definition my_mul :my_type -> my_type -> my_type := @GRing.mul R.
Definition my_add :my_type -> my_type -> my_type:= @GRing.add R.
Definition my_sub :my_type -> my_type -> my_type:= fun (x y : R) => x - y.
Definition my_opp :my_type -> my_type := @GRing.opp R.
Definition my_ring_theory := @mk_rt my_type 0 1 my_add my_mul my_sub my_opp (@eq _)
(@add0r R) (@addrC R) (@addrA R) (@mul1r R) (@mulrC R) (@mulrA R) (@mulrDl R)
(fun x y => erefl _) (@addrN R).

Add Ring my_ring : my_ring_theory.

Ltac rring := 
rewrite !mulr1 !mul1r -/my_mul -/my_opp -/my_add -/my_type;ring.

Definition P := 'rV[R]_2. 
Definition xCoord (p : P) := p ord10 ord20.
Definition yCoord (p : P) := p ord10 ord21.

Definition matrix_oriented_surface (p a b : P) :=
  \matrix_( i<3, j<3) if i==ord30 then if j==ord30 then xCoord p
                                        else if j==ord31 then yCoord p
                                               else 1%R
                             else if i==ord31 then if j==ord30 then xCoord a
                                               else if j==ord31 then yCoord a
                                                    else 1%R
                                  else if j==ord30 then xCoord b
                                       else if j==ord31 then yCoord b
                                            else 1%R.

Definition oriented_surface (a b c : P):=
\det (matrix_oriented_surface a b c).

Definition is_left_of := is_left_of oriented_surface.

Definition is_left_or_on_line := is_left_or_on_line oriented_surface.




Definition T := 'rV[P]_3.


Definition vertex (t : T) := t ord10.

Definition vertex1 := vertex1 vertex.

Definition vertex2 := vertex2 vertex.

Definition vertex3 := vertex3 vertex.

Definition E := 'rV[P]_2.

Open Local Scope ring_scope.

Definition vertices_to_edge_aux (p1:P) (p2:P) :=
  \matrix_(j<1, i<2) (if i == ord20 then p1 else p2).


Definition vertices_to_edge (p1 : P) (p2 : P): E :=
  if xCoord p1 < xCoord p2 then 
    vertices_to_edge_aux p1 p2
  else if xCoord p2 < xCoord p1 then
         vertices_to_edge_aux p2 p1
       else if yCoord p1 < yCoord p2 then
              vertices_to_edge_aux p1 p2
            else vertices_to_edge_aux p2 p1.

Definition edge t i :=
  if i == ord30 then vertices_to_edge (vertex1 t) (vertex2 t)
  else if i==ord31 then vertices_to_edge (vertex2 t) (vertex3 t)
       else vertices_to_edge (vertex3 t) (vertex1 t).

Definition vertex_edge (e:E) := e ord10.

Definition vertices_to_triangle (a b c : P) : T :=
  if is_left_or_on_line a b c then 
    \matrix_(j<1, i<3) (if i == ord30 then a
                        else if i == ord31 then b
                             else c)
  else \matrix_(j<1, i<3) ( if i == ord30 then b
                            else if i == ord31 then a
                                 else c).


Lemma vertices_to_triangle_correct a b c: 
    is_left_or_on_line a b c ->
    a = vertex (vertices_to_triangle a b c) ord30 /\
    b = vertex (vertices_to_triangle a b c) ord31 /\
    c = vertex (vertices_to_triangle a b c) ord32.
Proof.
by move => islor_abc; split;last split;
rewrite /vertices_to_triangle /vertex islor_abc => /=;
rewrite mxE.
Qed.

Definition vertex_set_edge := vertex_set_edge vertex_edge.

Lemma vertices_to_edge_correct a b:
 vertex_set_edge (vertices_to_edge a b) = [fset a;b].
Proof.
rewrite /vertices_to_edge.
by case:(xCoord a < xCoord b);case(yCoord a < yCoord b);
case:(xCoord b < xCoord a); apply /eqP;
rewrite eqEfsubset;apply/andP;split;apply/fsubsetP;move => x;
try (move => /fset2P [] ->;
rewrite /vertices_to_edge_aux;
rewrite /vertex_set_edge /triangulation.vertex_set_edge;
apply/imfsetP);
try(by exists ord20 => //=; rewrite /vertex_edge mxE );
try(by exists ord21 => //=; rewrite /vertex_edge mxE );
rewrite /vertex_set_edge /triangulation.vertex_set_edge;
move=>/imfsetP [[[|[|[|x']]] px'] _ ] => //=;
try (have:Ordinal px' = ord20 by apply ord_inj);
try (have:Ordinal px' = ord21 by apply ord_inj);
move ->; rewrite /vertex_edge mxE /= => ->;apply  /fset2P;
(try by left);
right.
Qed.

Lemma oriented_surface_x_x x y: oriented_surface x x y = 0%R.
Proof.
rewrite /oriented_surface /matrix_oriented_surface.
have ord301:(ord30 != ord31) by []. 
apply:(determinant_alternate ord301).
move =>[[|[|[|k]]] pk] => //=;
rewrite !mxE => //=.
Qed.

Lemma eq_or_inf (a:R) b: a<b \/ a=b \/ a>b.
Proof.
case ab:(a < b);case ba:(b < a);try (by left);try (by right;right);right;left.
move:ab=> /negP /negP;rewrite -lerNgt => ab.
move:ba=> /negP /negP;rewrite -lerNgt => ba;symmetry;apply /eqP.
move:(ab);rewrite ler_eqVlt => /orP [] //=.
by rewrite ltrNge ba.
Qed.

Lemma coord_eq_imply_point_eq (a:P) b :
  xCoord a = xCoord b -> yCoord a = yCoord b -> a=b.
Proof.
move => xa xb.
rewrite -matrixP.
move => x y.
move:x=>[[|x'] px] => //=.
have:Ordinal px = ord10.
  by apply ord_inj.
move => ->.
by move:y=>[[|[|y']] py] => //=;
[have:Ordinal py = ord20|have:Ordinal py = ord21];(try by apply ord_inj) => //= ->.
Qed.

Lemma inf_imply_not_inf (a:R) b : a<b -> (b<a) = false. 
Proof.
rewrite ltrNge ler_eqVlt.
move => /orP /Decidable.not_or [] _ H. by apply/negP.
Qed.


Lemma vertices_to_edge_sym a b :
 vertices_to_edge a b = vertices_to_edge b a.
Proof.

rewrite /vertices_to_edge.
have xCoord_disj := eq_or_inf (xCoord a) (xCoord b).
have yCoord_disj := eq_or_inf (yCoord a) (yCoord b);
move:xCoord_disj => [] [] xab;rewrite xab;
move:yCoord_disj => [] [] yab;(try rewrite yab);
try(have xba:=inf_imply_not_inf xab;rewrite xba);
try(have yba:=inf_imply_not_inf yab;rewrite yba) => //=;
(try rewrite !ltrr) => //=.
rewrite /vertices_to_edge_aux.
have ab :a=b by apply coord_eq_imply_point_eq.
by apply matrixP; rewrite ab.
Qed.


Definition in_circle_determinant (p a b c : P) :=
  let M:= \matrix_(i<4, j<4) if i == @Ordinal 4 0 isT then if j==@Ordinal 4 0 isT then
                                     xCoord a
                                         else if j==@Ordinal 4 1 isT  then
                                     yCoord a
                                         else if j== @Ordinal 4 2 isT  then
                         (xCoord a) ^+ 2
                            + (yCoord a)^+2
                                         else 1%R
                           else if i == @Ordinal 4 1 isT  then if j== @Ordinal 4 0 isT  then
                                     xCoord b
                                         else if j==@Ordinal 4 1 isT  then
                                     yCoord b
                                         else if j== @Ordinal 4 2 isT  then 
                         (xCoord b)^+2
                            + (yCoord b)^+2
                                         else 1%R
                           else if i == @Ordinal 4 2 isT  then if j== @Ordinal 4 0 isT  then
                                     xCoord c
                                         else if j== @Ordinal 4 1 isT  then
                                     yCoord c
                                         else if j== @Ordinal 4 2 isT  then 
                         (xCoord c)^+2
                            + (yCoord c)^+2
                                         else 1%R
                           else if j== @Ordinal 4 0 isT  then
                                     xCoord p
                                else if j== @Ordinal 4 1 isT  then
                                     yCoord p
                                         else if j== @Ordinal 4 2 isT  then 
                                     (xCoord p)^+2 + (yCoord p)^+2 
                                         else 1%R
  in (\det M).

Definition in_circle := in_circle in_circle_determinant.

Definition oriented_triangle := oriented_triangle vertex oriented_surface.

Definition vertex_set := vertex_set vertex.

Lemma vertices_to_triangle_correct2 : forall p1 p2 p3, forall t,
          (t = vertices_to_triangle p1 p2 p3) ->
  ((p1 \in vertex_set t) /\ (p2 \in vertex_set t) /\ (p3 \in vertex_set t)).
Proof.
move => p1 p2 p3 t ->.
split;last split;
rewrite /vertex_set /triangulation.vertex_set;
apply /imfsetP;rewrite /vertices_to_triangle;
case:(is_left_or_on_line p1 p2 p3);
try ( by exists ord30 => //=; rewrite /vertex mxE);
try ( by exists ord31 => //=; rewrite /vertex mxE);
try ( by exists ord32 => //=; rewrite /vertex mxE).
Qed.

Definition edges_set := edges_set edge.

Lemma vertex_set_edge_triangle :
  forall t, forall (a:P), a \in vertex_set t ->  forall (b:P), b \in vertex_set t -> a!=b ->
            (vertices_to_edge a b) \in edges_set t.
Proof.
move => t a a_t b b_t a_nb.
rewrite /edges_set /triangulation.edges_set.
move:a_t => /imfsetP [x _] a_tx.
move:b_t => /imfsetP [y _] b_ty.
move: a_tx;move: x =>[[|[|[|x']]] px] a_tx;rewrite a_tx;
(try have:Ordinal px = ord30 by apply ord_inj);
(try have:Ordinal px = ord31 by apply ord_inj);
(try have:Ordinal px = ord32 by apply ord_inj) => px_ord;
rewrite px_ord;rewrite px_ord in a_tx;
move: b_ty;move: y =>[[|[|[|y']]] py] b_ty; rewrite b_ty;
(try have:Ordinal py = ord30 by apply ord_inj);
(try have:Ordinal py = ord31 by apply ord_inj);
(try have:Ordinal py = ord32 by apply ord_inj) => py_ord;
rewrite py_ord;rewrite py_ord in b_ty =>  //=;
(try have ab : a = b by rewrite a_tx b_ty);
(try by move:a_nb;rewrite ab => /eqP);
apply /imfsetP;
[exists ord30|exists ord32|exists ord30|exists ord31|exists ord32|exists ord31] => //=;
rewrite /edge /vertex1 /vertex2 /vertex3 /triangulation.vertex1
/triangulation.vertex2 /triangulation.vertex3=> //=;
try (by rewrite vertices_to_edge_sym).
Qed.


Lemma oriented_surface_circular a b c:
  oriented_surface a b c = oriented_surface c a b.
Proof.
rewrite /oriented_surface.
rewrite !expand_det33.
rewrite /matrix_oriented_surface.
rewrite !mxE => /=.
rring.
Qed.


Lemma oriented_surface_change1 a b c:
        oriented_surface a b c = -oriented_surface a c b.
Proof.
rewrite /oriented_surface.
rewrite !expand_det33.
rewrite /matrix_oriented_surface.
rewrite !mxE => //=.
rring.
Qed.
  

Definition is_left_or_on_line_circular :=
  is_left_or_on_line_circular oriented_surface_circular.
Lemma vertices_to_triangle_oriented  a b c :
  oriented_triangle (vertices_to_triangle a b c).
Proof.
rewrite /vertices_to_triangle.
case islor_abc:(is_left_or_on_line a b c);
rewrite /oriented_triangle /triangulation.oriented_triangle;
rewrite /vertex /triangulation.vertex1 /triangulation.vertex2;
rewrite  /triangulation.vertex3;
rewrite !mxE => //=.
rewrite /is_left_or_on_line in islor_abc.
rewrite is_left_or_on_line_circular in islor_abc. 
move:islor_abc.
rewrite /triangulation.is_left_or_on_line lerNgt.
move => /negP /negP.
by rewrite -oppr_gt0 -oriented_surface_change1
   -oriented_surface_circular ltr_def => /andP [].
Qed.

Definition is_left_of_circular := is_left_of_circular oriented_surface_circular.

Lemma edges_set_vertices_to_triangle a b c: 
  is_left_of a b c ->
  edges_set (vertices_to_triangle a b c) = 
  [fset (vertices_to_edge a b);
     vertices_to_edge a c;
     vertices_to_edge b c].
Proof.
rewrite /edges_set /triangulation.edges_set.
symmetry.
apply/eqP.
rewrite eqEfcard.
apply /andP;split.
  by apply/fsubsetP => x /fsetUP [/fset2P []|/fset1P] ->;
  apply /imfsetP;rewrite /edge /vertices_to_triangle;
  case islor:(is_left_or_on_line a b c) => /=;
  [exists ord30|exists ord30|exists ord32|exists ord31|exists ord31|exists ord32]=> //=;
  rewrite /vertex1 /vertex2 /vertex3 /triangulation.vertex1
  /triangulation.vertex2 /triangulation.vertex3 /vertex !mxE => //=;
  rewrite vertices_to_edge_sym.
suff card_fset3 : #|` [fset vertices_to_edge a b; vertices_to_edge a c; vertices_to_edge b c] | = 3%N.
  rewrite card_fset3 (leq_trans (leq_imfset_card _ _)) //.
  by rewrite card_finset card_ord.
case a_nb : (a == b);first move:a_nb => /eqP a_b;first move:H;
first by rewrite /is_left_of a_b /triangulation.is_left_of oriented_surface_x_x ltrr.
move:a_nb => /eqP /eqP a_nb.
rewrite /is_left_of is_left_of_circular in H.
case a_nc : (a == c);first move:a_nc => /eqP a_c;first move:H;
first by rewrite /is_left_of a_c /triangulation.is_left_of oriented_surface_x_x ltrr.
move:a_nc => /eqP /eqP a_nc.
rewrite /is_left_of is_left_of_circular in H.
case b_nc : (b == c);first move:b_nc => /eqP b_c;first move:H;
first by rewrite /is_left_of b_c /triangulation.is_left_of oriented_surface_x_x ltrr.
move:b_nc => /eqP /eqP b_nc.

case vab_nac :(vertices_to_edge a b == vertices_to_edge a c).
  have:false.
    move:vab_nac.
    by rewrite /vertices_to_edge;case:(xCoord a < xCoord b);case(xCoord b < xCoord a);
    case:(yCoord a < yCoord c);case:(xCoord a < xCoord c);case:(xCoord c < xCoord a);
    case:(yCoord a < yCoord b) => /=;
    rewrite /vertices_to_edge_aux => /eqP;
    rewrite -matrixP => H2;
    (try by (have abs := H2 ord10 ord21;move:abs;
    rewrite !mxE => //= H3;
    (try by move:b_nc;rewrite H3 => /eqP);
    (try by move:a_nb;rewrite H3 => /eqP);
    (try by move:a_nc;rewrite H3 => /eqP)));
    have abs := H2 ord10 ord20;move:(abs);
    rewrite !mxE => //= H3;
    (try by move:b_nc;rewrite H3 => /eqP);
    (try by move:a_nb;rewrite H3 => /eqP);
    (try by move:a_nc;rewrite H3 => /eqP).
 by [].
case vab_nbc :(vertices_to_edge a b == vertices_to_edge b c).
  have:false.
    move:vab_nbc.
    by rewrite /vertices_to_edge;case:(xCoord a < xCoord b);case:(xCoord b < xCoord a);
    case:(xCoord b < xCoord c);case:(xCoord c < xCoord b);case:(yCoord b  < yCoord c);
    case:(yCoord a < yCoord b) => /=;
    rewrite /vertices_to_edge_aux => /eqP;
    rewrite -matrixP => H2;
    (try by (have abs := H2 ord10 ord21;move:abs;
    rewrite !mxE => //= H3;
    (try by move:b_nc;rewrite H3 => /eqP);
    (try by move:a_nb;rewrite H3 => /eqP);
    (try by move:a_nc;rewrite H3 => /eqP)));
    have abs := H2 ord10 ord20;move:(abs);
    rewrite !mxE => //= H3;
    (try by move:b_nc;rewrite H3 => /eqP);
    (try by move:a_nb;rewrite H3 => /eqP);
    (try by move:a_nc;rewrite H3 => /eqP).
  by [].

case vbc_nac :(vertices_to_edge a c == vertices_to_edge b c).
  have:false.
    move:vbc_nac.
    rewrite /vertices_to_edge;case:(xCoord a < xCoord c);case:(xCoord c < xCoord a);
    case:(xCoord b < xCoord c);case:(xCoord c < xCoord b);case:(yCoord a  < yCoord c);
    case:(yCoord b < yCoord c) => /=;
    rewrite /vertices_to_edge_aux => /eqP;
    rewrite -matrixP => H2;
    (try by (have abs := H2 ord10 ord21;move:abs;
    rewrite !mxE => //= H3;
    (try by move:b_nc;rewrite H3 => /eqP);
    (try by move:a_nb;rewrite H3 => /eqP);
    (try by move:a_nc;rewrite H3 => /eqP)));
    have abs := H2 ord10 ord20;move:(abs);
    rewrite !mxE => //= H3;
    (try by move:b_nc;rewrite H3 => /eqP);
    (try by move:a_nb;rewrite H3 => /eqP);
    (try by move:a_nc;rewrite H3 => /eqP).
  by [].
rewrite !cardfsU !cardfs1 fsetI1 !inE.
move:vab_nac => /negP /negP vab_nac.
move:vab_nbc => /negP /negP vab_nbc.
move:vbc_nac => /negP /negP vbc_nac.

rewrite [vertices_to_edge a c == vertices_to_edge a b]eq_sym (negPf vab_nac) cardfs0.
rewrite fsetI1 !inE ![vertices_to_edge b c == _]eq_sym.
by rewrite  (negPf vab_nbc) (negPf vbc_nac) /= cardfs0.
Qed.


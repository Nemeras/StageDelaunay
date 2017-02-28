From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple.
From mathcomp Require Import choice path finset finfun fintype bigop.
From mathcomp Require Import ssralg ssrnum matrix mxalgebra.
From mathcomp Require Import finmap.
From mathcomp Require Import zmodp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

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
 (\sum_ i (a i) == 1) /\ (forall i, (0 <= (a i))) /\ (d != fset0).

Definition encompassed x h := ucycle (is_left_or_on_line x) h.

Definition all_left_of (d : {fset P}) x y  := [forall p : d, is_left_or_on_line x y (val p)].

Open Local Scope nat_scope.

Definition CH (s : seq P) (d : {fset P}) := ((seq_fset s) `<=` d) /\
                                            (forall x, x \in d -> encompassed x s) /\
                                            (#|`d| >= 2 -> (size s) >= 2) /\
                                            (#|`d| = 1 -> (size s) = 1).

Hypothesis encompassed_ch : forall d : {fset P}, forall x, 0 < #|`d| -> hull d x = forall h,  (CH h d  -> encompassed x h).


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
  forall t1, forall t2, t1 \in tr -> t2 \in tr ->  forall p, in_triangle t1 p -> in_triangle t2 p -> t1 = t2.

Definition regular (Ts:{fset T})  := forall t1 , forall t2,
      t1 \in Ts -> t2 \in Ts ->
                         forall p, p \in vertex_set t1-> in_circle_triangle p t2 -> false.

Definition no_point_on_segment (tr : {fset T}) (d : {fset P}) :=
  forall t1, forall t2,t1 \in tr -> t2 \in tr -> forall p, p \in vertex_set t1 -> in_triangle_w_edges t2 p -> p \in vertex_set t2.

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

Open Local Scope ring_scope.




Lemma hull_add_point p d: p \notin d -> hull d p ->
   forall q, hull (p |` d ) q -> hull d q.
Proof.
move => npd [b [b_x [b_y [bsum [bpos dne]]]]] q [a [a_x [a_y [asum [apos _]]]]].
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
  (* stopped here. *)

split;last by [].
move => i.
rewrite /c.
apply:addr_ge0 => //=.
by apply:mulr_ge0 => //=.
Qed.
(* useless part from here
Search "big" "distr".
have t := (big_split (GRing.add_comoid R) (index_enum (fset_sub_finType (p |` d))) (fun x : fset_sub_finType (p |` d) => x != p')
            (fun i => a (fincl dpd (insubd [` p1_in_d] (fsval i))))
            (fun i => a p' * b (insubd [` p1_in_d] (fsval i)))).
simpl in t.
rewrite [X in _ == X]t.
move => ->.
set u := BigOp.bigop.

  rewrite [X in _ == X].
            .
              (fun i => a (fincl dpd (insubd [` p1_in_d] (val i))) +
                        a p' * b (insubd [` p1_in_d] (val i)))).
Search "mkcond".
have separation : \sum_i ((a i) * xCoord (val i)) = (a p') *(xCoord p) + 
                                                    \sum_(i | i != p') ((a i) * xCoord (val i)) 
by rewrite (bigD1 p').
rewrite (eqP a_x) separation.
rewrite (eqP b_x).
rewrite big_distrr => /=.


pose b' := fun i =>  if i==p' then 0 else b (insubd [` p1_in_d] (val i)).
rewrite (eq_big _ (fun i : d => (a p') * (b' (h i) * xCoord (val (h i)))) (reindex_h)); last first.
  move =>i _;rewrite /b'.
  case hv : (h i == p').
    by case/negP:npd; rewrite -[p]/(val p') -(eqP hv) {hv}; case: i.
  congr (_ * _).
  congr (b _ * _ ).
  by apply/val_inj; rewrite val_insubd /= {hv}; case: i  => /= i' ->.
pose F' := fun i => a p' * (b' i * xCoord (val i) ).  
have reindexation2 : \sum_(i | i != p') (F' i) = 
                     \sum_(i | h i != p') (F' (h i)) by rewrite (reindex h).
rewrite -reindexation2.
rewrite -big_split => /=.
have eq_f_f' : forall i, i != p' -> F' i + a i * xCoord (fsval i) = F i.
  move => i => nip ; rewrite /F /F' /c'/b' => /=.
  case abs :(i==p');first by rewrite abs in nip.
  rewrite /c.
  have -> :(fincl dpd (insubd  [` p1_in_d] (fsval i)) = i).
  destruct abs.
  apply/val_inj => /= ; rewrite val_insubd  => /=.
  have i_d : (fsval i = p) \/ (fsval i \in d) by  apply /fset1UP.
  case i_d => valip.
  rewrite valip.
  case abs:(p \in d);first by [].
  
Check npd.
  simpl.
*)
      
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



   Lemma hull_from_triangle :
  forall d, forall tr, forall t, forall p, triangulation tr d -> t \in tr -> in_triangle t p -> hull d p.
  Proof.
move => d tr t p tr_d t_tr intp.
rewrite /triangulation in tr_d.
move:tr_d =>[covh_tr_d [covv_tr_d nps_tr_d]].   
rewrite /covers_hull in covh_tr_d.
rewrite /hull.
Admitted.


  Theorem triangulation_split_triangle:
  forall tr, forall t , forall p, forall d, triangulation tr d -> t \in tr -> in_triangle t p ->
                      triangulation (split_triangle tr t p) (p |` d).
 move => tr t p d tr_d t_tr intp.
rewrite /triangulation in tr_d.
rewrite /triangulation.
split.
  rewrite /covers_hull.
  move => q hull_pdq.
  move:tr_d => [covh_tr_d [covv_tr_d nps_tr_d]].
  case p_q:(p==q).
  rewrite /split_triangle.
  rewrite /covers_hull in covh_tr_d.
  

  rewrite /split_triangle_aux.
  
(*
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
*)
  Admitted.

  Theorem flip_edge_triangulation : forall tr, forall d, triangulation tr d -> forall t1, forall t2, t1 != t2 -> t1 \in tr-> t2 \in tr ->
                                    forall p1, forall p2, p1 \in vertex_set t1 -> p1 \in vertex_set t1 ->
                                    p2 \in vertex_set t1 -> p2 \in vertex_set t2 ->
                                    triangulation (flip_edge tr t1 t2 p1 p2) d.
Proof.
  move => tr d tr_d t1 t2 t1_not_t2 t1_tr t2_tr p1 p2 p1_t1 p1_t2 p2_t1 p2_t2.

  rewrite /triangulation in tr_d.
  move:tr_d =>[covh_tr_d [covv_tr_d nps_tr_d]].  

  rewrite /triangulation.
  split.
    rewrite /covers_hull.
    move => p => hull_d_p.
    rewrite /covers_hull in covh_tr_d.
    have exists_t_covh : exists t, t \in tr /\ in_triangle_w_edges t p by apply covh_tr_d.
    move :exists_t_covh => [t [t_tr t_intwe]].
    case t_t1_t2:((t==t1) || (t==t2)).
    move:t_t1_t2 => /orP t_t1_t2.
    destruct t_t1_t2.
    (*there should be a better way to do that in ssreflect.*)
      admit.
      admit.
    move:t_t1_t2 => /norP [t_t1 t_t2].
    exists t.
    split;trivial;rewrite /flip_edge.
    
End Triangulation.
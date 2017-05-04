From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple.
From mathcomp Require Import choice path finset finfun fintype bigop.
From mathcomp Require Import ssralg ssrnum matrix mxalgebra.
From mathcomp Require Import finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Local Scope nat_scope.

Definition ord10:=@Ordinal 1 0 isT.
Definition ord20:=@Ordinal 2 0 isT.
Definition ord21:=@Ordinal 2 1 isT.
Definition ord30:=@Ordinal 3 0 isT.
Definition ord31:=@Ordinal 3 1 isT.
Definition ord32:=@Ordinal 3 2 isT.

Open Local Scope ring_scope.

Require Import triangulation.


Variable R : realDomainType.

Definition P := 'rV[R]_2. 


Definition xCoord (p : P) := p ord10 ord20.
Definition yCoord (p : P) := p ord10 ord21.

Definition T := 'rV[P]_3.

Definition vertex (t : T) := t ord10.

Definition E := 'rV[P]_2.
Definition vertices_to_edge_aux (p1:P) (p2:P) :=
  \matrix_(j<1, i<2) (if i == ord20 then p1 else p2).

Axiom a:P.
Check vertices_to_edge_aux a a.
Definition vertices_to_edge (p1 : P) (p2 : P): E :=
  if xCoord p1 < xCoord p2 then 
    vertices_to_edge_aux p1 p2
  else vertices_to_edge_aux p2 p1.
Definition vertex_edge (e:E) := e ord10.

Definition matrix_oriented_surface (p a b : P) :=
  \matrix_( i<3, j<3) if i==ord30 then if j==ord30 then xCoord p
                                        else if j==@Ordinal 3 1 isT then yCoord p
                                               else 1%R
                             else if i==ord31 then if j==ord30 then yCoord a
                                               else if j==ord31 then yCoord a
                                                    else 1%R
                                  else if j==ord30 then xCoord b
                                       else if j==ord31 then yCoord b
                                            else 1%R.
Check matrix_oriented_surface.


Definition oriented_surface (a b c : P):= \det (matrix_oriented_surface a b c).

Definition is_left_of := (triangulation.is_left_of oriented_surface).

Definition vertices_to_triangle (a b c : P) : T :=
  if is_left_of a b c then 
    \matrix_(j<1, i<3) (if i == ord30 then a
                        else if i == ord31 then b
                             else c)
  else \matrix_(j<1, i<3) ( if i == ord30 then b
                            else if i == ord31 then a
                                 else c).

       
(*Definition in_circle_determinant (p a b c : P) :=
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
  in (\det M).*)

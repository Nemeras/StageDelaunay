From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple.
From mathcomp Require Import choice path finset finfun fintype bigop.
From mathcomp Require Import ssralg ssrnum matrix mxalgebra.
From mathcomp Require Import finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Open Local Scope ring_scope.

Require Import triangulation.

Variable P : choiceType.
Variable T : choiceType.
Variable R : numDomainType.
Variable x_coord : P -> R.
Variable y_coord : P -> R.
Variable vertex : T -> P^3.

Definition oriented_surface := fun (p a b : P) =>
 let M1 := \matrix_( i<3, j<3) if i==@Ordinal 3 0 isT then if j==@Ordinal 3 0 isT then x_coord p
                                        else if j==@Ordinal 3 1 isT then y_coord p
                                               else 1%R
                             else if i==@Ordinal 3 1 isT then if j==@Ordinal 3 0 isT then y_coord a
                                               else if j==@Ordinal 3 1 isT then y_coord a
                                                    else 1%R
                                  else if j==@Ordinal 3 0 isT then x_coord b
                                       else if j==@Ordinal 3 1 isT then y_coord b
                                            else 1%R
  in \det M1.


Definition in_circle_determinant (p a b c : P) :=
  let M:= \matrix_(i<4, j<4) if i == @Ordinal 4 0 isT then if j==@Ordinal 4 0 isT then
                                     x_coord a
                                         else if j==@Ordinal 4 1 isT  then
                                     y_coord a
                                         else if j== @Ordinal 4 2 isT  then
                         (x_coord a)^+2
                            + (y_coord a)^+2
                                         else 1%R
                           else if i == @Ordinal 4 1 isT  then if j== @Ordinal 4 0 isT  then
                                     x_coord b
                                         else if j==@Ordinal 4 1 isT  then
                                     y_coord b
                                         else if j== @Ordinal 4 2 isT  then 
                         (x_coord b)^+2
                            + (y_coord b)^+2
                                         else 1%R
                           else if i == @Ordinal 4 2 isT  then if j== @Ordinal 4 0 isT  then
                                     x_coord c
                                         else if j== @Ordinal 4 1 isT  then
                                     y_coord c
                                         else if j== @Ordinal 4 2 isT  then 
                         (x_coord c)^+2
                            + (y_coord c)^+2
                                         else 1%R
                           else if j== @Ordinal 4 0 isT  then
                                     x_coord p
                                else if j== @Ordinal 4 1 isT  then
                                     y_coord p
                                         else if j== @Ordinal 4 2 isT  then 
                                     (x_coord p)^+2 + (y_coord p)^+2 
                                         else 1%R
  in (\det M).


Check in_circle in_circle_determinant.
Check in_circle_triangle .

Check in_circle_triangle vertex in_circle_determinant.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple.
From mathcomp Require Import choice path finset finfun fintype bigop.
From mathcomp Require Import ssralg ssrnum matrix mxalgebra.
From mathcomp Require Import finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import triangulation.

Open Local Scope ring_scope.


Definition orientedSurface := fun (p a b : P) =>
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


Definition inCircle (p a b c : P) :=
  let M:= \matrix_(i<4, j<4) if i == @Ordinal 4 0 isT then if j==@Ordinal 4 0 isT then
                                     xCoord a
                                         else if j==@Ordinal 4 1 isT  then
                                     yCoord a
                                         else if j== @Ordinal 4 2 isT  then
                         (xCoord a)^+2
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
   in (\det M >0).

Definition inCircleTriangle p t := inCircle p (vertex1 t) (vertex2 t) (vertex3 t).





Definition isLeftOf := fun (p a b : P) =>
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
              

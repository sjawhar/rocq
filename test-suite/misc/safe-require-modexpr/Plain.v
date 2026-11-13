From SafeModExpr Require M MF.
Module Type A := M.N.T.
Module B := M.N.
Module Type W := M.N.T with Definition x := 0.
Module Type I. Include M.N.T. End I.
Module L := M.
Declare Module D : M.N.T.
Module S : M.N.T. Definition x := 0. End S.
Module F (X : M.N.T). End F.
Module Type E. End E.
Module G (X : E). End G.
Module Ap := G M.N.
Module U <: M.N.T. Definition x := 0. End U.
Print Module MF.F.
Import M.
Module Type A2 := N.T.

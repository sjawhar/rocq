From SafeModExpr Require (safe) M MF.
Module Type E. End E.
Module G (X : E). End G.
Module B := G M.N.
Module X <: M.N.T. Definition x := 0. End X.
Print Module MF.F.

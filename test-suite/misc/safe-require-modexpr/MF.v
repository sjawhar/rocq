Module Type S. Parameter x : nat. End S.
Module F (X : S). Definition y := X.x. End F.

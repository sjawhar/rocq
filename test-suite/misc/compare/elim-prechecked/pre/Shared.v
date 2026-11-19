(* The library the config declares pre-checked, Pre.Shared: one file for
   both sides. It declares the global sort s and an inductive type box in
   it, and no elimination constraint on s. *)

Sort s.

Inductive box : Type@{s;_} := mk : box.

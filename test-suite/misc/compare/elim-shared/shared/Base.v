(* One of the image's own installed libraries, Img.Base: one file for both
   sides, read from the load path, bound by no -Q and pinned by no config.
   It declares the global sort s and an inductive type box in it, and no
   elimination constraint on s. *)

Sort s.

Inductive box : Type@{s;_} := mk : box.

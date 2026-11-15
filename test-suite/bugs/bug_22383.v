
Set Universe Polymorphism.

Fail Cumulative Inductive token@{*u v | u < v} : Set :=
| make_token (ghost : Type@{v} := Type@{u}).

Cumulative Inductive token@{u v | u < v} : Set :=
| make_token (ghost : Type@{v} := Type@{u}).

Definition read_token@{u v | u < v} (t : token@{u v}) : Type@{v} :=
  match t with make_token ghost => ghost end.

Fail Definition small@{u v | Set < u, u < v} : Type@{u} :=
  read_token@{Set u} (make_token@{u v}).

(* The position is invariant, not covariant: asking for covariance in the
   letin's universe must be refused too. *)
Fail Cumulative Inductive tokcov@{+u v | u < v} : Set :=
| make_tokcov (ghost : Type@{v} := Type@{u}).

(* Since #22681 the type of a letin is inferred as a CUMUL position, as the
   type of an argument is, so a universe that occurs only in its type is
   covariant, not irrelevant (see bug_22675.v, only_type). *)
Fail Cumulative Inductive typed_only@{*u} : Set :=
| make_typed_only (ghost : Type@{u} := nat).

Cumulative Inductive typed_only@{+u} : Set :=
| make_typed_only (ghost : Type@{u} := nat).

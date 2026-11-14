(* A tolerated uip flag, in both forms. The config has no allow_uip input,
   so a kind-only uip entry is that switch: the task saying definitional
   UIP is allowed wherever its proof reaches. An entry with an object allows
   it on that object alone, when the object is the task's declaration.

   The task declares seq under definitional UIP, and thm does not mention
   it, so an honest proof of thm reaches no object that carries uip. The
   config tolerates uip on Top.A.seq2 alone, a name the task does not hold.
   An index of seq has its type in Type, so seq, like Corelib.Init.Logic.eq,
   also carries indices-not-mattering; every config of the case tolerates
   that kind on every object (flags-kind-only), so that uip is the one flag
   a verdict turns on.

   bad-task-seq proves thm through the task's seq: the config does not
   tolerate uip on it, and its tolerate-uip config, which names Top.A.seq,
   does. bad-own-seq proves thm through a seq2 of its own: the config's
   entry for Top.A.seq2 does not reach an object only the answer declares,
   and its tolerate-uip config, with a kind-only uip entry, does. *)

Set Definitional UIP.

Inductive seq {A : Type} (a : A) : A -> SProp := srefl : seq a a.

Unset Definitional UIP.

Theorem thm : forall (P : nat -> Prop) (n : nat), P n -> P n.
Proof.
Admitted.

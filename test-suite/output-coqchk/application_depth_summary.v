(* Applications nested deeper than rocqchk -o reads them: App is C65's body,
   App.M C64's, and so on down to C0's, 66 applications on one path, and
   boom_deep rests on the axiom a of C0's body, read at SDeep.App.M...M with
   65 times M. The walk reads App and each application under it down to
   App.M...M with 63 times M, C2's body, and stops at the next one, C1's
   body, read inside 64 nested applications. It has not read C0's body,
   which declares a, so rocqchk -o refuses to print a summary.
   misc/rocqchk_application_bound_summary.sh checks the same shape, with
   result types that name no axiom, with and without -o. *)

Module Type Empty. End Empty.
Module E. End E.
Module Type UseT. Parameter use : False. End UseT.

Module C0 (X : Empty). Axiom a : False. End C0.
Module C1 (X : Empty). Module M := C0 X. End C1.
Module C2 (X : Empty). Module M := C1 X. End C2.
Module C3 (X : Empty). Module M := C2 X. End C3.
Module C4 (X : Empty). Module M := C3 X. End C4.
Module C5 (X : Empty). Module M := C4 X. End C5.
Module C6 (X : Empty). Module M := C5 X. End C6.
Module C7 (X : Empty). Module M := C6 X. End C7.
Module C8 (X : Empty). Module M := C7 X. End C8.
Module C9 (X : Empty). Module M := C8 X. End C9.
Module C10 (X : Empty). Module M := C9 X. End C10.
Module C11 (X : Empty). Module M := C10 X. End C11.
Module C12 (X : Empty). Module M := C11 X. End C12.
Module C13 (X : Empty). Module M := C12 X. End C13.
Module C14 (X : Empty). Module M := C13 X. End C14.
Module C15 (X : Empty). Module M := C14 X. End C15.
Module C16 (X : Empty). Module M := C15 X. End C16.
Module C17 (X : Empty). Module M := C16 X. End C17.
Module C18 (X : Empty). Module M := C17 X. End C18.
Module C19 (X : Empty). Module M := C18 X. End C19.
Module C20 (X : Empty). Module M := C19 X. End C20.
Module C21 (X : Empty). Module M := C20 X. End C21.
Module C22 (X : Empty). Module M := C21 X. End C22.
Module C23 (X : Empty). Module M := C22 X. End C23.
Module C24 (X : Empty). Module M := C23 X. End C24.
Module C25 (X : Empty). Module M := C24 X. End C25.
Module C26 (X : Empty). Module M := C25 X. End C26.
Module C27 (X : Empty). Module M := C26 X. End C27.
Module C28 (X : Empty). Module M := C27 X. End C28.
Module C29 (X : Empty). Module M := C28 X. End C29.
Module C30 (X : Empty). Module M := C29 X. End C30.
Module C31 (X : Empty). Module M := C30 X. End C31.
Module C32 (X : Empty). Module M := C31 X. End C32.
Module C33 (X : Empty). Module M := C32 X. End C33.
Module C34 (X : Empty). Module M := C33 X. End C34.
Module C35 (X : Empty). Module M := C34 X. End C35.
Module C36 (X : Empty). Module M := C35 X. End C36.
Module C37 (X : Empty). Module M := C36 X. End C37.
Module C38 (X : Empty). Module M := C37 X. End C38.
Module C39 (X : Empty). Module M := C38 X. End C39.
Module C40 (X : Empty). Module M := C39 X. End C40.
Module C41 (X : Empty). Module M := C40 X. End C41.
Module C42 (X : Empty). Module M := C41 X. End C42.
Module C43 (X : Empty). Module M := C42 X. End C43.
Module C44 (X : Empty). Module M := C43 X. End C44.
Module C45 (X : Empty). Module M := C44 X. End C45.
Module C46 (X : Empty). Module M := C45 X. End C46.
Module C47 (X : Empty). Module M := C46 X. End C47.
Module C48 (X : Empty). Module M := C47 X. End C48.
Module C49 (X : Empty). Module M := C48 X. End C49.
Module C50 (X : Empty). Module M := C49 X. End C50.
Module C51 (X : Empty). Module M := C50 X. End C51.
Module C52 (X : Empty). Module M := C51 X. End C52.
Module C53 (X : Empty). Module M := C52 X. End C53.
Module C54 (X : Empty). Module M := C53 X. End C54.
Module C55 (X : Empty). Module M := C54 X. End C55.
Module C56 (X : Empty). Module M := C55 X. End C56.
Module C57 (X : Empty). Module M := C56 X. End C57.
Module C58 (X : Empty). Module M := C57 X. End C58.
Module C59 (X : Empty). Module M := C58 X. End C59.
Module C60 (X : Empty). Module M := C59 X. End C60.
Module C61 (X : Empty). Module M := C60 X. End C61.
Module C62 (X : Empty). Module M := C61 X. End C62.
Module C63 (X : Empty). Module M := C62 X. End C63.
Module C64 (X : Empty). Module M := C63 X. End C64.
Module C65 (X : Empty). Module M := C64 X. End C65.
Module SDeep : UseT.
  Module App := C65 E.
  Definition helper : False := App.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.M.a.
  Definition use : False := helper.
End SDeep.
Definition boom_deep : False := SDeep.use.

theory Variables
  imports Main
begin
(* Variables - SLOTZERO *)
type_synonym Transactions = nat
type_synonym Hash = nat
type_synonym Party = nat

type_synonym Slot = nat
definition "(SlotZero::int) = 0"

type_synonym Delay = nat
type_synonym Parties = "Party list"

type_synonym InitParties = Parties


end
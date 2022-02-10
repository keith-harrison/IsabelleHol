theory Variables
  imports Main
begin
(* Variables - SLOTZERO *)
type_synonym Transactions = int
type_synonym Hash = int
type_synonym Party = int

type_synonym Slot = int
definition "(SlotZero::int) = 0"

type_synonym Delay = nat
type_synonym Parties = "Party list"

type_synonym InitParties = Parties


end
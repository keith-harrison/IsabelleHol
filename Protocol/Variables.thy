theory Variables
  imports Main
begin
(* Variables - SLOTZERO *)
datatype Transactions = Eqtype
datatype Hash = nat
datatype Party = finType

type_synonym Slot = nat
type_synonym SlotZero = nat

type_synonym Delay = nat
type_synonym Parties = "Party list"

datatype InitParties = Parties


end
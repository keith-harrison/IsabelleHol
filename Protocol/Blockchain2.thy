theory Blockchain2
  imports Main
begin
type_synonym Transactions = nat
type_synonym Party = nat 
type_synonym Slot = nat
datatype Hash = H nat nat
definition "Slotzero = 0"
type_synonym Delay = nat
type_synonym Parties = "Party list"
fun Winner :: "Party \<Rightarrow> Slot \<Rightarrow> bool" where
"Winner P S = (if P = S then True else False)"

record Block = 
  sl :: Slot
  txs :: Transactions
  pred :: Hash
  bid :: Party
type_synonym Chain = "Block list"
type_synonym Chains = "Chain list"
type_synonym BlockPool = "Block list"

fun HashCompare :: "Hash \<Rightarrow> Block \<Rightarrow> bool" where
"HashCompare (H a b) bl1 = (if((a = sl bl1) \<and> (b = bid bl1)) then True else False)"

fun HashB :: "Block \<Rightarrow> Block \<Rightarrow> bool" where
"HashB bl1 bl2 = HashCompare (pred bl2) bl1"

definition "GenBlock = \<lparr>sl = 0, txs = 0, pred = H 0 0 ,bid = 0\<rparr>"
definition "Block1 = \<lparr>sl = 1, txs =1, pred = H 0 0, bid = 1\<rparr>"

value "Hash B GenBlock Block1"

fun valid_blocks :: "Block \<Rightarrow> Block \<Rightarrow> bool" where
"valid_blocks b1 b2 = 
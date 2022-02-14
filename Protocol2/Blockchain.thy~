theory Blockchain
  imports Main
begin
type_synonym Transactions = nat
type_synonym Hash = nat
type_synonym Party = nat
type_synonym Slot = nat
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
definition HashB :: "Block \<Rightarrow> nat" where
"HashB bl = pred bl+1"
definition "GenBlock = \<lparr>sl = 0, txs = 0, pred = 0, bid = 0\<rparr>"
fun valid_blocks ::"Block \<Rightarrow> Block \<Rightarrow> bool" where
"valid_blocks b1 b2 =(if (Winner (sl b1) (bid b1) \<and> (HashB b2 = pred b1 ) \<and> (sl b2 < sl b1)) then True else False) "
value "valid_blocks \<lparr>sl=1,txs=1,pred=1,bid=1\<rparr> GenBlock"
value "a#b#[c,d]"
fun valid_chain :: "Chain \<Rightarrow> bool" where
"valid_chain [] = True"|
"valid_chain [b1] = (if b1 = GenBlock then True else False)"|
"valid_chain (b1#b2#c) = (if valid_blocks b1 b2 then valid_chain c else False) "
(*tree time*)



datatype T = Leaf | GenesisNode Block T T | Node Block T T   
fun allBlocks :: "T \<Rightarrow> BlockPool" where
"allBlocks (Node m l r) =[m]@ allBlocks l@allBlocks r "|
"allBlocks (GenesisNode m l r) = [m]@allBlocks l@allBlocks r " |
"allBlocks Leaf = []"

definition "tree0 = GenesisNode GenBlock Leaf Leaf"

fun extendTree :: "T \<Rightarrow> Block \<Rightarrow> T" where
"extendTree (GenesisNode Bl1 Leaf Leaf) Bl2 = (GenesisNode Bl1 (Node Bl2 Leaf Leaf) Leaf)"|
"extendTree (Node Bl1  Leaf) Bl2 = (GenesisNode Bl1 (Node Bl2 Leaf Leaf) Leaf)"
theory Block
  imports Variables
begin

(* Block *)
record Block =
  sl :: Slot
  txs :: Transactions
  pred :: Hash (*Hash*)
  bid :: Party

(* Type synononym for blocks change list to seq *)
type_synonym Chain = "Block list"
type_synonym Chains = "Chain list"
type_synonym BlockPool = "Block list"

(* Decidable equality for Blocks *)
definition eq_block :: "Block \<Rightarrow> Block \<Rightarrow> bool" where
"eq_block b1 b2 = (if ((sl b1  = sl b2)\<and>(txs b1 = txs b2)
\<and>(pred b1 = pred b2)\<and>(bid b1 = bid b2)) then True else False)"

lemma eq_blockP : " \<forall> b1. \<exists> b2. (eq_block b1 b2 = True) \<and> (b1 = b2)" 
  apply(auto)
  apply(simp add: eq_block_def)
  done


(* Parameters for Block *)
definition isGen :: "Block \<Rightarrow> bool" where
"isGen b =(if (pred b = 0) then True else False) "

value "isGen \<lparr> sl=0, txs = 1, pred =0, bid = 1 \<rparr>"

definition HashB :: "Block \<Rightarrow> int" where
"HashB bl = pred bl +1"




end
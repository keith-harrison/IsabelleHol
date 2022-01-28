theory Block
  imports Variables
begin

(* Block *)
record Block =
  sl :: int
  txs :: int
  pred :: nat (*Hash*)
  bid :: int

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
datatype GenesisBlock = Block

definition HashB :: "Block \<Rightarrow> nat" where
"HashB bl = pred bl +1"

(* Canonial structures for block *)
(*Math comp wut
canonical Block_eqMixin = Eval hnf in EqMixin eq_blockP.
canonical Block_eqType = Eval hnf in EqType Block Block_eqMixin. *)



end
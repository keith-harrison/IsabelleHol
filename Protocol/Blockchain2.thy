theory Blockchain2
  imports Main "HOL-Library.Tree"
begin
type_synonym Transactions = nat

type_synonym Party = nat
type_synonym Slot = nat

(*type_synonym Hash = "nat list"*)
datatype Hash = H nat nat
definition "Slotzero = 0"
type_synonym Delay = nat
type_synonym Parties = "Party list"
 
fun Winner :: "Party \<Rightarrow> Slot \<Rightarrow> bool" where
"Winner P S = (if P = S then True else False)"

(*"Hash option"*)
record Block =
  sl :: Slot
  txs :: Transactions
  pred :: Hash
  bid :: Party

type_synonym Chain = "Block list"
type_synonym Chains = "Chain list"
type_synonym BlockPool = "Block list"



fun HashCompare :: "Hash \<Rightarrow> Block \<Rightarrow> bool" where
"HashCompare (H a b) bl1 = (if ((a = sl bl1) \<and> (b = bid bl1)) then True else False)"

fun HashB :: "Block \<Rightarrow> Block \<Rightarrow> bool" where
"HashB bl1 bl2 = HashCompare (pred bl2) bl1"

definition "GenBlock = \<lparr>sl = 0, txs = 0, pred = H 0 0 ,bid = 0\<rparr>"
definition "Block1 = \<lparr>sl = 1, txs =1, pred = H 0 0, bid = 1\<rparr>"

value "HashB GenBlock Block1"

fun valid_blocks ::"Block \<Rightarrow> Block \<Rightarrow> bool" where
"valid_blocks b1 b2 =  (HashB b2 b1 \<and> (sl b2 < sl b1)) "

value "valid_blocks Block1 GenBlock"
value "a#b#[c,d]"

(*checking for b's being a node only and a /genesis node at the end of the list missing*)
fun valid_chain :: "Chain \<Rightarrow> bool" where
"valid_chain [] = False"|
"valid_chain [b1] = (if b1 = GenBlock then True else False)"|
"valid_chain (b1#b2#c) = (if valid_blocks b1 b2 \<and> (b1 \<noteq> GenBlock) then valid_chain (b2#c) else False)"


value "valid_chain [\<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr>, \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr>, \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr>]"
value "HashB  \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr> \<lparr>sl = 2, txs = 1, pred = H 1 1, bid = 2\<rparr>"


 
datatype T = Leaf | Node Block T T 

fun allBlocks :: "T \<Rightarrow> BlockPool" where
"allBlocks (Node m l r) = allBlocks l@allBlocks r @[m]"|
"allBlocks Leaf = []"

fun allBlocksGen :: "T \<Rightarrow> BlockPool" where
"allBlocksGen (Node m l r) = (if m = GenBlock then allBlocks l@allBlocks r @[m] else [])"|
"allBlocksGen Leaf = []"

fun allBlocksAppend :: "Block \<Rightarrow>BlockPool list\<Rightarrow> BlockPool list" where
"allBlocksAppend Bl BlP = (map (\<lambda> bl. bl @ [Bl]) BlP)"

fun allBlocks' :: "T \<Rightarrow> BlockPool list" where
"allBlocks' (Node m l r) = allBlocksAppend m (allBlocks' l) @allBlocksAppend m (allBlocks' r)"|
"allBlocks' Leaf = [[]]"

fun allBlocksGen' :: "T \<Rightarrow> BlockPool list" where
"allBlocksGen' (Node m l r) =  (if m = GenBlock then allBlocksAppend m (allBlocks' l) @allBlocksAppend m (allBlocks' r) else [[]])"|
"allBlocksGen' Leaf = [[]]"

definition "tree0 = Node GenBlock Leaf Leaf"

lemma initialTree : "allBlocksGen tree0 = [GenBlock]" 
  by (simp add: GenBlock_def tree0_def)


fun extendTree :: "T \<Rightarrow> Block \<Rightarrow> T" where
"extendTree (Node Bl1 Leaf Leaf) Bl2 =  (if valid_blocks Bl2 Bl1 then (Node Bl1 (Node Bl2 Leaf Leaf) Leaf) else (Node Bl1 Leaf Leaf)) "|
"extendTree (Node Bl1 t1 Leaf) Bl2 =  (if valid_blocks Bl2 Bl1 then (Node Bl1 t1 (Node Bl2 Leaf Leaf)) else (Node Bl1 (extendTree t1 Bl2) Leaf))"|
"extendTree (Node Bl1 Leaf t1) Bl2 =  (if valid_blocks Bl2 Bl1 then (Node Bl1 (Node Bl2 Leaf Leaf) t1) else (Node Bl1  Leaf (extendTree t1 Bl2)))"|
"extendTree (Node Bl1 t1 t2) Bl2 =(Node Bl1 (extendTree t1 Bl2) (extendTree t2 Bl2))"|
"extendTree Leaf Bl2 = Leaf"
(*valid_chain ([Bl2]#Bl1) <- will also check for gen node only use in extendTreeGen*)
value "a#[b]"
fun extendTreeGen :: "T \<Rightarrow> Block \<Rightarrow> T" where
"extendTreeGen (Node Bl1 Leaf Leaf) Bl2 = (if (valid_chain (Bl1#[Bl2])) then (Node Bl1 (Node Bl2 Leaf Leaf) Leaf) else (Node Bl1 Leaf Leaf)) "|
"extendTreeGen (Node Bl1 t1 Leaf) Bl2 =  (if (valid_chain (Bl1#[Bl2])) then (Node Bl1 t1 (Node Bl2 Leaf Leaf)) else (Node Bl1 (extendTree t1 Bl2) Leaf))"|
"extendTreeGen (Node Bl1 Leaf t1) Bl2 =  (if (valid_chain (Bl1#[Bl2]))then (Node Bl1 (Node Bl2 Leaf Leaf) t1) else (Node Bl1  Leaf (extendTree t1 Bl2)))"|
"extendTreeGen (Node Bl1 t1 t2) Bl2 = (Node Bl1 (extendTree t1 Bl2) (extendTree t2 Bl2))"|
"extendTreeGen Leaf Bl2 = Leaf"

lemma "extendTree Leaf B = Leaf"
  by simp

lemma AllExtend : assumes "extendTreeGen t b \<noteq> t" shows "set (allBlocksGen (extendTreeGen t b)) =set ([b]@ allBlocksGen t)"
proof(cases "t")
  case Leaf
  then show ?thesis
    using assms by auto
next
  case (Node x1 x2 x3)
  then show ?thesis proof(cases "x2")
    case Leaf
    then show ?thesis try
  next
    case (Node x21 x22 x23)
    then show ?thesis sorry
  qed
qed

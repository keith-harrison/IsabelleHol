theory Blockchain
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

(*Hash option \<rightarrow> None*)
definition "GenBlock = \<lparr>sl = 0, txs = 0, pred = H 0 0 ,bid = 0\<rparr>"
definition "Block1 = \<lparr>sl = 1, txs =1, pred = H 0 0, bid = 1\<rparr>"

value "HashB GenBlock Block1"

fun valid_blocks ::"Block \<Rightarrow> Block \<Rightarrow> bool" where
"valid_blocks b1 b2 = (Winner (sl b1) (bid b1) \<and> HashB b2 b1 \<and> (sl b2 < sl b1)) "

value "valid_blocks Block1 GenBlock"
value "a#b#[c,d]"

fun valid_chain :: "Chain \<Rightarrow> bool" where
"valid_chain [] = True"|
"valid_chain [b1] = (if b1 = GenBlock then True else False)"|
"valid_chain (b1#b2#c) = (if valid_blocks b1 b2 then valid_chain c else False) "
value "valid_chain [\<lparr>sl = 2, txs = 1, pred = H 1 1, bid = 2\<rparr>, \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr>, \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr>]"
value "HashB  \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr> \<lparr>sl = 2, txs = 1, pred = H 1 1, bid = 2\<rparr>"
(*tree time*)
datatype T = Leaf | GenesisNode Block T T | Node Block T T   

fun allBlocks :: "T \<Rightarrow> BlockPool" where
"allBlocks (Node m l r) = allBlocks l@allBlocks r @[m]"|
"allBlocks (GenesisNode m l r) = allBlocks l@allBlocks r @[m] " |
"allBlocks Leaf = []"
(* want list of lists*)
fun allBlocksAppend :: "Block \<Rightarrow>BlockPool list\<Rightarrow> BlockPool list" where
"allBlocksAppend Bl BlP = (map (\<lambda> bl. bl @ [Bl]) BlP)"

fun allBlocks' :: "T \<Rightarrow> BlockPool list" where
"allBlocks' (Node m l r) = allBlocksAppend m (allBlocks' l) @allBlocksAppend m (allBlocks' r)"|
"allBlocks' (GenesisNode m l r) = allBlocksAppend m (allBlocks' l) @allBlocksAppend m (allBlocks' r)"|
"allBlocks' Leaf = [[]]"

definition "tree0 = GenesisNode GenBlock Leaf Leaf"

lemma initialTree : "allBlocks tree0 = [GenBlock]" 
  by (simp add: GenBlock_def tree0_def)


fun extendTree :: "T \<Rightarrow> Block \<Rightarrow> T" where
"extendTree (GenesisNode Bl1 Leaf Leaf) Bl2 = (if (HashB Bl1 Bl2) then (GenesisNode Bl1 (Node Bl2 Leaf Leaf) Leaf) else (GenesisNode Bl1 Leaf Leaf)) "|
"extendTree (Node Bl1 Leaf Leaf) Bl2 =  (if HashB Bl1 Bl2 then (Node Bl1 (Node Bl2 Leaf Leaf) Leaf) else (Node Bl1 Leaf Leaf)) "|
"extendTree (GenesisNode Bl1 t1 Leaf) Bl2 =  (if HashB Bl1 Bl2  then (GenesisNode Bl1 t1 (Node Bl2 Leaf Leaf)) else (GenesisNode Bl1 (extendTree t1 Bl2) Leaf))"|
"extendTree (Node Bl1 t1 Leaf) Bl2 =  (if HashB Bl1 Bl2 then (Node Bl1 t1 (Node Bl2 Leaf Leaf)) else (Node Bl1 (extendTree t1 Bl2) Leaf))"|
"extendTree (GenesisNode Bl1 t1 t2) Bl2 = (GenesisNode Bl1 (extendTree t1 Bl2) (extendTree t2 Bl2))"|
"extendTree (Node Bl1 t1 t2) Bl2 =(Node Bl1 (extendTree t1 Bl2) (extendTree t2 Bl2))"|
"extendTree Leaf Bl2 = Leaf"
 
lemma "extendTree Leaf B = Leaf" 
  by simp

lemma AllExtend : "extendTree t b \<noteq> t \<Longrightarrow> set (allBlocks (extendTree t b)) =set ([b]@ allBlocks t)"
proof(induction t)
  case Leaf
  then show ?case by simp
next
  case (GenesisNode x1 t1 t2) note ABC=this
  then show ?case proof (cases "t1") 
    case Leaf note t1Leaf=this
    then show ?thesis proof (cases "t2")
      case Leaf
      then show ?thesis using ABC t1Leaf
        by auto   
    next
      case (GenesisNode x21 x22 x23)
      then show ?thesis using ABC t1Leaf
        by auto
    next
      case (Node x31 x32 x33)
      then show ?thesis using ABC t1Leaf
        by auto
    qed
  next
    case (GenesisNode x21 x22 x23) note GenNode1=this
    then show ?thesis proof(cases "t2")
      case Leaf
      then show ?thesis using ABC GenNode1 
        by auto
    next
      case (GenesisNode x21 x22 x23)
      then show ?thesis using ABC GenNode1 
        by fastforce
    next
      case (Node x31 x32 x33)
      then show ?thesis using ABC GenNode1 
        by fastforce
    qed
  next
    case (Node x31 x32 x33) note Node1=this
    then show ?thesis proof(cases "t2" )
      case Leaf
      then show ?thesis using ABC Node1 by auto
    next
      case (GenesisNode x21 x22 x23)
      then show ?thesis using ABC Node1 by fastforce
    next
      case (Node x31 x32 x33)
      then show ?thesis using ABC Node1 by fastforce
    qed 
  qed 
next
  case (Node x1 t1 t2) note NodeA = this
  then show ?case proof(cases "t1")
    case Leaf note t2Leaf=this
    then show ?thesis proof(cases "t2")
      case Leaf
      then show ?thesis using NodeA t2Leaf
        by auto
    next
      case (GenesisNode x21 x22 x23)
      then show ?thesis  using NodeA t2Leaf
        by auto
    next
      case (Node x31 x32 x33)
      then show ?thesis  using NodeA t2Leaf
        by auto
    qed
  next
    case (GenesisNode x21 x22 x23) note t2GenNodeA = this
    then show ?thesis proof(cases "t2")
      case Leaf
      then show ?thesis using NodeA t2GenNodeA
        by auto
    next
      case (GenesisNode x21 x22 x23)
      then show ?thesis  using NodeA t2GenNodeA  by fastforce
    next
      case (Node x31 x32 x33)
      then show ?thesis using NodeA t2GenNodeA  by fastforce
    qed
  next
    case (Node x31 x32 x33) note t2NodeA = this
    then show ?thesis proof(cases "t2")
      case Leaf
      then show ?thesis using NodeA t2NodeA by auto
    next
      case (GenesisNode x21 x22 x23)
      then show ?thesis using NodeA t2NodeA 
        by fastforce
    next
      case (Node x31 x32 x33)
      then show ?thesis using NodeA t2NodeA by fastforce
    qed
  qed 
qed

(*Only extends if the parents block [sl,bid] is equal to childs pred list *)
value "extendTree (GenesisNode GenBlock Leaf Leaf) Block1 "
value "extendTree (GenesisNode GenBlock (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr> Leaf Leaf) (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 2\<rparr> Leaf Leaf)) \<lparr>sl = 0, txs = 0, pred =H 1 2, bid = 1\<rparr> "
value "extendTree (GenesisNode GenBlock (Node Block1 Leaf Leaf) Leaf) \<lparr>sl = 1, txs = 1, pred = H 1 2, bid = 1\<rparr> "
value "extendTree (GenesisNode GenBlock Leaf Leaf) Block1 "

fun returnsl :: "T \<Rightarrow> Slot \<Rightarrow> bool" where
"returnsl Leaf slot = False"|
"returnsl (GenesisNode Bl1 l r) slot = ((sl Bl1) \<le> slot)"|
"returnsl (Node Bl1 l r) slot = ((sl Bl1) \<le> slot)"

fun best_c :: "nat \<Rightarrow> Block list list \<Rightarrow> (Block list \<times> nat \<times> bool) option"where 
"best_c slot list = (let list' = map (\<lambda> l. (l,sl (hd l), valid_chain l)) list in find (\<lambda> (c,s,v).v\<and>(s\<le>slot)) list')"

definition get_first :: \<open>(Block list \<times> nat \<times> bool) option \<Rightarrow>Block list\<close> where
\<open>get_first a = (case a of None \<Rightarrow> [] | Some a \<Rightarrow> fst a)\<close>
(*need to access the tuple part*)
fun best_chain :: "Slot \<Rightarrow> T \<Rightarrow> Block list" where
"best_chain slot T = get_first ( best_c slot (allBlocks' T))"

value "best_c (3::nat) (allBlocks' ((GenesisNode GenBlock (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr>  Leaf Leaf)
 (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 2\<rparr> Leaf Leaf))))"

value "allBlocks' ((GenesisNode GenBlock (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr> (Node \<lparr>sl = 1, txs = 1, pred = H 1 1, bid = 1\<rparr> Leaf Leaf) Leaf)
 (Node \<lparr>sl = 1, txs = 1, pred = H 1 1, bid = 1\<rparr> Leaf Leaf)))"

value "best_chain 3 (GenesisNode GenBlock (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr> (Node \<lparr>sl = 1, txs = 1, pred = H 1 1, bid = 1\<rparr> (Node \<lparr>sl = 2, txs = 2, pred = H 1 1, bid = 2\<rparr> Leaf Leaf) Leaf) Leaf)
 (Node \<lparr>sl = 1, txs = 1, pred = H 1 1, bid = 1\<rparr> Leaf Leaf))"
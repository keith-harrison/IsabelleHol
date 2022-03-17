theory BlockchainNew
  imports Main "HOL-Library.Tree"
begin

datatype Hash = H nat nat 
record Block =
  sl :: nat
  txs :: nat
  pred :: Hash
  bid :: nat

type_synonym Chain = "Block list"
type_synonym Chains = "Chain list"
type_synonym BlockPool = "Block list"

fun Winner :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
"Winner P S = (if P = S then True else False)"

fun HashCompare :: "Hash \<Rightarrow> Block \<Rightarrow> bool" where
"HashCompare (H a b) bl1 = (if ((a = sl bl1) \<and> (b = bid bl1)) then True else False)"

fun HashB :: "Block \<Rightarrow> Block \<Rightarrow> bool" where
"HashB bl1 bl2 = HashCompare (pred bl2) bl1"


definition "GenBlock = \<lparr>sl = 0, txs = 0, pred = H 0 0 ,bid = 0\<rparr>"
definition "Block1 = \<lparr>sl = 1, txs =1, pred = H 0 0, bid = 1\<rparr>"

value "HashB GenBlock Block1"

fun valid_blocks ::"Block \<Rightarrow> Block \<Rightarrow> bool" where
"valid_blocks b1 b2 = (Winner (sl b1) (bid b1) \<and> HashB b2 b1 \<and> (sl b2 < sl b1)) "
value "valid_blocks Block1 GenBlock"
fun valid_chain :: "Chain \<Rightarrow> bool" where
"valid_chain [] = False"|
"valid_chain [b1] = (if b1 = GenBlock then True else False)"|
"valid_chain (b1#b2#c) = (if b1 \<noteq> b2\<and> valid_blocks b1 b2 \<and> (b1 \<noteq> GenBlock) then valid_chain (b2#c) else False)"

datatype T = Leaf | GenesisNode Block T T | Node Block T T   
fun allBlocks2 :: "T \<Rightarrow> BlockPool" where
"allBlocks2 (Node m l r) = allBlocks2 l@allBlocks2 r @[m]"|
"allBlocks2 (GenesisNode m l r) = [] " |
"allBlocks2 Leaf = []"
fun allBlocks :: "T \<Rightarrow> BlockPool" where
"allBlocks (Node m l r) = []"|
"allBlocks (GenesisNode m l r) = allBlocks2 l@allBlocks2 r @[m] " |
"allBlocks Leaf = []"


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
"extendTree (GenesisNode Bl1 Leaf Leaf) Bl2 = (if (valid_blocks Bl2 Bl1) then (GenesisNode Bl1 (Node Bl2 Leaf Leaf) Leaf) else (GenesisNode Bl1 Leaf Leaf)) "|
"extendTree (Node Bl1 Leaf Leaf) Bl2 =  (if valid_blocks Bl2 Bl1 then (Node Bl1 (Node Bl2 Leaf Leaf) Leaf) else (Node Bl1 Leaf Leaf)) "|
"extendTree (GenesisNode Bl1 t1 Leaf) Bl2 =  (if valid_blocks Bl2 Bl1  then (GenesisNode Bl1 t1 (Node Bl2 Leaf Leaf)) else (GenesisNode Bl1 (extendTree t1 Bl2) Leaf))"|
"extendTree (Node Bl1 t1 Leaf) Bl2 =  (if valid_blocks Bl2 Bl1 then (Node Bl1 t1 (Node Bl2 Leaf Leaf)) else (Node Bl1 (extendTree t1 Bl2) Leaf))"|
"extendTree (GenesisNode Bl1 t1 t2) Bl2 = (GenesisNode Bl1 (extendTree t1 Bl2) (extendTree t2 Bl2))"|
"extendTree (Node Bl1 t1 t2) Bl2 =(Node Bl1 (extendTree t1 Bl2) (extendTree t2 Bl2))"|
"extendTree Leaf Bl2 = Leaf"

definition valid_t where
"valid_t t = (\<forall>c\<in>set(allBlocks' t).valid_chain c)"
value "valid_t (GenesisNode \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr> T.Leaf
       (GenesisNode \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr> T.Leaf T.Leaf))"
lemma "extendTree Leaf B = Leaf" 
  by simp
value "extendTree (GenesisNode GenBlock Leaf Leaf) \<lparr>sl = 1, txs = 0, pred = H 0 0, bid = 1\<rparr>"
fun root2 :: "T \<Rightarrow> bool" where
"root2 Leaf = True"|
"root2 (Node Bl l r) = (if Bl \<noteq> GenBlock then True \<and> root2 l \<and> root2 r  else False)"|
"root2 (GenesisNode _ _ _) = False"

fun root :: "T \<Rightarrow> bool" where
"root (GenesisNode Bl l r) = (if Bl = GenBlock then True \<and> root2 l  \<and> root2 r else False)"|
"root (Node _ _ _) = False"|
"root Leaf = False"

lemma AllExtend : "extendTree   t b \<noteq> t \<and> (valid_t t) \<and> root t \<Longrightarrow> set (allBlocks (extendTree t b)) =set ([b]@ allBlocks t)"
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
        by (metis root.simps(1) root2.simps(3))
    next
      case (Node x31 x32 x33)
      then show ?thesis using ABC t1Leaf
        try
    qed
  next
    case (GenesisNode x21 x22 x23) note GenNode1=this
    then show ?thesis proof(cases "t2")
      case Leaf
      then show ?thesis using ABC GenNode1 
        by (metis root.simps(1) root2.simps(3))
    next
      case (GenesisNode x21 x22 x23)
      then show ?thesis using ABC GenNode1 
        try
    next
      case (Node x31 x32 x33)
      then show ?thesis using ABC GenNode1 
        try
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



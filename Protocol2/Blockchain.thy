theory Blockchain
  imports Main "HOL-Library.Tree"
begin
type_synonym Transactions = nat

type_synonym Party = nat
type_synonym Slot = nat
(*datatype Hash = H nat nat"*)
type_synonym Hash = "nat list"
definition "Slotzero = 0"
type_synonym Delay = nat
type_synonym Parties = "Party list"
 
(*make a list of values in a list pick one at a time list of length n parties - currently n limited as n = 2 due to being a binary tree.*)
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
(*
value "hd [bid,b]"
value "tl [bid,b]"*)
(*
definition getHashing :: "Block \<Rightarrow> Hash" where
"getHashing \<lparr>sl=_,txs=_,pred=Hashing a b,bid=_\<rparr> = Hashing a b"*)
definition HashB :: "Block \<Rightarrow> Block \<Rightarrow> bool" where
"HashB bl1 bl2 = ((hd (pred bl2) =sl bl1) \<and> (hd (tl (pred bl2)) = bid bl1))"


(*maybe values from haskell*)
definition "GenBlock = \<lparr>sl = 0, txs = 0, pred = [],bid = 0\<rparr>"
definition "Block1 = \<lparr>sl = 1, txs =1, pred = [0,0], bid = 1\<rparr>"
(*
definition "GenBlock = \<lparr>sl = 0, txs = 0, pred = Hashing 100 100,bid = 0\<rparr>"
definition "Block1 = \<lparr>sl = 1, txs =1, pred = Hashing 0 0, bid = 1\<rparr>"
*)
value "HashB GenBlock Block1"
fun valid_blocks ::"Block \<Rightarrow> Block \<Rightarrow> bool" where
"valid_blocks b1 b2 = (Winner (sl b1) (bid b1) \<and> HashB b2 b1 \<and> (sl b2 < sl b1)) "
value "valid_blocks Block1 GenBlock"
value "a#b#[c,d]"
fun valid_chain :: "Chain \<Rightarrow> bool" where
"valid_chain [] = True"|
"valid_chain [b1] = (if b1 = GenBlock then True else False)"|
"valid_chain (b1#b2#c) = (if valid_blocks b1 b2 then valid_chain c else False) "
(*tree time*)
datatype T = Leaf | GenesisNode Block T T | Node Block T T   
fun allBlocks :: "T \<Rightarrow> BlockPool" where
"allBlocks (Node m l r) = allBlocks l@allBlocks r @[m]"|
"allBlocks (GenesisNode m l r) = allBlocks l@allBlocks r @[m] " |
"allBlocks Leaf = []"

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

(*need to fix these counter examples \<rightarrow> probably by making pred field a datatype having two be two nats *)
 
lemma "extendTree Leaf B = Leaf" apply(simp) done

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
    then show ?thesis proof(cases "") sorry
  qed sorry
next
  case (Node x1 t1 t2)
  then show ?case sorry
qed
  done
  
(*Only extends if the parents block [sl,bid] is equal to childs pred list *)
value "extendTree (GenesisNode GenBlock Leaf Leaf) Block1 "
value "extendTree (GenesisNode GenBlock (Node \<lparr>sl = 1, txs = 1, pred = [0,0], bid = 1\<rparr> Leaf Leaf) (Node \<lparr>sl = 1, txs = 1, pred = [0,0], bid = 2\<rparr> Leaf Leaf)) \<lparr>sl = 0, txs = 0, pred = [1,2], bid = 1\<rparr> "
value "extendTree (GenesisNode GenBlock (Node Block1 Leaf Leaf) Leaf) \<lparr>sl = 1, txs = 1, pred = [1,2], bid = 1\<rparr> "
value "extendTree (GenesisNode GenBlock Leaf Leaf) Block1 "



fun returnsl :: "T \<Rightarrow> Slot \<Rightarrow> bool" where
"returnsl (GenesisNode Bl1 l r) slot = ((sl Bl1) \<le> slot)"|
"returnsl (Node Bl1 l r) slot = ((sl Bl1) \<le> slot)"

fun bestChain :: "Slot \<Rightarrow> T \<Rightarrow> Chain" where
"bestChain slot (GenesisNode Bl1 Leaf Leaf) = [Bl1]"|
"bestChain slot (Node Bl1 Leaf Leaf) = [Bl1]"|
"bestChain slot (GenesisNode Bl1 t1 Leaf) = (if (returnsl t1 slot) then (bestChain slot t1 @[Bl1]) else [Bl1])"|
"bestChain slot (Node Bl1 t1 Leaf) = (if (returnsl t1 slot) then (bestChain slot t1 @[Bl1]) else [Bl1])"




(*
"bestChain slot (GenesisNode Bl1 t1 t2) = "|
"bestChain slot (Node Bl1 t1 t2) =  (if sl Bl1 = slot then (bestChain slot t1)@[Bl1] else (if sl Bl = slot then (bestChain slot t2)@[Bl1] else []))""
 (if sl Bl1 = slot then [Bl1] else [])
*)
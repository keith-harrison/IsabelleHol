theory BlockchainNew
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
"valid_blocks b1 b2 = (HashB b2 b1 \<and> (sl b2 \<le> sl b1)) "


value "valid_blocks Block1 GenBlock"
value "a#b#[c,d]"

(*checking for b's being a node only and a /genesis node at the end of the list missing*)
fun valid_chain :: "Chain \<Rightarrow> bool" where
"valid_chain [] = True"|
"valid_chain [b1] = (if b1 = GenBlock then True else False)"|
"valid_chain (b1#b2#c) = (if valid_blocks b1 b2 \<and> (b1 \<noteq> GenBlock) then valid_chain (b2#c) else False)"


value "valid_chain [\<lparr>sl = 2, txs = 2, pred = H 1 1, bid = 2\<rparr>, \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr>, \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr>]"
value "HashB  \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr> \<lparr>sl = 2, txs = 1, pred = H 1 1, bid = 2\<rparr>"

datatype T = Leaf | Node Block T T 
datatype GenT = GenesisNode Block T T

fun allBlocks :: "T \<Rightarrow> BlockPool" where
"allBlocks (Node m l r) = allBlocks l@allBlocks r @[m]"|
"allBlocks Leaf = []"

fun allBlocksGen :: "GenT \<Rightarrow> BlockPool" where
"allBlocksGen (GenesisNode m l r) = (allBlocks l)@(allBlocks r)@[m] "

fun allBlocksAppend :: "Block \<Rightarrow>BlockPool list\<Rightarrow> BlockPool list" where
"allBlocksAppend Bl BlP = (map (\<lambda> bl. bl @ [Bl]) BlP)"

fun allBlocks2 :: "T \<Rightarrow> BlockPool list" where
"allBlocks2 (Node m l r) = allBlocksAppend m (allBlocks2 l) @allBlocksAppend m (allBlocks2 r)"|
"allBlocks2 Leaf = [[]]"

fun allBlocks' :: "GenT \<Rightarrow> BlockPool list" where
"allBlocks' (GenesisNode m l r) = allBlocksAppend m (allBlocks2 l) @allBlocksAppend m (allBlocks2 r)"



definition "tree0 = GenesisNode GenBlock Leaf Leaf"
definition "exampleTree = (GenesisNode GenBlock (Node Block1 Leaf Leaf) (Node Block1 Leaf Leaf))"
lemma initialTree : "allBlocksGen tree0 = [GenBlock]" 
  by (simp add: GenBlock_def tree0_def)
value "set(allBlocksGen exampleTree) = {\<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr>,
  \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr>}"
value "allBlocks' exampleTree"


fun extendTree :: "T \<Rightarrow> Block \<Rightarrow> T" where
"extendTree (Node Bl1 Leaf Leaf) Bl2 =  (if valid_blocks Bl2 Bl1 then (Node Bl1 (Node Bl2 Leaf Leaf) Leaf) else (Node Bl1 Leaf Leaf)) "|
"extendTree (Node Bl1 t1 Leaf) Bl2 =  (if valid_blocks Bl2 Bl1 then (Node Bl1 t1 (Node Bl2 Leaf Leaf)) else (Node Bl1 (extendTree t1 Bl2) Leaf))"|
"extendTree (Node Bl1 Leaf t1) Bl2 =  (if valid_blocks Bl2 Bl1 then (Node Bl1 (Node Bl2 Leaf Leaf) t1) else (Node Bl1  Leaf (extendTree t1 Bl2)))"|
"extendTree (Node Bl1 t1 t2) Bl2 =(Node Bl1 (extendTree t1 Bl2) (extendTree t2 Bl2))"|
"extendTree Leaf Bl2 = Leaf"

fun extendTreeGen :: "GenT \<Rightarrow> Block \<Rightarrow> GenT" where
"extendTreeGen (GenesisNode Bl1 Leaf Leaf) Bl2 = (if (valid_blocks Bl2 Bl1) then (GenesisNode Bl1 (Node Bl2 Leaf Leaf) Leaf) else (GenesisNode Bl1 Leaf Leaf)) "|
"extendTreeGen (GenesisNode Bl1 t1 Leaf) Bl2 =  (if valid_blocks Bl2 Bl1  then (GenesisNode Bl1 t1 (Node Bl2 Leaf Leaf)) else (GenesisNode Bl1 (extendTree t1 Bl2) Leaf))"|
"extendTreeGen (GenesisNode Bl1 Leaf t1) Bl2 =  (if valid_blocks Bl2 Bl1 then (GenesisNode Bl1 (Node Bl2 Leaf Leaf) t1) else (GenesisNode Bl1  Leaf (extendTree t1 Bl2)))"|
"extendTreeGen (GenesisNode Bl1 t1 t2) Bl2 = (GenesisNode Bl1 (extendTree t1 Bl2) (extendTree t2 Bl2))"

lemma "extendTree Leaf B = Leaf"
  by simp

definition valid_t where
"valid_t t = (\<forall>c\<in>set(allBlocks' t).valid_chain c)"

lemma AllExtend : "extendTreeGen t b \<noteq> t  \<Longrightarrow> set (allBlocksGen (extendTreeGen t b)) =set ([b]@ allBlocksGen t)"
proof(induction t)
  case (GenesisNode x1a x2a x3a) note Gen = this
  then show ?case proof (cases "x2a")
    case Leaf note x2aLeaf = this
    then show ?thesis proof (cases "x3a")
      case Leaf
      then show ?thesis using Gen x2aLeaf 
        by auto
    next
      case (Node x21 x22 x23)
      then show ?thesis using Gen x2aLeaf by auto
    qed
  next
    case (Node x21 x22 x23) note x2aNode = this
    then show ?thesis proof (cases "x3a")
      case Leaf
      then show ?thesis using Gen x2aNode sorry
    next
      case (Node x21 x22 x23)
      then show ?thesis using Gen x2aNode sorry
    qed
  qed
qed


value "extendTreeGen (GenesisNode GenBlock Leaf Leaf) Block1 "
value "extendTreeGen (GenesisNode GenBlock (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr> Leaf Leaf) (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 2\<rparr> Leaf Leaf)) \<lparr>sl = 0, txs = 0, pred =H 1 2, bid = 1\<rparr> "
value "extendTreeGen (GenesisNode GenBlock (Node Block1 Leaf Leaf) Leaf) \<lparr>sl = 1, txs = 1, pred = H 1 2, bid = 1\<rparr> "
value "extendTreeGen (GenesisNode GenBlock Leaf Leaf) Block1 "

fun best_c :: "nat \<Rightarrow> Block list list \<Rightarrow> (Block list \<times> nat \<times> bool) option"where 
"best_c slot list = (let list' = map (\<lambda> l. (l,sl (hd l), valid_chain l)) list in find (\<lambda> (c,s,v).v\<and>(s\<le>slot)) list')"

definition get_first :: \<open>(Block list \<times> nat \<times> bool) option \<Rightarrow>Block list\<close> where
\<open>get_first a = (case a of None \<Rightarrow> [] | Some a \<Rightarrow> fst a)\<close>

lemma best_c_none : "best_c n [] = None"
  by(simp)

lemma find_in : \<open>find p ls = Some l\<Longrightarrow> l\<in> set(ls)\<close>
proof(induction ls)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  then show ?case
    by (metis find_Some_iff nth_mem)
qed

lemma best_c_in : "best_c n bl \<noteq> None \<Longrightarrow>  get_first(best_c n bl) \<in> set(bl)"
  apply(simp add:get_first_def find_in)
proof(induction bl)
  case Nil
  then show ?case
    by simp 
next
  case (Cons a bl)
  then show ?case
    by auto
qed

fun best_chain :: "Slot \<Rightarrow> GenT \<Rightarrow> Block list" where
"best_chain 0 (GenesisNode x _ _) = (if x = GenBlock then [GenBlock]else [])"|
"best_chain s T = get_first ( best_c s (allBlocks' T))"

value "best_c (3::nat) (allBlocks' ((GenesisNode GenBlock (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr>  Leaf Leaf)
 (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 2\<rparr> Leaf Leaf))))"
value "allBlocks' ((GenesisNode GenBlock (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr> (Node \<lparr>sl = 1, txs = 1, pred = H 1 1, bid = 1\<rparr> Leaf Leaf) Leaf)
 (Node \<lparr>sl = 1, txs = 1, pred = H 1 1, bid = 1\<rparr> Leaf Leaf)))"

value "valid_chain (best_chain 2 (GenesisNode GenBlock (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr> (Node \<lparr>sl = 1, txs = 1, pred = H 1 1, bid = 1\<rparr> (Node \<lparr>sl = 2, txs = 2, pred = H 1 1, bid = 2\<rparr> Leaf Leaf) Leaf) Leaf)
 (Node \<lparr>sl = 1, txs = 1, pred = H 1 1, bid = 1\<rparr> Leaf Leaf)))"

value "best_chain 1 (GenesisNode \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 1\<rparr> Leaf Leaf)"
value "allBlocks'  (GenesisNode \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 1\<rparr> Leaf Leaf)"

lemma best_valid :"\<forall>s. valid_t t \<and> (allBlocks' t \<noteq>[[]]) \<Longrightarrow> valid_chain (best_chain s t)"
  proof(induction t)
    case (GenesisNode x1a x2a x3a) note Gen = this
    then show ?case proof (cases "x2a")
      case Leaf note Leafa = this
      then show ?thesis proof (cases "x3a")
        case Leaf
        then show ?thesis using Leafa Gen try
      next
        case (Node x21 x22 x23)
        then show ?thesis using Leafa Gen
      qed
    next
      case (Node x21 x22 x23)
      then show ?thesis proof (cases "x3a")
        case Leaf
        then show ?thesis sorry
      next
        case (Node x21 x22 x23)
        then show ?thesis sorry
      qed
    qed
  qed

  

theory Blockchain
  imports Main "HOL-Library.Tree"
begin

(* -- TYPES / Hash / Block Datatype / BlockTree Datatype --*)
type_synonym Transactions = int
type_synonym Party = int
type_synonym Slot = int
datatype Hash = H int int
definition "Slotzero = 0"
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





definition "GenBlock = \<lparr>sl = 0, txs = 0, pred = H 0 0 ,bid = 0\<rparr>"
definition "Block1 = \<lparr>sl = 1, txs =1, pred = H 0 0, bid = 1\<rparr>"
definition "Block2 = \<lparr> sl = 2, txs = 0, pred = H 1 1, bid = 1\<rparr>"
definition "Block3 = \<lparr> sl = 3, txs = 0, pred = H 2 1, bid = 1\<rparr>"


datatype T = Leaf | Node Block T T 

definition "tree0 = Node GenBlock Leaf Leaf"

(*-- Functions for valid_chain --*)
fun HashCompare' :: "Hash \<Rightarrow> Block \<Rightarrow> bool" where
"HashCompare' (H a b) bl1 = ((a = sl bl1) \<and> (b = bid bl1))"

fun HashCompare :: "Block \<Rightarrow> Block \<Rightarrow> bool" where
"HashCompare bl1 bl2 = HashCompare' (pred bl2) bl1"

fun valid_blocks ::"Block \<Rightarrow> Block \<Rightarrow> bool" where
"valid_blocks b1 b2 =  (HashCompare b2 b1 \<and> (sl b2 < sl b1)) "

fun valid_chain :: "Chain \<Rightarrow> bool" where
"valid_chain [] = False"|
"valid_chain [b1] = (if b1 = GenBlock then True else False)"|
"valid_chain (b1#b2#c) = (if valid_blocks b1 b2 \<and> (b1 \<noteq> GenBlock) then valid_chain (b2#c) else False)"

fun valid_chain_weak :: "Chain \<Rightarrow> bool" where 
"valid_chain_weak [] = False"|
"valid_chain_weak [b1] = True"|
"valid_chain_weak (b1#b2#c) = (if valid_blocks b1 b2 then valid_chain_weak (b2#c) else False)"


(*-- Functions for allBlocks/allBlocks' and extendTree --*)
fun allBlocks :: "T \<Rightarrow> BlockPool" where 
"allBlocks (Node m l r) = allBlocks l @ allBlocks r @ [m]"|
"allBlocks Leaf = []"

fun allBlocksAppend :: "Block \<Rightarrow>BlockPool list\<Rightarrow> BlockPool list" where
"allBlocksAppend Bl BlP = (map (\<lambda> bl. bl @ [Bl]) BlP)"

fun allBlocks' :: "T \<Rightarrow> BlockPool list" where
"allBlocks' (Node m l r) = allBlocksAppend m (allBlocks' l) @allBlocksAppend m (allBlocks' r)"|
"allBlocks' Leaf = [[]]"

fun extendTree :: "T \<Rightarrow> Block \<Rightarrow> T" where
"extendTree (Node Bl1 Leaf Leaf) Bl2 =  (
  if valid_blocks Bl2 Bl1 then (Node Bl1 (Node Bl2 Leaf Leaf) Leaf) 
  else (Node Bl1 Leaf Leaf)) "|
"extendTree (Node Bl1 t1 Leaf) Bl2 =  (
  if valid_blocks Bl2 Bl1 then (Node Bl1 t1 (Node Bl2 Leaf Leaf)) 
  else (Node Bl1 (extendTree t1 Bl2) Leaf))"|
"extendTree (Node Bl1 Leaf t1) Bl2 =  (
  if valid_blocks Bl2 Bl1 then (Node Bl1 (Node Bl2 Leaf Leaf) t1) 
  else (Node Bl1  Leaf (extendTree t1 Bl2)))"|
"extendTree (Node Bl1 t1 t2) Bl2 =(Node Bl1 (extendTree t1 Bl2) (extendTree t2 Bl2))"|
"extendTree Leaf Bl2 = Leaf"


(*-- Functions for finding best_chain --*)

fun best_c :: "Slot \<Rightarrow> BlockPool list \<Rightarrow> (Block list \<times> int \<times> bool) option"where 
"best_c slot list = (let list' = map (\<lambda> l. (l,sl (hd l), valid_chain l)) list 
  in find (\<lambda> (c,s,v).v\<and>(s\<le>slot)) list')"

fun get_first :: "(Block list \<times> int \<times> bool) option \<Rightarrow>Block list" where
"get_first a = (case a of None \<Rightarrow> [] | Some a \<Rightarrow> fst a)"

fun best_chain :: "Slot \<Rightarrow> T \<Rightarrow> Chain" where
"best_chain s Leaf = []"|
"best_chain s (Node x l r) = (if s > 0 then get_first ( best_c s (allBlocks' (Node x l r)))else [GenBlock])"

fun block_eq :: "Block \<Rightarrow> Block \<Rightarrow> bool" where
"block_eq b1 b2 = (b1 =b2)"

fun blockpool_eq :: "BlockPool \<Rightarrow> BlockPool \<Rightarrow> bool" where
"blockpool_eq bpl1 bpl2 = (bpl1 =bpl2)"

fun blocktree_eq :: "T \<Rightarrow> T \<Rightarrow> bool" where
"blocktree_eq (Node t1 t2 t3) (Node t_1 t_2 t_3) =((block_eq t1 t_1) \<and> blocktree_eq t2 t_2 \<and> blocktree_eq t3 t_3)"|
"blocktree_eq Leaf Leaf = True"|
"blocktree_eq (Node t1 t2 t3) Leaf  =False"|
"blocktree_eq Leaf (Node _ _ _)  =False"

(* Unit Testing Code*)

definition "test_tree_bad = (Node GenBlock (Node \<lparr>sl = 1, txs =1, pred = H 0 0, bid = 1\<rparr>
 (Node \<lparr>sl = 2, txs =1, pred = H 1 1, bid = 1\<rparr> Leaf Leaf) Leaf) (Node \<lparr>sl = 1, txs =1, pred = H 0 0, bid = 4\<rparr> 
Leaf (Node \<lparr>sl = 2, txs =1, pred = H 1 1, bid = 1\<rparr> Leaf Leaf)))"
definition "test_tree_bad2 = (Node GenBlock (Node \<lparr>sl = 1, txs =1, pred = H 0 0, bid = 1\<rparr>
 (Node \<lparr>sl = 2, txs =1, pred = H 1 1, bid = 1\<rparr> Leaf Leaf) Leaf) (Node \<lparr>sl = 1, txs =1, pred = H 0 0, bid = 4\<rparr> 
Leaf (Node \<lparr>sl = 2, txs =1, pred = H 1 1, bid = 4\<rparr> Leaf Leaf)))"
definition "test_tree = (Node GenBlock 
(Node \<lparr>sl = 1, txs =1, pred = H 0 0, bid = 1\<rparr> (Node \<lparr>sl = 2, txs =1, pred = H 1 1, bid = 1\<rparr>
 (Node \<lparr>sl = 3, txs =1, pred = H 2 1, bid = 6\<rparr> Leaf Leaf) Leaf) Leaf)
 (Node \<lparr>sl = 1, txs =1, pred = H 0 0, bid = 4\<rparr> Leaf (Node \<lparr>sl = 2, txs =1, pred = H 1 4, bid = 1\<rparr> Leaf Leaf)))"
definition "extend_block = \<lparr>sl = 4, txs = 1, pred = H 3 6, bid = 4\<rparr>"


value "valid_blocks Block1 GenBlock"
value "valid_chain [Block1,GenBlock]"
value "Block1 # [GenBlock]"


value "(extendTree tree0 Block1) = (Node GenBlock (Node Block1 Leaf Leaf)  Leaf)"
value "extendTree (T.Node \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr> T.Leaf (T.Node \<lparr>sl = 1, txs = 0, pred = H 0 0, bid = 0\<rparr> T.Leaf T.Leaf))  \<lparr>sl =1 , txs = 0, pred = H 0 0, bid = 0\<rparr> "
value "valid_chain  (\<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr>#[\<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 1\<rparr>])"


value "valid_chain [Block3,Block2,Block1,GenBlock]"
value "valid_chain [\<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr>, \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr>, \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr>]"
value "HashCompare  \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr> \<lparr>sl = 2, txs = 1, pred = H 1 1, bid = 2\<rparr>"

value "HashCompare GenBlock Block1"
value "HashCompare Block1 Block2"
value "HashCompare Block2 Block3"
value "HashCompare GenBlock Block2"
value "HashCompare Block2 Block1"
value "HashCompare Block1 GenBlock"

value "valid_blocks Block1 GenBlock"
value "valid_blocks Block2 Block1"
value "valid_blocks Block3 Block2"
value "valid_blocks Block2 Block3"
value "b#[c]"
definition valid_t where
"valid_t t = (\<forall>c\<in>set(allBlocks' t).valid_chain c)"

definition valid_t_weak where
"valid_t_weak t = (\<forall>c \<in> set(allBlocks' t).valid_chain_weak c)"
value "valid_t test_tree_bad"

value "valid_t test_tree_bad2"

value "valid_t test_tree"

value "best_chain 0 test_tree"

value "best_chain 3 test_tree"

value "best_chain 4 (extendTree test_tree extend_block)"

value "valid_chain(best_chain 4 (extendTree test_tree extend_block))"

value "valid_chain [\<lparr>sl = 2, txs = 2, pred = H 1 1, bid = 2\<rparr>, \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr>, \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr>]"

value "best_c (3::int) (allBlocks'((Node GenBlock (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr> (Node \<lparr>sl = 2, txs = 2, pred = H 1 1, bid = 2\<rparr> Leaf Leaf) Leaf)
 (Node \<lparr>sl = 2, txs = 2, pred = H 1 1, bid = 2\<rparr> Leaf Leaf))) )"


value "best_chain 10  ((Node GenBlock (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr> (Node \<lparr>sl = 2, txs = 2, pred = H 1 1, bid = 2\<rparr> Leaf Leaf) Leaf)
 (Node \<lparr>sl = 2, txs = 2, pred = H 1 1, bid = 2\<rparr> Leaf Leaf)))"
value "best_c (3::int) (allBlocks' ((Node GenBlock (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr>  Leaf Leaf)
 (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 2\<rparr> Leaf Leaf))))"

value "allBlocks' ((Node GenBlock (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr> (Node \<lparr>sl = 2, txs = 2, pred = H 1 1, bid = 2\<rparr> Leaf Leaf) Leaf)
 (Node \<lparr>sl = 2, txs = 2, pred = H 1 1, bid = 2\<rparr> Leaf Leaf)))"

value "valid_chain (best_chain 0 (Node GenBlock (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr> (Node \<lparr>sl = 1, txs = 1, pred = H 1 1, bid = 1\<rparr> (Node \<lparr>sl = 2, txs = 2, pred = H 1 1, bid = 2\<rparr> Leaf Leaf) Leaf) Leaf)
 (Node \<lparr>sl = 1, txs = 1, pred = H 1 1, bid = 1\<rparr> Leaf Leaf)))"

value "best_chain 2  ((Node GenBlock (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr> (Node \<lparr>sl = 1, txs = 1, pred = H 1 1, bid = 1\<rparr> Leaf Leaf) Leaf)
 (Node \<lparr>sl = 1, txs = 1, pred = H 1 1, bid = 1\<rparr> Leaf Leaf)))"
value "allBlocks'  (Node \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 1\<rparr> Leaf Leaf)"

value "valid_chain (best_chain 4 (T.Node \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr> T.Leaf T.Leaf))"


(*-- LEMMAS + PROOFS -- *)




export_code HashCompare' HashCompare GenBlock  blockpool_eq  block_eq valid_blocks valid_chain valid_chain_weak allBlocks allBlocksAppend allBlocks' tree0 extendTree valid_t valid_t_weak best_c get_first best_chain blocktree_eq  in Haskell  

lemma initialTree : "allBlocks tree0 = [GenBlock]" 
  by (simp add: GenBlock_def tree0_def)

lemma ExtendInitial : "(extendTree tree0 Block1) = (Node GenBlock (Node Block1 Leaf Leaf) Leaf)"
  by (simp add: GenBlock_def tree0_def Block1_def)

lemma "extendTree Leaf B = Leaf"
  by simp 
lemma BaseExtend : "(extendTree t b \<noteq> t) \<Longrightarrow> set (allBlocks (extendTree t b)) =set ([b]@ allBlocks t)"
proof(induction "t")
  case Leaf
  then show ?case 
    by simp
next
  case (Node x1 t1 t2) note Nodex1 = this
  then show ?case proof (cases "t1")
    case Leaf note Leaft1 = this
    then show ?thesis proof (cases "t2")
      case Leaf
      then show ?thesis using Nodex1 Leaft1 
        by auto
    next
      case (Node x21 x22 x23)
      then show ?thesis using Nodex1 Leaft1
        by auto
    qed
  next
    case (Node x21 x22 x23) note Nodet1 = this
    then show ?thesis proof (cases "t2")
      case Leaf
      then show ?thesis using Nodex1 Nodet1 
        by auto
    next
      case (Node x21 x22 x23)
      then show ?thesis using Nodex1 Nodet1 
        by fastforce
    qed
  qed
qed

lemma GenExtend : assumes "(extendTree t b \<noteq> t)\<and>valid_t t" shows "set (allBlocks (extendTree t b)) =set ([b]@ allBlocks t)"
proof(cases "t")
  case Leaf note LeafCase = this
  then show ?thesis using assms LeafCase
    by simp
next
  case (Node x1 t1 t2)
  then show ?thesis proof(cases "t1")
    case Leaf
    then show ?thesis using assms BaseExtend 
      by simp
  next
    case (Node x1 t11 t12)
    then show ?thesis using assms BaseExtend
      by simp
  qed
qed


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

lemma best_c_in : "best_c n bl \<noteq> None \<Longrightarrow> get_first(best_c n bl) \<in> set(bl)"
  apply(simp add: find_in)
proof(induction bl)
  case Nil
  then show ?case
    by simp 
next
  case (Cons a bl)
  then show ?case
    by auto
qed 
(*
lemma base_best_valid:"(valid_chain(best_chain s tree0) = True)"
proof(induction "s")
  case 0
  then show ?case  apply(simp add: GenBlock_def best_c_in tree0_def) done
next
  case (Suc s)
  then show ?case   apply(simp add: GenBlock_def best_c_in tree0_def) done
qed
*)

lemma best_valid :assumes"valid_t t" shows "valid_chain (best_chain s t)"
proof(cases "t")
  case Leaf
  then show ?thesis using assms
    by simp
next
  case (Node x21 x22 x23) note nodex21 = this
  then show ?thesis proof(cases "x22")
    case Leaf note leafx22 = this
    then show ?thesis proof(cases "x23")
      case Leaf note leafx23 =this
      show ?thesis using assms leafx23 leafx22 nodex21 apply(simp add: GenBlock_def best_c_in tree0_def) try
    next
      case (Node x21 x22 x23) note nodex23 =this
      then show ?thesis using "x21 = GenBlock" assms leafx22 nodex23 nodex21 apply(simp add: GenBlock_def best_c_in)
    qed
  next
    case (Node x21a x22a x23a) note nodex22 = this
    then show ?thesis proof(cases "x23")
      case Leaf
      then show ?thesis sorry
    next
      case (Node x21 x22 x23)
      then show ?thesis sorry
    qed
  qed
qed

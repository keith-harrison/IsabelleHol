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
"valid_blocks b1 b2 =  ( HashCompare b2 b1 \<and>(sl b2 < sl b1))"

fun valid_chain :: "Chain \<Rightarrow> bool" where
"valid_chain [] = False"|
"valid_chain [b1] = (if b1 = GenBlock then True else False)"|
"valid_chain (b1#b2#c) = (if valid_blocks b1 b2 \<and> (b1 \<noteq> GenBlock) then valid_chain (b2#c) else False)"

fun block_get where
"block_get (Node m l r) = m"|
"block_get Leaf = GenBlock"

fun valid_t_weak where
"valid_t_weak (Node m Leaf Leaf) = True"|
"valid_t_weak (Node m Leaf r) = ((valid_blocks (block_get r) m )\<and> valid_t_weak r)"|
"valid_t_weak (Node m l Leaf) = ((valid_blocks (block_get l) m )\<and> valid_t_weak l)"|
"valid_t_weak (Node m l r) = 
(valid_blocks (block_get l) m  \<and> valid_blocks (block_get r) m \<and> valid_t_weak r \<and> valid_t_weak l)"|
"valid_t_weak Leaf = True"

fun hash_t where
"hash_t (Node m Leaf Leaf) = True"|
"hash_t (Node m Leaf r) = ((HashCompare m (block_get r)  )\<and> hash_t r)"|
"hash_t (Node m l Leaf) = ((HashCompare m (block_get l)  )\<and> hash_t l)"|
"hash_t(Node m l r) = 
(HashCompare m (block_get l)  \<and> HashCompare m (block_get r)  \<and> hash_t r \<and> hash_t l)"|
"hash_t Leaf = True"

fun sl_t where
"sl_t (Node m Leaf Leaf) = True"|
"sl_t (Node m Leaf r) = ((sl m < sl (block_get r)  )\<and> sl_t r)"|
"sl_t (Node m l Leaf) = ((sl m < sl (block_get l)  )\<and> sl_t l)"|
"sl_t(Node m l r) = 
(sl m < sl (block_get l)  \<and> sl m < sl (block_get r)  \<and> sl_t r \<and> sl_t l)"|
"sl_t Leaf = True"

(*-- Functions for allBlocks/allBlocks' and extendTree --*)
fun allBlocks :: "T \<Rightarrow> BlockPool" where 
"allBlocks (Node m l r) = allBlocks l @ allBlocks r @ [m]"|
"allBlocks Leaf = []"

fun allBlocksAppend :: "Block \<Rightarrow>BlockPool list\<Rightarrow> BlockPool list" where
"allBlocksAppend Bl BlP = (map (\<lambda> bl. bl @ [Bl]) BlP)"

fun allBlocks' :: "T \<Rightarrow> BlockPool list" where
"allBlocks' (Node m l r) =( allBlocksAppend m (allBlocks' l) @allBlocksAppend m (allBlocks' r))"|
"allBlocks' Leaf = [[]]"

fun valid_t where
"valid_t Leaf = True"|
"valid_t t = (\<forall>c\<in>set(allBlocks' t).valid_chain c)"

value "allBlocks' (Node GenBlock (Node Block1 Leaf (Node Block2 (Node Block3 (Node Block4 Leaf (Node Block6 Leaf Leaf)) Leaf) (Node Block5 Leaf Leaf))) Leaf)"

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
"block_eq bl1 b2 = ((sl bl1 = sl b2)\<and>(txs bl1 = txs b2)\<and>(pred bl1 = pred b2)\<and>(bid bl1 = bid b2))"

fun blockpool_eq_set :: "BlockPool \<Rightarrow> BlockPool \<Rightarrow> bool" where
"blockpool_eq_set bpl1 bpl2 = (set(bpl1) = set(bpl2)) "


fun blockpool_eq :: "BlockPool \<Rightarrow> BlockPool \<Rightarrow> bool" where
"blockpool_eq Nil Nil= True"|
"blockpool_eq a b = (((set a \<inter> set b) =set a)\<and>((set a \<inter> set b) =set b))"


fun blocktree_eq :: "T \<Rightarrow> T \<Rightarrow> bool" where
"blocktree_eq (Node t1 t2 t3) (Node t_1 t_2 t_3) =((Node t1 t2 t3) = (Node t_1 t_2 t_3))"|
"blocktree_eq Leaf b = False"|
"blocktree_eq a Leaf = False" 


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


value "valid_blocks Block3 Block2"
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

definition "testblock = \<lparr>sl = 1, txs = 1, pred = H 2 1, bid = 1 \<rparr>"
definition "testblock2 = \<lparr>sl = 2, txs = 1, pred = H 1 1, bid = 1 \<rparr>"
value "extendTree (Node testblock Leaf Leaf) testblock2"
value"allBlocks (extendTree (Node testblock Leaf Leaf) testblock2)"
value"allBlocks (Node testblock Leaf Leaf)@[testblock2]"
value"blockpool_eq (allBlocks (extendTree (Node testblock Leaf Leaf) testblock2)) (allBlocks (Node testblock Leaf Leaf)@[testblock2])"
value"blockpool_eq_set (allBlocks (extendTree (Node testblock Leaf Leaf) testblock2)) (allBlocks (Node testblock Leaf Leaf)@[testblock2])"

(*-- LEMMAS + PROOFS -- *)

export_code HashCompare' HashCompare GenBlock  blockpool_eq_set  block_eq valid_blocks valid_chain  allBlocks allBlocksAppend allBlocks' tree0 extendTree valid_t valid_t_weak best_c get_first best_chain blocktree_eq  in Haskell  

lemma initialTree : "allBlocks tree0 = [GenBlock]" 
  by (simp add: GenBlock_def tree0_def)

lemma initialExtend : "(extendTree tree0 b \<noteq> tree0)
\<Longrightarrow> set (allBlocks (extendTree tree0 b)) = set ([b]@ allBlocks tree0)"
  apply(simp add : GenBlock_def tree0_def)
  by auto

lemma base_best_valid :"valid_chain(best_chain s (Node GenBlock Leaf Leaf))"
  apply(auto) apply(simp add:GenBlock_def) done

lemma initialExtendValid : "valid_t tree0 \<Longrightarrow>valid_t (extendTree tree0 b)"
  apply(simp add: GenBlock_def tree0_def) done

lemma initialExtendweakValid : "valid_t_weak tree0 \<Longrightarrow>valid_t_weak (extendTree tree0 b)"
  by (simp add: tree0_def)

lemma initialBestChain : "valid_t (extendTree tree0 b)
\<Longrightarrow> valid_chain( best_chain s (extendTree tree0 b)) "
  apply(simp add: GenBlock_def tree0_def) done 

lemma ExtendInitial : "(extendTree tree0 Block1) = (Node GenBlock (Node Block1 Leaf Leaf) Leaf)"
  by (simp add: GenBlock_def tree0_def Block1_def)

lemma "extendTree Leaf B = Leaf"
  by simp 

lemma SameBlock : assumes "block_eq bl1 bl2" shows "bl1 = bl2"
  using assms apply(auto) done

lemma SamePool : assumes "blockpool_eq (x) (y)" shows "set x = set y"
  using assms  
  by (smt (verit, best) blockpool_eq.elims(2))

lemma SameTreeBase : assumes "blocktree_eq T1 T2" shows "T1 = T2"
  using assms SameBlock 
  using blocktree_eq.elims(2) by blast

lemma SameTree : assumes "blocktree_eq T1 T2" shows "blockpool_eq (allBlocks T1) (allBlocks T2)"
  using assms SamePool 
  by (metis (no_types, opaque_lifting) SameTreeBase blockpool_eq.simps(1) blockpool_eq.simps(3) inf.idem valid_chain.cases)


lemma BaseExtend : "(extendTree t b \<noteq> t) 
\<Longrightarrow> set (allBlocks (extendTree t b)) = set ([b]@ allBlocks t)"
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

lemma GenExtend : assumes "valid_t t\<and> extendTree t b \<noteq> t" shows
"set (allBlocks (extendTree t b)) =set ([b]@ allBlocks t)"
proof(cases "t")
  case Leaf note LeafCase = this
  then show ?thesis using assms LeafCase 
    by simp
next
  case (Node x1 t1 t2) note t1Node = this
  then show ?thesis proof(cases "t1")
    case Leaf note t2Leaf = this
    then show ?thesis proof(cases "t2")
      case Leaf
      then show ?thesis using t1Node t2Leaf assms BaseExtend apply(auto)done
    next
      case (Node x21 x22 x23)
      then show ?thesis using t1Node t2Leaf assms  BaseExtend apply(auto) done
    qed
  next
    case (Node x1 t11 t12)
    then show ?thesis using assms BaseExtend apply(auto) done
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

lemma slThan : assumes "r \<noteq> Leaf \<and> l\<noteq>Leaf\<and>valid_t_weak (Node m l r)\<and>block_get (Node m l r) = m" shows "( sl m < sl (block_get r) \<and> sl m < sl(block_get l))"
  using assms apply(auto) apply(rule valid_t_weak.cases)
  apply auto[1] 
  apply simp
  apply simp 
  apply simp 
  apply simp
  apply (metis allBlocks.elims valid_blocks.elims(2) valid_t_weak.simps(4)) apply(rule block_get.cases)
  apply auto[1] 
  by (metis allBlocks.elims valid_blocks.elims(2) valid_t_weak.simps(4)) 
lemma slThan2 : assumes "r \<noteq> Leaf \<and> l\<noteq>Leaf\<and> sl_t (Node m l r)\<and>block_get (Node m l r) = m" shows "( sl m < sl (block_get r) \<and> sl m < sl(block_get l))"
  using assms apply(auto) apply(rule valid_t_weak.cases)
  apply auto[1] 
  apply simp
  apply simp 
  apply simp 
  apply simp
  apply (metis T.distinct(1) T.inject  assms block_get.elims sl_t.simps(5))
  by (metis block_get.elims sl_t.simps(4))
lemma slThanAll : assumes "r\<noteq>Leaf \<and>l \<noteq>Leaf\<and>valid_t_weak(Node m l r)" shows "(sl_t (Node m l r))"
 proof(cases "l")
   case Leaf note lleaf=this
   then show ?thesis proof(cases "r")
     case Leaf
     then show ?thesis using assms 
       by simp
   next
     case (Node x21 x22 x23)
     then show ?thesis using assms lleaf 
       by simp
   qed
   next
   case (Node x21 x22 x23) note rnode=this
   then show ?thesis proof(cases "r")
     case Leaf
     then show ?thesis using assms rnode
       by simp
   next
     case (Node x1 t1 t2)
     then show ?thesis using assms rnode slThan slThan2 apply(auto) try
   qed
 qed
lemma predThan : assumes "r \<noteq> Leaf \<and> l\<noteq>Leaf\<and>valid_t_weak (Node m l r)" shows "( HashCompare m (block_get r) \<and> HashCompare m (block_get l))"
  using assms apply(auto) apply(rule valid_t_weak.cases)
  apply auto[1] 
  apply simp
  apply simp 
  apply simp 
  apply simp apply(rule block_get.cases)
  apply blast
  apply (metis HashCompare.elims(2) valid_blocks.elims(2) valid_t.cases valid_t_weak.simps(5))
  by (metis (no_types, lifting) HashCompare.elims(2) block_get.elims valid_blocks.elims(2) valid_t_weak.simps(5)) 
lemma predThan2 : assumes "r \<noteq> Leaf \<and> l\<noteq>Leaf\<and>hash_t(Node m l r)" shows "( HashCompare m (block_get r) \<and> HashCompare m (block_get l))"
  using assms predThan apply(auto) apply(rule valid_t_weak.cases)
  apply auto[1] 
  apply simp
  apply simp 
  apply simp 
  apply simp apply(rule block_get.cases)
  apply blast 
  try

lemma validExtend : assumes "valid_t_weak t" shows "valid_t_weak (extendTree t b)"
proof(cases "t")
  case Leaf
  then show ?thesis 
    by simp
next
  case (Node x1 t1 t2) note t = this
  then show ?thesis proof(cases "t1")
    case Leaf note leaft1=this
    then show ?thesis proof(cases "t2")
      case Leaf
      then show ?thesis using assms leaft1 t apply(auto) done
    next
      case (Node x21 x22 x23)
      then show ?thesis  using assms leaft1 t  initialExtendweakValid slThan  apply(simp add: tree0_def GenBlock_def) apply(auto) apply(rule HashCompare'.cases HashCompare'.elims HashCompare'.simps)
         apply(rule valid_t_weak.cases valid_t_weak.elims valid_t_weak.simps valid_t_weak.induct) apply(rule extendTree.cases extendTree.elims extendTree.simps extendTree.induct) 
        apply(rule block_get.cases block_get.elims block_get.simps)
        apply auto[1] apply(rule valid_t.cases valid_t.elims valid_t.simps valid_t_weak.induct) apply(simp+)  sorry
    qed
  next
    case (Node x21 x22 x23)
    then show ?thesis sorry
  qed
  qed

lemma best_valid: assumes "x = GenBlock\<and>valid_t_weak (Node x l r)" shows "valid_chain (best_chain s (Node x l r))"
proof(cases "l")
  case Leaf note lleaf = this
  then show ?thesis proof(cases "r")
    case Leaf
    then show ?thesis using assms lleaf apply(auto) apply(simp add: GenBlock_def) done
  next
    case (Node x21 x22 x23)
    then show ?thesis using assms lleaf apply(auto) apply(simp add: GenBlock_def) done
  qed
next
  case (Node x21 x22 x23) note lnode = this
  then show ?thesis proof(cases "r")
    case Leaf
    then show ?thesis using assms lnode find_in best_c_in base_best_valid apply(auto) apply(simp add: GenBlock_def find_def o_def) sorry
  next
    case (Node x1 x2 x3)
    then show ?thesis using assms lnode find_in best_c_in base_best_valid apply(auto) apply(simp add: GenBlock_def append_def find_def map_def set_def) sorry
  qed
qed




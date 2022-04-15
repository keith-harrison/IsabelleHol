theory BlockchainNew
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


datatype T = Leaf Block | Node Block T  | Node2 Block T T  

definition "tree0 = Leaf GenBlock"

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

fun block_get :: "T \<Rightarrow> Block" where
"block_get (Node2 m l r) = m"|
"block_get (Node m l) = m"|
"block_get (Leaf m) = m"

fun valid_t_weak where
"valid_t_weak (Node2 m l r) = 
(valid_blocks (block_get l) m  \<and> valid_blocks (block_get r) m \<and> valid_t_weak r \<and> valid_t_weak l)"|
"valid_t_weak (Node m l) = (valid_blocks (block_get l) m  \<and> valid_t_weak l)"|
"valid_t_weak (Leaf m) = True"

fun hash_t where
"hash_t(Node2 m l r) = 
(HashCompare m (block_get l)  \<and> HashCompare m (block_get r)  \<and> hash_t r \<and> hash_t l)"|
"hash_t (Node m l) = (HashCompare m (block_get l) \<and> hash_t l)"|
"hash_t (Leaf m) = True"

fun sl_t where
"sl_t(Node2 m l r) = 
(sl m < sl (block_get l)  \<and> sl m < sl (block_get r)  \<and> sl_t r \<and> sl_t l)"|
"sl_t (Node m l) = (sl m < sl (block_get l) \<and> sl_t l)"|
"sl_t (Leaf m) = True"

(*-- Functions for allBlocks/allBlocks' and extendTree --*)

fun allBlocks :: "T \<Rightarrow> BlockPool" where
"allBlocks (Node2 m l r) = allBlocks l @ allBlocks r @ [m]"|
"allBlocks (Node m l ) = allBlocks l @ [m]"|
"allBlocks (Leaf m) = [m]"

fun allBlocksAppend :: "Block \<Rightarrow>BlockPool list\<Rightarrow> BlockPool list" where
"allBlocksAppend Bl BlP = (map (\<lambda> bl. bl @ [Bl]) BlP)"

fun allBlocks' :: "T \<Rightarrow> BlockPool list" where
"allBlocks' (Node2 m l r) =( allBlocksAppend m (allBlocks' l) @allBlocksAppend m (allBlocks' r))"|
"allBlocks' (Node m l) =( allBlocksAppend m (allBlocks' l) @[[m]])"|
"allBlocks' (Leaf m)= [[m]]"

fun extendTree :: "T \<Rightarrow> Block \<Rightarrow> T" where
"extendTree (Leaf Bl1) Bl2 = 
  (if valid_blocks Bl2 Bl1 then (Node Bl1 (Leaf Bl2)) else (Leaf Bl1))"|
"extendTree (Node Bl1 l) Bl2 =
  (if valid_blocks Bl2 Bl1 then (Node2 Bl1 l (Leaf Bl2)) else (Node Bl1 (extendTree l Bl2)))"|
"extendTree (Node2 m l r) Bl2 = (Node2 m (extendTree l Bl2) (extendTree r Bl2))"

fun valid_t where
"valid_t t = (\<forall>c\<in>set(allBlocks' t).valid_chain c)"
(*-- Functions for finding best_chain --*)

fun best_c :: "Slot \<Rightarrow> BlockPool list \<Rightarrow> (Block list \<times> int \<times> bool) option"where 
"best_c slot list = (let list' = map (\<lambda> l. (l,sl (hd l), valid_chain l)) list 
  in find (\<lambda> (c,s,v).v\<and>(s\<le>slot)) list')"


fun get_first :: "(Block list \<times> int \<times> bool) option \<Rightarrow>Block list" where
"get_first a = (case a of None \<Rightarrow> [] | Some a \<Rightarrow> fst a)"

fun best_chain :: "Slot \<Rightarrow> T \<Rightarrow> Chain" where
"best_chain s (Node x l) = (if s > 0 then get_first ( best_c s (allBlocks' (Node x l)))else [GenBlock])"|
"best_chain s (Node2 x l r) = (if s > 0 then get_first ( best_c s (allBlocks' (Node2 x l r)))else [GenBlock])"|
"best_chain s (Leaf m) = (if s > 0 then get_first ( best_c s (allBlocks' (Leaf m)))else [GenBlock])"

fun block_eq :: "Block \<Rightarrow> Block \<Rightarrow> bool" where
"block_eq bl1 b2 = ((sl bl1 = sl b2)\<and>(txs bl1 = txs b2)\<and>(pred bl1 = pred b2)\<and>(bid bl1 = bid b2))"

fun blockpool_eq_set :: "BlockPool \<Rightarrow> BlockPool \<Rightarrow> bool" where
"blockpool_eq_set bpl1 bpl2 = (set(bpl1) = set(bpl2)) "


fun blockpool_eq :: "BlockPool \<Rightarrow> BlockPool \<Rightarrow> bool" where
"blockpool_eq Nil Nil= True"|
"blockpool_eq a b = (((set a \<inter> set b) =set a)\<and>((set a \<inter> set b) =set b))"


fun blocktree_eq :: "T \<Rightarrow> T \<Rightarrow> bool" where
"blocktree_eq (Node2 t1 t2 t3) (Node2 t_1 t_2 t_3) =((Node2 t1 t2 t3) = (Node2 t_1 t_2 t_3))"|
"blocktree_eq (Node t1 t2) (Node t_1 t_2) =((Node t1 t2) = (Node t_1 t_2))"|
"blocktree_eq (Leaf m) (Leaf n) = (Leaf m = Leaf n)"|
"blocktree_eq (T.Leaf v) (T.Node va vb) = False"|
"blocktree_eq (T.Leaf v) (Node2 va vb vc) = False"|
"blocktree_eq (T.Node v va) (T.Leaf vb) = False"|
"blocktree_eq (T.Node v va) (Node2 vb vc vd) = False"|
"blocktree_eq (Node2 va vb vc) (T.Leaf v) = False"|
"blocktree_eq (Node2 vb vc vd) (T.Node v va) = False" 


(*-- LEMMAS + PROOFS -- *)

export_code HashCompare' HashCompare GenBlock  blockpool_eq_set  block_eq valid_blocks valid_chain  allBlocks allBlocksAppend allBlocks' tree0 extendTree valid_t valid_t_weak best_c get_first best_chain blocktree_eq  in Haskell  

lemma initialTree : "allBlocks tree0 = [GenBlock]" 
  by (simp add: GenBlock_def tree0_def)

lemma initialExtend : "(extendTree tree0 b \<noteq> tree0)
\<Longrightarrow> set (allBlocks (extendTree tree0 b)) = set ([b]@ allBlocks tree0)"
  apply(simp add : GenBlock_def tree0_def)
  by auto

lemma base_best_valid :"valid_chain(best_chain s tree0)"
  apply(simp add : tree0_def GenBlock_def) done
  

lemma initialExtendValid : "valid_t tree0 \<Longrightarrow>valid_t (extendTree tree0 b)"
  apply(simp add: GenBlock_def tree0_def) done

lemma initialExtendweakValid : "valid_t_weak tree0 \<Longrightarrow>valid_t_weak (extendTree tree0 b)"
  by (simp add: tree0_def)

lemma initialBestChain : "valid_t (extendTree tree0 b)
\<Longrightarrow> valid_chain( best_chain s (extendTree tree0 b)) "
  apply(simp add: GenBlock_def tree0_def) done 

lemma ExtendInitial : "(extendTree tree0 Block1) = (Node GenBlock (Leaf Block1))"
  by (simp add: GenBlock_def tree0_def Block1_def)

lemma ExtendLeaf : assumes "valid_blocks B m" shows "extendTree (Leaf m) B = (Node m (Leaf B))"
  using assms by auto
  

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

lemma slThan : assumes "valid_t_weak t \<and> t = (Node2 m l r)" 
  shows "( sl m < sl (block_get r) \<and> sl m < sl(block_get l))"
  using assms by auto

lemma predThan : assumes "valid_t_weak t \<and> t = (Node2 m l r)" 
  shows "( HashCompare m (block_get r) \<and> HashCompare m (block_get l))"
  using assms by auto

lemma slThan2 : assumes "sl_t t \<and> t = (Node2 m l r)" 
  shows "( sl m < sl (block_get r) \<and> sl m < sl(block_get l))"
  using assms by auto

lemma predThan2 : assumes "hash_t t \<and> t = (Node2 m l r)" 
  shows "( HashCompare m (block_get r) \<and> HashCompare m (block_get l))"
  using assms by auto


lemma hashAll : assumes "valid_t_weak t" shows "hash_t t"
  using assms oops

lemma validSame : assumes "valid_t_weak t" shows "sl_t t \<and> hash_t t"
  using assms oops

lemma BaseExtend : "(extendTree t b \<noteq> t) 
\<Longrightarrow> set (allBlocks (extendTree t b)) = set ([b]@ allBlocks t)" oops

lemma validExtend : assumes "valid_t_weak t" shows "valid_t_weak (extendTree t b)"
  using assms oops

lemma best_valid: assumes "s>0\<and>block_get t = GenBlock\<and>valid_t_weak t" 
  shows "valid_chain (best_chain s t)"
proof(cases "t")
  case (Leaf x1)
  then show ?thesis apply(simp add: GenBlock_def) 
    using GenBlock_def assms by auto
next
  case (Node x21 x22)
  then show ?thesis apply(simp add: GenBlock_def) using GenBlock_def assms try
next
  case (Node2 x31 x32 x33)
  then show ?thesis sorry
qed



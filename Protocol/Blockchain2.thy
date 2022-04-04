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



fun HashCompare' :: "Hash \<Rightarrow> Block \<Rightarrow> bool" where
"HashCompare' (H a b) bl1 = ((a = sl bl1) \<and> (b = bid bl1))"


fun HashCompare :: "Block \<Rightarrow> Block \<Rightarrow> bool" where
"HashCompare bl1 bl2 = HashCompare' (pred bl2) bl1"

definition "GenBlock = \<lparr>sl = 0, txs = 0, pred = H 0 0 ,bid = 0\<rparr>"
definition "Block1 = \<lparr>sl = 1, txs =1, pred = H 0 0, bid = 1\<rparr>"
definition "Block2 = \<lparr> sl = 2, txs = 0, pred = H 1 1, bid = 1\<rparr>"
definition "Block3 = \<lparr> sl = 3, txs = 0, pred = H 2 1, bid = 1\<rparr>"

value "HashCompare GenBlock Block1"
value "HashCompare Block1 Block2"
value "HashCompare Block2 Block3"
value "HashCompare GenBlock Block2"
value "HashCompare Block2 Block1"
value "HashCompare Block1 GenBlock"

fun valid_blocks ::"Block \<Rightarrow> Block \<Rightarrow> bool" where
"valid_blocks b1 b2 =  (HashCompare b2 b1 \<and> (sl b2 < sl b1)) "

value "valid_blocks Block1 GenBlock"
value "valid_blocks Block2 Block1"
value "valid_blocks Block3 Block2"
value "valid_blocks Block2 Block3"
value "b#[c]"

(*checking for b's being a node only and a /genesis node at the end of the list missing*)
fun valid_chain :: "Chain \<Rightarrow> bool" where
"valid_chain [] = False"|
"valid_chain [b1] = (if b1 = GenBlock then True else False)"|
"valid_chain (b1#b2#c) = (if valid_blocks b1 b2 \<and> (b1 \<noteq> GenBlock) then valid_chain (b2#c) else False)"

value "valid_chain [Block3,Block2,Block1,GenBlock]"
value "valid_chain [\<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr>, \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr>, \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr>]"
value "HashCompare  \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr> \<lparr>sl = 2, txs = 1, pred = H 1 1, bid = 2\<rparr>"


 
datatype T = Leaf | Node Block T T 

fun allBlocks :: "T \<Rightarrow> BlockPool" where 
"allBlocks (Node m l r) = allBlocks l @ allBlocks r @ [m]"|
"allBlocks Leaf = []"

(*
fun allBlocksGen :: "T \<Rightarrow> BlockPool" where
"allBlocksGen (Node m l r) = (if m = GenBlock then allBlocks l@allBlocks r @[m]else [])"|
"allBlocksGen Leaf = []"
*)

fun allBlocksAppend :: "Block \<Rightarrow>BlockPool list\<Rightarrow> BlockPool list" where
"allBlocksAppend Bl BlP = (map (\<lambda> bl. bl @ [Bl]) BlP)"

fun allBlocks' :: "T \<Rightarrow> BlockPool list" where
"allBlocks' (Node m l r) = allBlocksAppend m (allBlocks' l) @allBlocksAppend m (allBlocks' r)"|
"allBlocks' Leaf = [[]]"
(*
fun allBlocksGen' :: "T \<Rightarrow> BlockPool list" where
"allBlocksGen' (Node m l r) = (if m = GenBlock then allBlocksAppend m (allBlocks' l) @allBlocksAppend m (allBlocks' r) else [])"
*)
definition "tree0 = Node GenBlock Leaf Leaf"

lemma initialTree : "allBlocks tree0 = [GenBlock]" 
  by (simp add: GenBlock_def tree0_def)

fun extendTree :: "T \<Rightarrow> Block \<Rightarrow> T" where
"extendTree (Node Bl1 Leaf Leaf) Bl2 =  (if valid_blocks Bl2 Bl1 then (Node Bl1 (Node Bl2 Leaf Leaf) Leaf) else (Node Bl1 Leaf Leaf)) "|
"extendTree (Node Bl1 t1 Leaf) Bl2 =  (if valid_blocks Bl2 Bl1 then (Node Bl1 t1 (Node Bl2 Leaf Leaf)) else (Node Bl1 (extendTree t1 Bl2) Leaf))"|
"extendTree (Node Bl1 Leaf t1) Bl2 =  (if valid_blocks Bl2 Bl1 then (Node Bl1 (Node Bl2 Leaf Leaf) t1) else (Node Bl1  Leaf (extendTree t1 Bl2)))"|
"extendTree (Node Bl1 t1 t2) Bl2 =(Node Bl1 (extendTree t1 Bl2) (extendTree t2 Bl2))"|
"extendTree Leaf Bl2 = Leaf"
value "valid_blocks Block1 GenBlock"
value "valid_chain [Block1,GenBlock]"
value "Block1 # [GenBlock]"
(*
fun extendTreeGen :: "T \<Rightarrow> Block \<Rightarrow> T" where
"extendTreeGen (Node Bl1 Leaf Leaf) Bl2 = (if valid_chain (Bl2#[Bl1]) then (Node Bl1 (Node Bl2 Leaf Leaf) Leaf) else (Node Bl1 Leaf Leaf)) "|
"extendTreeGen (Node Bl1 t1 Leaf) Bl2 =  (if valid_chain (Bl2#[Bl1])  then (Node Bl1 t1 (Node Bl2 Leaf Leaf)) else (if Bl1 = GenBlock then (Node Bl1 (extendTree t1 Bl2) Leaf) else (Node Bl1 t1 Leaf)))"|
"extendTreeGen (Node Bl1 Leaf t1) Bl2 =  (if valid_chain (Bl2#[Bl1]) then (Node Bl1 (Node Bl2 Leaf Leaf) t1) else (if Bl1 = GenBlock then (Node Bl1  Leaf (extendTree t1 Bl2)) else (Node Bl1 Leaf t1)))"|
"extendTreeGen (Node Bl1 t1 t2) Bl2 = (if Bl1 = GenBlock then (Node Bl1 (extendTree t1 Bl2) (extendTree t2 Bl2)) else (Node Bl1 t1 t2)) "|
"extendTreeGen Leaf Bl2 = Leaf "
*)

lemma "extendTree Leaf B = Leaf"
  by simp 


value "(extendTree tree0 Block1) = (Node GenBlock (Node Block1 Leaf Leaf)  Leaf)"
value "extendTree (T.Node \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr> T.Leaf (T.Node \<lparr>sl = 1, txs = 0, pred = H 0 0, bid = 0\<rparr> T.Leaf T.Leaf))  \<lparr>sl =1 , txs = 0, pred = H 0 0, bid = 0\<rparr> "
value "valid_chain  (\<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr>#[\<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 1\<rparr>])"
lemma ExtendInitial : "(extendTree tree0 Block1) = (Node GenBlock (Node Block1 Leaf Leaf) Leaf)"
  by (simp add: GenBlock_def tree0_def Block1_def)

definition valid_t where
"valid_t t = (\<forall>c\<in>set(allBlocks' t).valid_chain c)"

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


fun best_c :: "nat \<Rightarrow> Block list list \<Rightarrow> (Block list \<times> nat \<times> bool) option"where 
"best_c slot list = (let list' = map (\<lambda> l. (l,sl (hd l), valid_chain l)) list in find (\<lambda> (c,s,v).v\<and>(s\<le>slot)) list')"

definition get_first :: "(Block list \<times> nat \<times> bool) option \<Rightarrow>Block list" where
"get_first a = (case a of None \<Rightarrow> [] | Some a \<Rightarrow> fst a)"

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

fun best_chain :: "Slot \<Rightarrow> T \<Rightarrow> Block list" where
"best_chain s Leaf = []"|
"best_chain 0 (Node x _ _) = []"|
"best_chain s (Node x l r) = get_first ( best_c s (allBlocks' (Node x l r)))"

value "best_c (3::nat) (allBlocks' ((Node GenBlock (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr>  Leaf Leaf)
 (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 2\<rparr> Leaf Leaf))))"

value "allBlocks' ((Node GenBlock (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr> (Node \<lparr>sl = 1, txs = 1, pred = H 1 1, bid = 1\<rparr> Leaf Leaf) Leaf)
 (Node \<lparr>sl = 1, txs = 1, pred = H 1 1, bid = 1\<rparr> Leaf Leaf)))"

value "valid_chain (best_chain 0 (Node GenBlock (Node \<lparr>sl = 1, txs = 1, pred = H 0 0, bid = 1\<rparr> (Node \<lparr>sl = 1, txs = 1, pred = H 1 1, bid = 1\<rparr> (Node \<lparr>sl = 2, txs = 2, pred = H 1 1, bid = 2\<rparr> Leaf Leaf) Leaf) Leaf)
 (Node \<lparr>sl = 1, txs = 1, pred = H 1 1, bid = 1\<rparr> Leaf Leaf)))"

value "best_chain 1 (Node \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr> Leaf Leaf)"
value "allBlocks'  (Node \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 1\<rparr> Leaf Leaf)"

value "valid_chain (best_chain 1 (T.Node \<lparr>sl = 0, txs = 0, pred = H 0 0, bid = 0\<rparr> T.Leaf T.Leaf))"
lemma best_valid :assumes"t\<noteq>Leaf\<and>s > 0 \<and>valid_t t" shows "valid_chain (best_chain s t)"
proof(cases "t")
  case Leaf
  then show ?thesis using assms
    by simp
next
  case (Node x1 x2 x3) note nodet = this
  then show ?thesis proof(cases "x2")
    case Leaf note x2leaf = this
    then show ?thesis proof(cases "x3")
      case Leaf
      then show ?thesis  using assms nodet x2leaf apply(simp add:GenBlock_def valid_t_def) apply(auto) try
    next
      case (Node x21 x22 x23)
      then show ?thesis using assms nodet x2leaf apply(simp add:GenBlock_def valid_t_def) sorry
    qed
  next
    case (Node x21 x22 x23) note x2node = this
    then show ?thesis proof(cases "x3")
      case Leaf
      then show ?thesis using assms nodet x2node apply(simp add:GenBlock_def valid_t_def) sorry
    next
      case (Node x21 x22 x23)
      then show ?thesis using assms nodet x2node apply(simp add:GenBlock_def valid_t_def) sorry 
    qed
  qed

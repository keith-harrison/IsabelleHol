theory Tree
imports Main Block Variables "HOL-Library.Tree"
begin
(* Block Tree.
   This file contains the definition of a treeType, which is the type of a blocktree. 
   First, the [valid_chain] predicate is defined and afterwards is the treeType defined. 
*)

(*Notation*)

definition correct_block :: "Block \<Rightarrow> bool" where
"correct_block bl = (if (bid bl = sl bl)  then True else False)"
  (*where "correct_block = Winner bid b sl b" done just saying that bid outweights slot*)

fun correct_blocks :: "Chain \<Rightarrow> bool" where
"correct_blocks [] = True"|
"correct_blocks (c#cs) = (if correct_block c then correct_blocks cs else False)"


definition linked :: "Block \<Rightarrow> Block \<Rightarrow> bool" where 
"linked b b' = (if pred b = HashB b' then True else False)"

value "linked \<lparr> sl = 5, txs = 123, pred = 1, bid = 123 \<rparr> \<lparr> sl = 5, txs = 123, pred = 0, bid = 123 \<rparr>"
value "linked \<lparr> sl = 5, txs = 123, pred = 0, bid = 123 \<rparr> \<lparr> sl = 5, txs = 123, pred = 1, bid = 123 \<rparr>"

fun properly_linked :: "Chain \<Rightarrow> bool" where
"properly_linked [] = False"|
"properly_linked [b] =(if pred b = 0 then True  else False)"|
"properly_linked (c#cs) = (if linked c (hd cs) then properly_linked cs  else False)"

(*Do it so sl are descending is a bit weird because they sort then lok for less than so feels like cheating*)
(*check all attributed are correct*)
fun descending :: "Chain \<Rightarrow> bool" where
"descending [] = True"|
"descending [b] = True"|
"descending (c#cs) = (if sl c > sl (hd cs) then descending cs  else False)"

definition valid_chain  :: "Chain \<Rightarrow> bool" where
"valid_chain c =(if properly_linked c \<and> correct_blocks c \<and> descending c then True else False)"
value "properly_linked [\<lparr> sl = 1, txs = 1, pred = 1, bid = 2 \<rparr>,\<lparr> sl=0, txs = 1, pred =0, bid = 1 \<rparr>]"
(*Chain goes  [bn,...,b3,b2,bgenesis]*)
value "valid_chain [\<lparr> sl = 1, txs = 1, pred = 1, bid = 1 \<rparr>,\<lparr> sl=0, txs = 1, pred =0, bid = 0 \<rparr>]"
definition "Block0 = \<lparr> sl=0, txs = 0, pred =0, bid = 0\<rparr>"
definition "Block1 = \<lparr> sl=1, txs = 1, pred =1, bid = 1\<rparr>"
(*might bite a bit later - GenesisNodes can exist mid tree*)
datatype T = Leaf | GenesisNode Block T T | Node Block T T   

(*concrete instance definition\<rightarrow>fun\<rightarrow>function power but also in inverse responsibility \<rightarrow> e.g. pattern matching/proving termination*)

fun allBlocks :: "T \<Rightarrow> BlockPool" where
"allBlocks (Node m l r) = allBlocks l@allBlocks r@ [m]"|
"allBlocks (GenesisNode m l r) = allBlocks l@allBlocks r@ [m]" |
"allBlocks Leaf = []"
value "allBlocks Leaf"
value "allBlocks (GenesisNode Block0 Leaf Leaf)"
(*functions ensure that pred is 0 ONLY for genesis node, and no genesis nodes exist in tree/no nodes at genesis location*)
fun validTree' :: "T \<Rightarrow> bool" where
"validTree' Leaf = True"|
"validTree' (Node m l r) = (if (pred m \<noteq> 0) then True \<and> validTree' l \<and> validTree' r else False) "|
"validTree' (GenesisNode m l r) = False"
fun validTree :: "T \<Rightarrow> bool" where
"validTree Leaf =False"|
"validTree (GenesisNode m l r) = (if (pred m = 0) then True \<and> validTree' l \<and> validTree' r else False)"|
"validTree (Node m l r) = False"

value "validTree Leaf"
value "validTree' Leaf"
value "validTree (Node Block0 Leaf Leaf)"
value "validTree (GenesisNode Block0 (Node Block1 Leaf Leaf) Leaf)"
value "allBlocks (GenesisNode Block0 (Node Block1 Leaf Leaf) Leaf)"

(*maybe want to ensure that allblocks returns unique/set*)
value "[a]@[]@[]@[1]" 
(* postorder search similar to allblocks 2 but given Node m l r and slot value how to check subtree l or r using \<lparr> \<rparr> and accessing sl*)
fun bestChain :: "Slot \<Rightarrow> T \<Rightarrow> Chain" where
"bestChain slotvalue (Node m l r) = (if slotvalue = sl m then (bestChain slotvalue l)@(bestChain slotvalue r)@[m] else []) "|
"bestChain slotvalue Leaf  = []"
(* similar to best chain but need to check sl value of block to put in correctly *)
(*extendtree - add to longest chain/e.g. left more trustworthy/right choice in context maybe depending on sl or bid *)
fun extendTree :: "T \<Rightarrow> Block \<Rightarrow> T" where
"extendTree (Node m l r) Bl = Node m (extendTree l Bl) r"|
"extendTree (Node m Leaf Leaf) Bl = Node m Bl Leaf "|
"extendTree Leaf Bl  = Node Bl Leaf Leaf"


(* all_tree0 T : @allBlocks T tree0  =i [:: GenesisBlock].*)
(*forall t b, allBlocks (extendTree t b) =i allBlocks t ++ [:: b]*)
(*forall s t, {subset (bestChain*)
(*forall t s, valid_chain (bestChain s t)*)
(*forall c s t, valid_chain c -> {subset c <= [seq b <- allBlocks t | sl b <= s]} -> |c| <= |bestChain s t|*)
(*forall s t, {subset (bestChain s t) <= [seq b <- allBlocks t | sl b <= s]}*)




end
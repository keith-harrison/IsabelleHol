theory Tree
imports Main Block Variables "HOL-Library.Tree"
begin
(* Block Tree.
   This file contains the definition of a treeType, which is the type of a blocktree. 
   First, the [valid_chain] predicate is defined and afterwards is the treeType defined. 
*)

(*Notation*)

definition correct_block :: "Block \<Rightarrow> bool" where
"correct_block bl = (if (bid bl \<ge> sl bl)  then True else False)"
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
value "valid_chain [\<lparr> sl = 1, txs = 1, pred = 1, bid = 2 \<rparr>,\<lparr> sl=0, txs = 1, pred =0, bid = 1 \<rparr>]"

datatype T = Leaf | Node Block T T
definition "tree0 = Node \<lparr> sl=0, txs = 1, pred =0, bid = 1 \<rparr> Leaf Leaf"
(*concrete instance definition\<rightarrow>fun\<rightarrow>function power but also in inverse responsibility \<rightarrow> e.g. pattern matching/proving termination*)


(*fun allBlocks :: "T \<Rightarrow> BlockPool" where
"allBlocks (Node m l r) =(if ((length r = 0) \<and> (isGen m = True))  then  [m]  else [])"|
"allBlocks Leaf = []"
*)
function allBlocks2 :: "T \<Rightarrow> BlockPool" where
"allBlocks2 (Node m l r) = allBlocks2 l@allBlocks2 r@ [m]"|
"allBlocks2 Leaf = []"

(* postorder search similar to allblocks 2 but given Node m l r and slot value how to check subtree l or r using \<lparr> \<rparr> and accessing sl*)
fun bestChain :: "Slot \<Rightarrow> T \<Rightarrow> Chain" where
"bestChain slotvalue (Node m l r) = []"|
"bestChain slotvalue Leaf  = []"
(* similar to best chain but need to check sl value of block to put in correctly *)
fun extendTree :: "T \<Rightarrow> Block \<Rightarrow> T" where
"extendTree (Node m l r) Bl = Leaf"|
"extendTree Leaf Bl  = Leaf"



(* all_tree0 T : @allBlocks T tree0  =i [:: GenesisBlock].*)
(*forall t b, allBlocks (extendTree t b) =i allBlocks t ++ [:: b]*)
(*forall s t, {subset (bestChain*)
(*forall t s, valid_chain (bestChain s t)*)
(*forall c s t, valid_chain c -> {subset c <= [seq b <- allBlocks t | sl b <= s]} -> |c| <= |bestChain s t|*)
(*forall s t, {subset (bestChain s t) <= [seq b <- allBlocks t | sl b <= s]}*)




end
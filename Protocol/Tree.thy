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

datatype T = Leaf | Node Block "T list"

type_synonym extendTree = "T \<Rightarrow> Block \<Rightarrow> T"
type_synonym bestChain = "Slot \<Rightarrow> T \<Rightarrow> Chain"

definition "x = Node \<lparr>sl = 0, txs=0, pred=0, bid = 0 \<rparr> []"
(*concrete instance definition\<rightarrow>fun\<rightarrow>function power but also in inverse responsibility \<rightarrow> e.g. pattern matching/proving termination*)

definition allBlocks x = 


(* basically saying if we flatten tree0 that it is a list of block 
so only contains a genesisblock
allBlocks tree0 =i [:: GenesisBlock] Instantiated*)

definition allBlocks :: "T \<Rightarrow> BlockPool" where
"allBlocks (Node Block) = [Block]"

(*forall t b, allBlocks (extendTree t b) =i allBlocks t ++ [:: b]*)

(*forall s t, {subset (bestChain*)

(*forall t s, valid_chain (bestChain s t)*)


(*forall c s t, valid_chain c -> {subset c <= [seq b <- allBlocks t | sl b <= s]} -> |c| <= |bestChain s t|*)

(*forall s t, {subset (bestChain s t) <= [seq b <- allBlocks t | sl b <= s]}*)




(*
 Notation class_of := mixin_of.
  Record type := Pack { sort : Type; class : class_of sort }.
    Coercion sort : type >-> Sortclass.
    Notation BlockTreeMixin := Mixin.
    Notation TreeType T m := (@Pack T m).
      Implicit Type (T : treeType).

      Definition extendTree {T} := extendTree (class T).
      Definition bestChain {T} := bestChain (class T).
      Definition allBlocks {T} := allBlocks (class T).
      Definition tree0 {T} := tree0 (class T).
Proofs
*)
end
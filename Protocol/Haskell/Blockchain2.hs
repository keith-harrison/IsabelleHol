{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Blockchain2(Hash, Block_ext, T, genBlock, tree0, block1, block2, block3,
               hashComparea, hashCompare, valid_blocks, valid_chain, best_c,
               allBlocksAppend, allBlocksa, valid_t, allBlocks, get_first,
               best_chain, extendTree, valid_chain_weak, valid_t_weak)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Option;
import qualified Product_Type;
import qualified List;
import qualified HOL;
import qualified Arith;

data Hash = H Arith.Nat Arith.Nat;

data Block_ext a = Block_ext Arith.Nat Arith.Nat Hash Arith.Nat a;

data T = Leaf | Node (Block_ext ()) T T;

genBlock :: Block_ext ();
genBlock =
  Block_ext Arith.Zero_nat Arith.Zero_nat (H Arith.Zero_nat Arith.Zero_nat)
    Arith.Zero_nat ();

tree0 :: T;
tree0 = Node genBlock Leaf Leaf;

block1 :: Block_ext ();
block1 =
  Block_ext Arith.one_nat Arith.one_nat (H Arith.Zero_nat Arith.Zero_nat)
    Arith.one_nat ();

block2 :: Block_ext ();
block2 =
  Block_ext (Arith.nat_of_num (Arith.Bit0 Arith.One)) Arith.Zero_nat
    (H Arith.one_nat Arith.one_nat) Arith.one_nat ();

block3 :: Block_ext ();
block3 =
  Block_ext (Arith.nat_of_num (Arith.Bit1 Arith.One)) Arith.Zero_nat
    (H (Arith.nat_of_num (Arith.Bit0 Arith.One)) Arith.one_nat) Arith.one_nat
    ();

equal_Hash :: Hash -> Hash -> Bool;
equal_Hash (H x1 x2) (H y1 y2) = Arith.equal_nat x1 y1 && Arith.equal_nat x2 y2;

equal_Block_ext :: forall a. (Eq a) => Block_ext a -> Block_ext a -> Bool;
equal_Block_ext (Block_ext sla txsa preda bida morea)
  (Block_ext sl txs pred bid more) =
  Arith.equal_nat sla sl &&
    Arith.equal_nat txsa txs &&
      equal_Hash preda pred && Arith.equal_nat bida bid && morea == more;

bid :: forall a. Block_ext a -> Arith.Nat;
bid (Block_ext sl txs pred bid more) = bid;

sl :: forall a. Block_ext a -> Arith.Nat;
sl (Block_ext sl txs pred bid more) = sl;

hashComparea :: Hash -> Block_ext () -> Bool;
hashComparea (H a b) bl1 =
  Arith.equal_nat a (sl bl1) && Arith.equal_nat b (bid bl1);

pred :: forall a. Block_ext a -> Hash;
pred (Block_ext sl txs pred bid more) = pred;

hashCompare :: Block_ext () -> Block_ext () -> Bool;
hashCompare bl1 bl2 = hashComparea (pred bl2) bl1;

valid_blocks :: Block_ext () -> Block_ext () -> Bool;
valid_blocks b1 b2 = hashCompare b2 b1 && Arith.less_nat (sl b2) (sl b1);

valid_chain :: [Block_ext ()] -> Bool;
valid_chain [] = False;
valid_chain [b1] = (if equal_Block_ext b1 genBlock then True else False);
valid_chain (b1 : b2 : c) =
  (if valid_blocks b1 b2 && not (equal_Block_ext b1 genBlock)
    then valid_chain (b2 : c) else False);

best_c ::
  Arith.Nat -> [[Block_ext ()]] -> Maybe ([Block_ext ()], (Arith.Nat, Bool));
best_c slot list =
  let {
    a = map (\ l -> (l, (sl (List.hd l), valid_chain l))) list;
  } in List.find (\ (_, (s, v)) -> v && Arith.less_eq_nat s slot) a;

allBlocksAppend :: Block_ext () -> [[Block_ext ()]] -> [[Block_ext ()]];
allBlocksAppend bl blP = map (\ bla -> bla ++ [bl]) blP;

allBlocksa :: T -> [[Block_ext ()]];
allBlocksa (Node m l r) =
  allBlocksAppend m (allBlocksa l) ++ allBlocksAppend m (allBlocksa r);
allBlocksa Leaf = [[]];

valid_t :: T -> Bool;
valid_t t = all valid_chain (allBlocksa t);

allBlocks :: T -> [Block_ext ()];
allBlocks (Node m l r) = allBlocks l ++ allBlocks r ++ [m];
allBlocks Leaf = [];

get_first :: Maybe ([Block_ext ()], (Arith.Nat, Bool)) -> [Block_ext ()];
get_first a = (case a of {
                Nothing -> [];
                Just aa -> fst aa;
              });

best_chain :: Arith.Nat -> T -> [Block_ext ()];
best_chain s Leaf = [];
best_chain Arith.Zero_nat (Node x l r) = [genBlock];
best_chain (Arith.Suc v) (Node x l r) =
  get_first (best_c (Arith.Suc v) (allBlocksa (Node x l r)));

extendTree :: T -> Block_ext () -> T;
extendTree (Node bl1 Leaf Leaf) bl2 =
  (if valid_blocks bl2 bl1 then Node bl1 (Node bl2 Leaf Leaf) Leaf
    else Node bl1 Leaf Leaf);
extendTree (Node bl1 (Node v va vb) Leaf) bl2 =
  (if valid_blocks bl2 bl1 then Node bl1 (Node v va vb) (Node bl2 Leaf Leaf)
    else Node bl1 (extendTree (Node v va vb) bl2) Leaf);
extendTree (Node bl1 Leaf (Node v va vb)) bl2 =
  (if valid_blocks bl2 bl1 then Node bl1 (Node bl2 Leaf Leaf) (Node v va vb)
    else Node bl1 Leaf (extendTree (Node v va vb) bl2));
extendTree (Node bl1 (Node v va vb) (Node vc vd ve)) bl2 =
  Node bl1 (extendTree (Node v va vb) bl2) (extendTree (Node vc vd ve) bl2);
extendTree Leaf bl2 = Leaf;

valid_chain_weak :: [Block_ext ()] -> Bool;
valid_chain_weak [] = False;
valid_chain_weak [b1] = True;
valid_chain_weak (b1 : b2 : c) =
  (if valid_blocks b1 b2 then valid_chain_weak (b2 : c) else False);

valid_t_weak :: T -> Bool;
valid_t_weak t = all valid_chain_weak (allBlocksa t);

}

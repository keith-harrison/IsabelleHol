{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell,AllowAmbiguousTypes,BlockArguments, UndecidableInstances, DeriveDataTypeable, DeriveGeneric, StandaloneDeriving, DeriveAnyClass #-}
module
  Blockchain(Hash, Block_ext, T, genBlock, tree0, hashComparea, hashCompare,
              valid_blocks, valid_chain, best_c, allBlocksAppend, allBlocksa,
              valid_t, block_eq, allBlocks, get_first, best_chain, extendTree,
              blockpool_eq, blocktree_eq, valid_chain_weak, valid_t_weak,blockpool_eq_set)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,Int,div,Show,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Option;
import qualified Set;
import qualified Product_Type;
import qualified List;
import qualified HOL;
import qualified Arith;
import GHC.Generics;
import Data.Maybe;
import Data.List;
import Control.Exception;
import Control.Monad;
import Test.QuickCheck;



data Hash = H Integer Integer deriving(Show);


equal_Hash :: Hash -> Hash -> Bool;
equal_Hash (H x1 x2) (H y1 y2) = Arith.equal_int x1 y1 && Arith.equal_int x2 y2;

data Block_ext a = Block_ext Integer Integer Hash Integer a deriving(Show);



equal_Block_ext :: forall a. (Eq a) => Block_ext a -> Block_ext a -> Bool;
equal_Block_ext (Block_ext sla txsa preda bida morea)
  (Block_ext sl txs pred bid more) =
  Arith.equal_int sla sl &&
    Arith.equal_int txsa txs &&
      equal_Hash preda pred && Arith.equal_int bida bid && morea == more;

instance (Eq a) => Eq (Block_ext a) where {
  a == b = equal_Block_ext a b;
};

data T = Leaf | Node (Block_ext ()) T T deriving(Show);




genBlock :: Block_ext ();
genBlock =
  Block_ext 0 0 (H 0 0) 0 ();

tree0 :: T;
tree0 = Node genBlock Leaf Leaf;

bid :: forall a. Block_ext a -> Integer;
bid (Block_ext sl txs pred bid more) = bid;

sl :: forall a. Block_ext a -> Integer;
sl (Block_ext sl txs pred bid more) = sl;

hashComparea :: Hash -> Block_ext () -> Bool;
hashComparea (H a b) bl1 =
  Arith.equal_int a (sl bl1) && Arith.equal_int b (bid bl1);

pred :: forall a. Block_ext a -> Hash;
pred (Block_ext sl txs pred bid more) = pred;

hashCompare :: Block_ext () -> Block_ext () -> Bool;
hashCompare bl1 bl2 = hashComparea (pred bl2) bl1;

valid_blocks :: Block_ext () -> Block_ext () -> Bool;
valid_blocks b1 b2 = hashCompare b2 b1 && Arith.less_int (sl b2) (sl b1);

valid_chain :: [Block_ext ()] -> Bool;
valid_chain [] = False;
valid_chain [b1] = (if equal_Block_ext b1 genBlock then True else False);
valid_chain (b1 : b2 : c) =
  (if valid_blocks b1 b2 && not (equal_Block_ext b1 genBlock)
    then valid_chain (b2 : c) else False);
blockpool_eq_set :: [Block_ext ()] -> [Block_ext ()] -> Bool;
blockpool_eq_set bpl1 bpl2 = Set.equal_set (Set.Set bpl1) (Set.Set bpl2);

best_c ::
  Integer -> [[Block_ext ()]] -> Maybe ([Block_ext ()], (Integer, Bool));
best_c slot list =
  let {
    a = map (\ l -> (l, (sl (List.hd l), valid_chain l))) list;
  } in List.find (\ (_, (s, v)) -> v && Arith.less_eq_int s slot) a;

allBlocksAppend :: Block_ext () -> [[Block_ext ()]] -> [[Block_ext ()]];
allBlocksAppend bl blP = map (\ bla -> bla ++ [bl]) blP;

allBlocksa :: T -> [[Block_ext ()]];
allBlocksa (Node m l r) =
  allBlocksAppend m (allBlocksa l) ++ allBlocksAppend m (allBlocksa r);
allBlocksa Leaf = [[]];

valid_t :: T -> Bool;
valid_t t = all valid_chain (allBlocksa t);

block_eq :: Block_ext () -> Block_ext () -> Bool;
block_eq b1 b2 = equal_Block_ext b1 b2;

allBlocks :: T -> [Block_ext ()];
allBlocks (Node m l r) = allBlocks l ++ allBlocks r ++ [m];
allBlocks Leaf = [];

get_first :: Maybe ([Block_ext ()], (Integer, Bool)) -> [Block_ext ()];
get_first a = (case a of {
                Nothing -> [];
                Just aa -> fst aa;
              });

best_chain :: Integer -> T -> [Block_ext ()];
best_chain s Leaf = [];
best_chain s (Node x l r) =
  (if Arith.less_int 0 s
    then get_first (best_c s (allBlocksa (Node x l r))) else [genBlock]);

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

blockpool_eq :: [Block_ext ()] -> [Block_ext ()] -> Bool;
blockpool_eq bpl1 bpl2 = bpl1 == bpl2;

blocktree_eq :: T -> T -> Bool;
blocktree_eq (Node t1 t2 t3) (Node t_1 t_2 t_3) =
  block_eq t1 t_1 && blocktree_eq t2 t_2 && blocktree_eq t3 t_3;
blocktree_eq Leaf Leaf = True;
blocktree_eq (Node t1 t2 t3) Leaf = False;
blocktree_eq Leaf (Node uu uv uw) = False;

valid_chain_weak :: [Block_ext ()] -> Bool;
valid_chain_weak [] = False;
valid_chain_weak [b1] = True;
valid_chain_weak (b1 : b2 : c) =
  (if valid_blocks b1 b2 then valid_chain_weak (b2 : c) else False);

valid_t_weak :: T -> Bool;
valid_t_weak t = all valid_chain_weak (allBlocksa t);


--Tests getting around 10000/60000 tests

{- 
instance Arbitrary (T) where{
  arbitrary = (sized arbTree1);
};
arbTree1 :: Int -> Gen(T);
arbTree1 0 = do{
    sla1 <- choose (0);
    bida1 <- choose (0);
    sla <- choose (0);
    txsa <- choose(0,1);
    bida <- choose (0);
    morea <- arbitrary;
    block <- frequency[(1,return genBlock),(10,return genBlock)];
    return (Node block Leaf Leaf);};
arbTree1 n = do{
    block <- frequency[(1,return genBlock ),(10,return genBlock)];
    let bush = sized arbTree; in frequency[(1, return (Node block Leaf Leaf)),(3, return (Node block bush bush))]; };
-}
-- `suchThat` valid t - to include valid t precondition 

instance Arbitrary (Hash) where{
  arbitrary = do
    sla <- choose (0,4);
    bida <- choose (0,4);
    return (H sla bida);
};

instance Arbitrary a => Arbitrary (Block_ext a) where{
  arbitrary = do
    sla <- choose (0,4);
    txsa <- choose(0,4);
    preda <- arbitrary;
    bida <- choose (0,4);
    morea <- arbitrary;
    return (Block_ext sla txsa preda bida morea);
};
instance Arbitrary (T) where {
arbitrary = (sized arbTree);
};

arbTree :: Int -> Gen (T);
arbTree 0 = do{bl <- arbitrary; return (Node bl Leaf Leaf);};
arbTree n = do{bl <- arbitrary; let bush = arbTree (div n 2); 
in frequency[(1, return (Node bl Leaf Leaf)),(3, liftM3 Node arbitrary bush bush)]; };
}



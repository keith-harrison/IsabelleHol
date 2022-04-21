{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# HLINT ignore "Redundant ==" #-}
module Lib
    ( someFunc
    ) where
import Test.QuickCheck (quickCheck, verboseCheckWith,maxSize, stdArgs,quickCheckWith,maxSuccess);
import qualified Option;
import qualified Product_Type;
import qualified List;
import qualified HOL;
import qualified Arith;
import qualified Blockchain(Hash, Block_ext, T, genBlock, tree0, hashComparea, hashCompare,
              valid_blocks, valid_chain, best_c, allBlocksAppend, allBlocksa,
              valid_t, block_eq, allBlocks, get_first, best_chain, extendTree,
              blockpool_eq, blocktree_eq, valid_chain_weak, valid_t_weak,blockpool_eq_set)
import Test.QuickCheck.Property
import qualified Data.Set as Set
import GHC.Generics
import Data.Maybe
import Data.List
import Control.Exception
import Control.Monad
import Test.SmallCheck(smallCheck)


prop_evenNumberPlusOneIsOdd :: Integer -> Property
prop_evenNumberPlusOneIsOdd x = even x ==> odd (x + 1)

prop_overlySpecific :: Integer -> Integer -> Property
prop_overlySpecific x y = x == 0 ==> x * y == 0
 
prop_tree :: Blockchain.T -> Blockchain.Block_ext ()-> Property
prop_tree t b = (not (Blockchain.blocktree_eq (Blockchain.extendTree t b) t)) ==> (Blockchain.blockpool_eq_set (Blockchain.allBlocks (Blockchain.extendTree t b)) ((Blockchain.allBlocks t)++[b]))

prop_valid_chain :: Integer -> Blockchain.T -> Property
prop_valid_chain s t = ((Blockchain.valid_t t)) ==> Blockchain.valid_chain(Blockchain.best_chain s t) == True


{- Test 1
Lemma one extension adds one to the set of allblocks in the tree
    "(extendTree t b ≠ t) ⟹ set (allBlocks (extendTree t b)) =set ([b]@ allBlocks t)" -}
someFunc :: IO ()
someFunc = quickCheckWith (Test.QuickCheck.stdArgs {maxSuccess = 10000}) prop_tree


{- Test 2
Lemma two best chain is a valid chain
    assumes"s≥0∧valid_t t" shows "valid_chain_(best_chain s t) -}
--someFunc :: IO ()
--someFunc = verboseCheckWith (Test.QuickCheck.stdArgs {maxSuccess = 100 }) prop_valid_chain



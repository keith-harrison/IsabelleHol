module Lib
    ( someFunc
    ) where
import Test.QuickCheck (quickCheck, verboseCheck);
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
prop_evenNumberPlusOneIsOdd :: Integer -> Property
prop_evenNumberPlusOneIsOdd x = even x ==> odd (x + 1)

prop_overlySpecific :: Integer -> Integer -> Property
prop_overlySpecific x y = x == 0 ==> x * y == 0
 
prop_tree :: Blockchain.T -> Blockchain.Block_ext ()-> Property
prop_tree t b = (not (Blockchain.blocktree_eq (Blockchain.extendTree t b) t)) ==> (Blockchain.blockpool_eq_set (Blockchain.allBlocks (Blockchain.extendTree t b)) ((Blockchain.allBlocks t)++[b]))

prop_valid_chain :: Integer -> Blockchain.T -> Property
prop_valid_chain s t = ((Blockchain.valid_t t)) ==> Blockchain.valid_chain(Blockchain.best_chain s t) == True


-- Lemma one extension adds one to the set of allblocks in the tree
-- "(extendTree t b ≠ t) ⟹ set (allBlocks (extendTree t b)) =set ([b]@ allBlocks t)"
-- Lemma two best chain is a valid chain
-- assumes"s≥0∧valid_t t" shows "valid_chain_(best_chain s t)

someFunc :: IO ()
someFunc = quickCheck (prop_tree);

-- Node (Block_ext 1 1 (H 1 2) 1 ()) Leaf Leaf
-- Block_ext 2 1 (H 1 1) 1 ()

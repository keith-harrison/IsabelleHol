module Lib
    ( someFunc
    ) where
import Test.QuickCheck (quickCheck);
import qualified Option;
import qualified Product_Type;
import qualified List;
import qualified HOL;
import qualified Arith;
import qualified Blockchain(Hash, Block_ext, T, genBlock, tree0, block1, block2, block3,
               hashComparea, hashCompare, valid_blocks, valid_chain, best_c,
               allBlocksAppend, allBlocksa, valid_t, allBlocks, get_first,
               best_chain, extendTree, valid_chain_weak, valid_t_weak);
someFunc :: IO ()
someFunc = quickCheck Arith.one_nat


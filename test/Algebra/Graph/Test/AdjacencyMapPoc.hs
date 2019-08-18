{-# LANGUAGE OverloadedLists #-}
-----------------------------------------------------------------------------
-- |
-- Module     : Algebra.Graph.Test.AdjacencyMap
-- Copyright  : (c) Andrey Mokhov 2016-2018
-- License    : MIT (see the file LICENSE)
-- Maintainer : andrey.mokhov@gmail.com
-- Stability  : experimental
--
-- Testsuite for "Algebra.Graph.AdjacencyMap".
-----------------------------------------------------------------------------
module Algebra.Graph.Test.AdjacencyMapPoc (
    -- * Testsuite
    testAdjacencyMapPoc
    ) where

import Data.List.NonEmpty

import Algebra.Graph.AdjacencyMapPoc
-- import Algebra.Graph.AdjacencyMap.Algorithm
import Algebra.Graph.Test
import Algebra.Graph.Test.API (toIntAPI, adjacencyMapPocAPI)
import Algebra.Graph.Test.Generic

-- import qualified Algebra.Graph.NonEmpty.AdjacencyMap as NonEmpty

tPoly :: Testsuite AdjacencyMapPoc Ord
tPoly = ("AdjacencyMapPoc.", adjacencyMapPocAPI)

t :: TestsuiteInt AdjacencyMapPoc
t = fmap toIntAPI tPoly

type AI = AdjacencyMapPoc Int


testTransformations' :: TestsuiteInt g -> IO ()
testTransformations' = mconcat [ testRemoveVertex
                              , testRemoveEdge
                              , testReplaceVertex
                              , testMergeVertices
                            --   , testTranspose
                              , testGmap ]
                            --   , testInduce ]

testAdjacencyMapPoc :: IO ()
testAdjacencyMapPoc = do
    putStrLn "\n============ AdjacencyMapPoc ============"
    test "Axioms of graphs" (axioms :: GraphTestsuite AI)

    -- testConsistent        t
    -- testShow              t
    testBasicPrimitives   t
    -- testFromAdjacencySets t
    -- testIsSubgraphOf      t
    -- testToGraph           t
    -- testGraphFamilies     t
    -- testTransformations   t
    testTransformations' t
    -- testRelational        t
    -- testBox               tPoly
    -- testBfsForest         t
    -- testBfsForestFrom     t
    -- testBfs               t
    -- testDfsForest         t
    -- testDfsForestFrom     t
    -- testDfs               t
    -- testReachable         t
    -- testTopSort           t
    -- testIsAcyclic         t
    -- testIsDfsForestOf     t
    -- testIsTopSortOf       t
    -- testInduceJust        tPoly

    -- putStrLn "\n============ AdjacencyMapPoc.scc ============"
    -- test "scc empty               == empty" $
    --       scc (empty :: AI)       == empty

    -- test "scc (vertex x)          == vertex (NonEmpty.vertex x)" $ \(x :: Int) ->
    --       scc (vertex x)          == vertex (NonEmpty.vertex x)

    -- test "scc (edge 1 1)          == vertex (NonEmpty.edge 1 1)" $
    --       scc (edge 1 1 :: AI)    == vertex (NonEmpty.edge 1 1)

    -- test "scc (edge 1 2)          == edge   (NonEmpty.vertex 1) (NonEmpty.vertex 2)" $
    --       scc (edge 1 2 :: AI)    == edge   (NonEmpty.vertex 1) (NonEmpty.vertex 2)

    -- test "scc (circuit (1:xs))    == vertex (NonEmpty.circuit1 (1 :| xs))" $ \(xs :: [Int]) ->
    --       scc (circuit (1:xs))    == vertex (NonEmpty.circuit1 (1 :| xs))

    -- test "scc (3 * 1 * 4 * 1 * 5) == <correct result>" $
    --       scc (3 * 1 * 4 * 1 * 5) == edges [ (NonEmpty.vertex 3       , NonEmpty.vertex  5      )
    --                                        , (NonEmpty.vertex 3       , NonEmpty.clique1 [1,4,1])
    --                                        , (NonEmpty.clique1 [1,4,1], NonEmpty.vertex  (5 :: Int)) ]

    -- test "isAcyclic . scc == const True" $ \(x :: AI) ->
    --       (isAcyclic . scc) x == (const True) x

    -- test "isAcyclic x     == (scc x == gmap NonEmpty.vertex x)" $ \(x :: AI) ->
    --       isAcyclic x     == (scc x == gmap NonEmpty.vertex x)
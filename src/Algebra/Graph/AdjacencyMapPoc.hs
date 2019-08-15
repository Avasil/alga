{-# LANGUAGE DeriveGeneric #-}
-----------------------------------------------------------------------------
-- |
-- Module     : Algebra.Graph.AdjacencyMapPoc
-- Copyright  : (c) Andrey Mokhov 2016-2019
-- License    : MIT (see the file LICENSE)
-- Maintainer : andrey.mokhov@gmail.com
-- Stability  : experimental
--
-- __Alga__ is a library for algebraic construction and manipulation of graphs
-- in Haskell. See <https://github.com/snowleopard/alga-paper this paper> for the
-- motivation behind the library, the underlying theory, and implementation details.
--
-- This module defines the 'AdjacencyMapPoc' data type and associated functions.
-- See "Algebra.Graph.AdjacencyMapPoc.Algorithm" for implementations of basic graph
-- algorithms. 'AdjacencyMapPoc' is an instance of the 'C.Graph' type class, which
-- can be used for polymorphic graph construction and manipulation.
-- "Algebra.Graph.AdjacencyIntMap" defines adjacency maps specialised to graphs
-- with @Int@ vertices.
-----------------------------------------------------------------------------
module Algebra.Graph.AdjacencyMapPoc (
    -- * Data structure
    AdjacencyMapPoc,

    -- -- * Basic graph construction primitives
    empty, vertex, edge, overlay, connect, edges,
    -- empty, vertex, edge, overlay, connect, vertices, edges, overlays, connects,

    -- -- * Relations on graphs
    -- isSubgraphOf,

    -- -- * Graph properties
    isEmpty, hasVertex, hasEdge, vertexCount, edgeCount, vertexList, edgeList
    -- adjacencyList, vertexSet, edgeSet, preSet, postSet,

    -- -- * Standard families of graphs
    -- path, circuit, clique, biclique, star, stars, fromAdjacencySets, tree,
    -- forest,

    -- -- * Graph transformation
    -- removeVertex, removeEdge, replaceVertex, mergeVertices, transpose, gmap,
    -- induce, induceJust,

    -- -- * Graph composition
    -- compose, box,

    -- -- * Relational operations
    -- closure, reflexiveClosure, symmetricClosure, transitiveClosure,

    -- -- * Miscellaneous
    -- consistent
    ) where

import Control.DeepSeq
-- import Data.List ((\\))
import Data.Map.Strict (Map)
-- import Data.Monoid
-- import Data.Set (Set)
-- import Data.Tree
import GHC.Generics
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Maybe      as Maybe
-- import qualified Data.Set        as Set
import qualified Algebra.Graph.AdjacencyIntMap as AIM

{-| The 'AdjacencyMapPoc' data type represents a graph by a map of vertices to
their adjacency sets. We define a 'Num' instance as a convenient notation for
working with graphs:

    > 0           == vertex 0
    > 1 + 2       == overlay (vertex 1) (vertex 2)
    > 1 * 2       == connect (vertex 1) (vertex 2)
    > 1 + 2 * 3   == overlay (vertex 1) (connect (vertex 2) (vertex 3))
    > 1 * (2 + 3) == connect (vertex 1) (overlay (vertex 2) (vertex 3))

__Note:__ the 'Num' instance does not satisfy several "customary laws" of 'Num',
which dictate that 'fromInteger' @0@ and 'fromInteger' @1@ should act as
additive and multiplicative identities, and 'negate' as additive inverse.
Nevertheless, overloading 'fromInteger', '+' and '*' is very convenient when
working with algebraic graphs; we hope that in future Haskell's Prelude will
provide a more fine-grained class hierarchy for algebraic structures, which we
would be able to utilise without violating any laws.

The 'Show' instance is defined using basic graph construction primitives:

@show (empty     :: AdjacencyMapPoc Int) == "empty"
show (1         :: AdjacencyMapPoc Int) == "vertex 1"
show (1 + 2     :: AdjacencyMapPoc Int) == "vertices [1,2]"
show (1 * 2     :: AdjacencyMapPoc Int) == "edge 1 2"
show (1 * 2 * 3 :: AdjacencyMapPoc Int) == "edges [(1,2),(1,3),(2,3)]"
show (1 * 2 + 3 :: AdjacencyMapPoc Int) == "overlay (vertex 3) (edge 1 2)"@

The 'Eq' instance satisfies all axioms of algebraic graphs:

    * 'overlay' is commutative and associative:

        >       x + y == y + x
        > x + (y + z) == (x + y) + z

    * 'connect' is associative and has 'empty' as the identity:

        >   x * empty == x
        >   empty * x == x
        > x * (y * z) == (x * y) * z

    * 'connect' distributes over 'overlay':

        > x * (y + z) == x * y + x * z
        > (x + y) * z == x * z + y * z

    * 'connect' can be decomposed:

        > x * y * z == x * y + x * z + y * z

The following useful theorems can be proved from the above set of axioms.

    * 'overlay' has 'empty' as the identity and is idempotent:

        >   x + empty == x
        >   empty + x == x
        >       x + x == x

    * Absorption and saturation of 'connect':

        > x * y + x + y == x * y
        >     x * x * x == x * x

When specifying the time and memory complexity of graph algorithms, /n/ and /m/
will denote the number of vertices and edges in the graph, respectively.

The total order on graphs is defined using /size-lexicographic/ comparison:

* Compare the number of vertices. In case of a tie, continue.
* Compare the sets of vertices. In case of a tie, continue.
* Compare the number of edges. In case of a tie, continue.
* Compare the sets of edges.

Here are a few examples:

@'vertex' 1 < 'vertex' 2
'vertex' 3 < 'edge' 1 2
'vertex' 1 < 'edge' 1 1
'edge' 1 1 < 'edge' 1 2
'edge' 1 2 < 'edge' 1 1 + 'edge' 2 2
'edge' 1 2 < 'edge' 1 3@

Note that the resulting order refines the 'isSubgraphOf' relation and is
compatible with 'overlay' and 'connect' operations:

@'isSubgraphOf' x y ==> x <= y@

@'empty' <= x
x     <= x + y
x + y <= x * y@
-}

data AdjacencyMapPoc a = AM
    { graph :: AIM.AdjacencyIntMap
    , valueMap :: IntMap a
    , indexMap :: Map a Int } deriving (Generic)

value :: AdjacencyMapPoc a -> Int -> Maybe a
value g i = IntMap.lookup i (valueMap g)

index :: Ord a => AdjacencyMapPoc a -> a -> Maybe Int
index g a = Map.lookup a (indexMap g)

instance Eq (AdjacencyMapPoc a) where
    (==) x y = (==) (graph x) (graph y) -- todo: needs to convert mappings

instance Ord (AdjacencyMapPoc a) where
    compare x y = compare (graph x) (graph y) -- todo: needs to convert mappings

-- instance (Ord a, Show a) => Show (AdjacencyMapPoc a) where
--     showsPrec p am@(AdjacencyMapPoc g _ _)
--         | null vs    = showString "empty"
--         | null es    = showParen (p > 10) $ vshow vs
--         | vs == used = showParen (p > 10) $ eshow es
--         | otherwise  = showParen (p > 10) $ showString "overlay ("
--                      . vshow (vs \\ used) . showString ") ("
--                      . eshow es . showString ")"
--       where
--         vs             = vertexList am
--         es             = edgeList am
--         vshow [x]      = showString "vertex "   . showsPrec 11 x
--         vshow xs       = showString "vertices " . showsPrec 11 xs
--         eshow [(x, y)] = showString "edge "     . showsPrec 11 x .
--                          showString " "         . showsPrec 11 y
--         eshow xs       = showString "edges "    . showsPrec 11 xs
--         used           = Set.toAscList (referredToVertexSet m)

-- | __Note:__ this does not satisfy the usual ring laws; see 'AdjacencyMapPoc'
-- for more details.
instance (Ord a, Num a) => Num (AdjacencyMapPoc a) where
    fromInteger = vertex . fromInteger
    (+)         = overlay
    (*)         = connect
    signum      = const empty
    abs         = id
    negate      = id

instance NFData a => NFData (AdjacencyMapPoc a) where
    rnf (AM a b c) = rnf a `seq` rnf b `seq` rnf c

-- -- | Construct the /empty graph/.
-- -- Complexity: /O(1)/ time and memory.
-- --
-- -- @
-- -- 'isEmpty'     empty == True
-- -- 'hasVertex' x empty == False
-- -- 'vertexCount' empty == 0
-- -- 'edgeCount'   empty == 0
-- -- @
empty :: AdjacencyMapPoc a
empty = AM AIM.empty IntMap.empty Map.empty
{-# NOINLINE [1] empty #-}

-- -- | Construct the graph comprising /a single isolated vertex/.
-- -- Complexity: /O(1)/ time and memory.
-- --
-- -- @
-- -- 'isEmpty'     (vertex x) == False
-- -- 'hasVertex' x (vertex x) == True
-- -- 'vertexCount' (vertex x) == 1
-- -- 'edgeCount'   (vertex x) == 0
-- -- @
vertex :: a -> AdjacencyMapPoc a
vertex a = AM (AIM.vertex 0) newValue newIndex
    where 
        newValue = IntMap.singleton 0 a
        newIndex = Map.singleton a 0
{-# NOINLINE [1] vertex #-}

-- -- | Construct the graph comprising /a single edge/.
-- -- Complexity: /O(1)/ time, memory.
-- --
-- -- @
-- -- edge x y               == 'connect' ('vertex' x) ('vertex' y)
-- -- 'hasEdge' x y (edge x y) == True
-- -- 'edgeCount'   (edge x y) == 1
-- -- 'vertexCount' (edge 1 1) == 1
-- -- 'vertexCount' (edge 1 2) == 2
-- -- @
edge :: Ord a => a -> a -> AdjacencyMapPoc a
edge x y | x == y    = AM  (AIM.edge 0 0) newValue newIndex
         | otherwise = AM  (AIM.edge 0 1) newValue' newIndex'
    where 
        newValue  = IntMap.singleton 0 x
        newIndex  = Map.singleton x 0
        newValue' = IntMap.fromDistinctAscList [(0, x), (1, y)]
        newIndex' = Map.fromList [(x, 0), (y, 1)]

-- | /Overlay/ two graphs. This is a commutative, associative and idempotent
-- operation with the identity 'empty'.
-- Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
--
-- @
-- 'isEmpty'     (overlay x y) == 'isEmpty'   x   && 'isEmpty'   y
-- 'hasVertex' z (overlay x y) == 'hasVertex' z x || 'hasVertex' z y
-- 'vertexCount' (overlay x y) >= 'vertexCount' x
-- 'vertexCount' (overlay x y) <= 'vertexCount' x + 'vertexCount' y
-- 'edgeCount'   (overlay x y) >= 'edgeCount' x
-- 'edgeCount'   (overlay x y) <= 'edgeCount' x   + 'edgeCount' y
-- 'vertexCount' (overlay 1 2) == 2
-- 'edgeCount'   (overlay 1 2) == 0
-- @
overlay :: Ord a => AdjacencyMapPoc a -> AdjacencyMapPoc a -> AdjacencyMapPoc a
overlay g1 g2 = AM (AIM.overlay (graph g1) newGraph) newValue newIndex
    where 
        f nodes n = 
            foldr (\(v :: Int) (valuePairs :: IntMap a, indexPairs :: Map a Int, n) -> 
                let maybeA = IntMap.lookup v valuePairs
                    (newN, newValuePairs, newIndexPairs) = Maybe.fromMaybe 
                        (Maybe.maybe (n, valuePairs, indexPairs) (\a -> (n + 1, IntMap.insert n a valuePairs, Map.insert a n indexPairs)) (value g2 v))
                        (maybeA >>= (\newA -> fmap (\oldA -> 
                            if newA == oldA
                                then (n, valuePairs, indexPairs) 
                                else (n + 1, IntMap.insert n oldA valuePairs, Map.insert oldA n indexPairs))
                            (value g2 v)))
                in (newValuePairs, newIndexPairs, newN))
                (valueMap g1, indexMap g1, n)
                nodes
        n = AIM.vertexCount (graph g1)
        (newValue, newIndex, _) = f (AIM.vertexList (graph g2)) n
        newGraph = AIM.gmap (\v -> Maybe.fromMaybe v (value g2 v >>= (`Map.lookup` newIndex))) (graph g2)
{-# NOINLINE [1] overlay #-}

-- -- | /Connect/ two graphs. This is an associative operation with the identity
-- -- 'empty', which distributes over 'overlay' and obeys the decomposition axiom.
-- -- Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory. Note that the
-- -- number of edges in the resulting graph is quadratic with respect to the number
-- -- of vertices of the arguments: /m = O(m1 + m2 + n1 * n2)/.
-- --
-- -- @
-- -- 'isEmpty'     (connect x y) == 'isEmpty'   x   && 'isEmpty'   y
-- -- 'hasVertex' z (connect x y) == 'hasVertex' z x || 'hasVertex' z y
-- -- 'vertexCount' (connect x y) >= 'vertexCount' x
-- -- 'vertexCount' (connect x y) <= 'vertexCount' x + 'vertexCount' y
-- -- 'edgeCount'   (connect x y) >= 'edgeCount' x
-- -- 'edgeCount'   (connect x y) >= 'edgeCount' y
-- -- 'edgeCount'   (connect x y) >= 'vertexCount' x * 'vertexCount' y
-- -- 'edgeCount'   (connect x y) <= 'vertexCount' x * 'vertexCount' y + 'edgeCount' x + 'edgeCount' y
-- -- 'vertexCount' (connect 1 2) == 2
-- -- 'edgeCount'   (connect 1 2) == 1
-- -- @
connect :: Ord a => AdjacencyMapPoc a -> AdjacencyMapPoc a -> AdjacencyMapPoc a
connect g1 g2 = AM (AIM.connect (graph g1) newGraph) newValue newIndex
    where 
        f nodes n = 
            foldr (\(v :: Int) (valuePairs :: IntMap a, indexPairs :: Map a Int, n) -> 
                let maybeA = IntMap.lookup v valuePairs
                    (newN, newValuePairs, newIndexPairs) = Maybe.fromMaybe 
                        (Maybe.maybe (n, valuePairs, indexPairs) (\a -> (n + 1, IntMap.insert n a valuePairs, Map.insert a n indexPairs)) (value g2 v))
                        (maybeA >>= (\newA -> fmap (\oldA -> 
                            if newA == oldA
                                then (n, valuePairs, indexPairs) 
                                else (n + 1, IntMap.insert n oldA valuePairs, Map.insert oldA n indexPairs))
                            (value g2 v)))
                in (newValuePairs, newIndexPairs, newN))
                (valueMap g1, indexMap g1, n)
                nodes
        n = AIM.vertexCount (graph g1)
        (newValue, newIndex, _) = f (AIM.vertexList (graph g2)) n
        newGraph = AIM.gmap (\v -> Maybe.fromMaybe v (value g2 v >>= (`Map.lookup` newIndex))) (graph g2)
{-# NOINLINE [1] connect #-}

-- -- -- | Construct the graph comprising a given list of isolated vertices.
-- -- -- Complexity: /O(L * log(L))/ time and /O(L)/ memory, where /L/ is the length
-- -- -- of the given list.
-- -- --
-- -- -- @
-- -- -- vertices []            == 'empty'
-- -- -- vertices [x]           == 'vertex' x
-- -- -- 'hasVertex' x . vertices == 'elem' x
-- -- -- 'vertexCount' . vertices == 'length' . 'Data.List.nub'
-- -- -- 'vertexSet'   . vertices == Set.'Set.fromList'
-- -- -- @
-- -- vertices :: Ord a => [a] -> AdjacencyMapPoc a
-- -- vertices = AdjacencyMapPoc . Map.fromList . map (\x -> (x, Set.empty))
-- -- {-# NOINLINE [1] vertices #-}

-- -- -- | Construct the graph from a list of edges.
-- -- -- Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
-- -- --
-- -- -- @
-- -- -- edges []          == 'empty'
-- -- -- edges [(x,y)]     == 'edge' x y
-- -- -- 'edgeCount' . edges == 'length' . 'Data.List.nub'
-- -- -- 'edgeList' . edges  == 'Data.List.nub' . 'Data.List.sort'
-- -- -- @
edges :: Ord a => [(a, a)] -> AdjacencyMapPoc a
edges es = AM (AIM.edges newEdges) newValue newIndex
    where 
        (newEdges, newValue, newIndex, _) = foldr (\(from, to) (newEdges, valueMap, indexMap, n) -> 
            finalResult from to valueMap indexMap n newEdges) 
            ([], IntMap.empty, Map.empty, 0)
            es
        -- (Maybe Int, newIndexMap)
        newMapping a indexMap n = Map.insertLookupWithKey f a n indexMap
        f _ _ oldValue = oldValue
        newN (Just _) n = n
        newN Nothing  n = n + 1
        updateValue (Just n) _ _ valueMap = (n, valueMap)
        updateValue _        a n valueMap = (n, IntMap.insert n a valueMap)

        costam v valueMap indexMap n = let (oldInt, newIndexMap) = newMapping v indexMap n
                                           (newInt, newValueMap) = updateValue oldInt v n valueMap
                                       in  (newInt, newValueMap, newIndexMap, newN oldInt n)
        finalResult from to valueMap indexMap n lastEdges = let (from', valueMap', indexMap', n') = costam from valueMap indexMap n
                                                                (to', valueMap'', indexMap'', n'') = costam to valueMap' indexMap' n'
                                                            in  ((from', to') : lastEdges, valueMap'', indexMap'', n'')
-- -- -- | Overlay a given list of graphs.
-- -- -- Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
-- -- --
-- -- -- @
-- -- -- overlays []        == 'empty'
-- -- -- overlays [x]       == x
-- -- -- overlays [x,y]     == 'overlay' x y
-- -- -- overlays           == 'foldr' 'overlay' 'empty'
-- -- -- 'isEmpty' . overlays == 'all' 'isEmpty'
-- -- -- @
-- -- overlays :: Ord a => [AdjacencyMapPoc a] -> AdjacencyMapPoc a
-- -- overlays = AM . Map.unionsWith Set.union . map AdjacencyMapPoc
-- -- {-# NOINLINE overlays #-}

-- -- -- | Connect a given list of graphs.
-- -- -- Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
-- -- --
-- -- -- @
-- -- -- connects []        == 'empty'
-- -- -- connects [x]       == x
-- -- -- connects [x,y]     == 'connect' x y
-- -- -- connects           == 'foldr' 'connect' 'empty'
-- -- -- 'isEmpty' . connects == 'all' 'isEmpty'
-- -- -- @
-- -- connects :: Ord a => [AdjacencyMapPoc a] -> AdjacencyMapPoc a
-- -- connects = foldr connect empty
-- -- {-# NOINLINE connects #-}

-- -- -- | The 'isSubgraphOf' function takes two graphs and returns 'True' if the
-- -- -- first graph is a /subgraph/ of the second.
-- -- -- Complexity: /O((n + m) * log(n))/ time.
-- -- --
-- -- -- @
-- -- -- isSubgraphOf 'empty'         x             ==  True
-- -- -- isSubgraphOf ('vertex' x)    'empty'         ==  False
-- -- -- isSubgraphOf x             ('overlay' x y) ==  True
-- -- -- isSubgraphOf ('overlay' x y) ('connect' x y) ==  True
-- -- -- isSubgraphOf ('path' xs)     ('circuit' xs)  ==  True
-- -- -- isSubgraphOf x y                         ==> x <= y
-- -- -- @
-- -- isSubgraphOf :: Ord a => AdjacencyMapPoc a -> AdjacencyMapPoc a -> Bool
-- -- isSubgraphOf (AM x) (AM y) = Map.isSubmapOfBy Set.isSubsetOf x y

-- -- -- | Check if a graph is empty.
-- -- -- Complexity: /O(1)/ time.
-- -- --
-- -- -- @
-- -- -- isEmpty 'empty'                       == True
-- -- -- isEmpty ('overlay' 'empty' 'empty')       == True
-- -- -- isEmpty ('vertex' x)                  == False
-- -- -- isEmpty ('removeVertex' x $ 'vertex' x) == True
-- -- -- isEmpty ('removeEdge' x y $ 'edge' x y) == False
-- -- -- @
isEmpty :: AdjacencyMapPoc a -> Bool
isEmpty x = AIM.isEmpty (graph x)

-- -- -- | Check if a graph contains a given vertex.
-- -- -- Complexity: /O(log(n))/ time.
-- -- --
-- -- -- @
-- -- -- hasVertex x 'empty'            == False
-- -- -- hasVertex x ('vertex' x)       == True
-- -- -- hasVertex 1 ('vertex' 2)       == False
-- -- -- hasVertex x . 'removeVertex' x == 'const' False
-- -- -- @
hasVertex :: Ord a => a -> AdjacencyMapPoc a -> Bool
hasVertex a g = Maybe.isJust (index g a)

-- -- -- | Check if a graph contains a given edge.
-- -- -- Complexity: /O(log(n))/ time.
-- -- --
-- -- -- @
-- -- -- hasEdge x y 'empty'            == False
-- -- -- hasEdge x y ('vertex' z)       == False
-- -- -- hasEdge x y ('edge' x y)       == True
-- -- -- hasEdge x y . 'removeEdge' x y == 'const' False
-- -- -- hasEdge x y                  == 'elem' (x,y) . 'edgeList'
-- -- -- @
hasEdge :: Ord a => a -> a -> AdjacencyMapPoc a -> Bool
hasEdge u v g@(AM aim _ _) = Maybe.isJust $ index g u >>= (\a -> fmap (\b -> AIM.hasEdge a b aim) (index g v))

-- -- -- | The number of vertices in a graph.
-- -- -- Complexity: /O(1)/ time.
-- -- --
-- -- -- @
-- -- -- vertexCount 'empty'             ==  0
-- -- -- vertexCount ('vertex' x)        ==  1
-- -- -- vertexCount                   ==  'length' . 'vertexList'
-- -- -- vertexCount x \< vertexCount y ==> x \< y
-- -- -- @
vertexCount :: AdjacencyMapPoc a -> Int
vertexCount = AIM.vertexCount . graph

-- -- -- | The number of edges in a graph.
-- -- -- Complexity: /O(n)/ time.
-- -- --
-- -- -- @
-- -- -- edgeCount 'empty'      == 0
-- -- -- edgeCount ('vertex' x) == 0
-- -- -- edgeCount ('edge' x y) == 1
-- -- -- edgeCount            == 'length' . 'edgeList'
-- -- -- @
edgeCount :: AdjacencyMapPoc a -> Int
edgeCount = AIM.edgeCount . graph

-- -- | The sorted list of vertices of a given graph.
-- -- Complexity: /O(n)/ time and memory.
-- --
-- -- @
-- -- vertexList 'empty'      == []
-- -- vertexList ('vertex' x) == [x]
-- -- vertexList . 'vertices' == 'Data.List.nub' . 'Data.List.sort'
-- -- @
vertexList :: AdjacencyMapPoc a -> [a]
vertexList g@(AM aim _ _) = Maybe.mapMaybe (value g) (AIM.vertexList aim)

-- -- -- | The sorted list of edges of a graph.
-- -- -- Complexity: /O(n + m)/ time and /O(m)/ memory.
-- -- --
-- -- -- @
-- -- -- edgeList 'empty'          == []
-- -- -- edgeList ('vertex' x)     == []
-- -- -- edgeList ('edge' x y)     == [(x,y)]
-- -- -- edgeList ('star' 2 [3,1]) == [(2,1), (2,3)]
-- -- -- edgeList . 'edges'        == 'Data.List.nub' . 'Data.List.sort'
-- -- -- edgeList . 'transpose'    == 'Data.List.sort' . 'map' 'Data.Tuple.swap' . edgeList
-- -- -- @
edgeList :: AdjacencyMapPoc a -> [(a, a)]
edgeList g@(AM aim _ _) = Maybe.mapMaybe (\(from, to) -> value g from >>= (\f -> fmap (f,) (value g to))) (AIM.edgeList aim)

-- -- -- | The set of vertices of a given graph.
-- -- -- Complexity: /O(n)/ time and memory.
-- -- --
-- -- -- @
-- -- -- vertexSet 'empty'      == Set.'Set.empty'
-- -- -- vertexSet . 'vertex'   == Set.'Set.singleton'
-- -- -- vertexSet . 'vertices' == Set.'Set.fromList'
-- -- -- @
-- -- vertexSet :: AdjacencyMapPoc a -> Set a
-- -- vertexSet = Map.keysSet . AdjacencyMapPoc

-- -- -- | The set of edges of a given graph.
-- -- -- Complexity: /O((n + m) * log(m))/ time and /O(m)/ memory.
-- -- --
-- -- -- @
-- -- -- edgeSet 'empty'      == Set.'Set.empty'
-- -- -- edgeSet ('vertex' x) == Set.'Set.empty'
-- -- -- edgeSet ('edge' x y) == Set.'Set.singleton' (x,y)
-- -- -- edgeSet . 'edges'    == Set.'Set.fromList'
-- -- -- @
-- -- edgeSet :: Eq a => AdjacencyMapPoc a -> Set (a, a)
-- -- edgeSet = Set.fromAscList . edgeList

-- -- -- | The sorted /adjacency list/ of a graph.
-- -- -- Complexity: /O(n + m)/ time and /O(m)/ memory.
-- -- --
-- -- -- @
-- -- -- adjacencyList 'empty'          == []
-- -- -- adjacencyList ('vertex' x)     == [(x, [])]
-- -- -- adjacencyList ('edge' 1 2)     == [(1, [2]), (2, [])]
-- -- -- adjacencyList ('star' 2 [3,1]) == [(1, []), (2, [1,3]), (3, [])]
-- -- -- 'stars' . adjacencyList        == id
-- -- -- @
-- -- adjacencyList :: AdjacencyMapPoc a -> [(a, [a])]
-- -- adjacencyList = map (fmap Set.toAscList) . Map.toAscList . AdjacencyMapPoc

-- -- -- | The /preset/ of an element @x@ is the set of its /direct predecessors/.
-- -- -- Complexity: /O(n * log(n))/ time and /O(n)/ memory.
-- -- --
-- -- -- @
-- -- -- preSet x 'empty'      == Set.'Set.empty'
-- -- -- preSet x ('vertex' x) == Set.'Set.empty'
-- -- -- preSet 1 ('edge' 1 2) == Set.'Set.empty'
-- -- -- preSet y ('edge' x y) == Set.'Set.fromList' [x]
-- -- -- @
-- -- preSet :: Ord a => a -> AdjacencyMapPoc a -> Set a
-- -- preSet x = Set.fromAscList . map fst . filter p  . Map.toAscList . AdjacencyMapPoc
-- --   where
-- --     p (_, set) = x `Set.member` set

-- -- -- | The /postset/ of a vertex is the set of its /direct successors/.
-- -- -- Complexity: /O(log(n))/ time and /O(1)/ memory.
-- -- --
-- -- -- @
-- -- -- postSet x 'empty'      == Set.'Set.empty'
-- -- -- postSet x ('vertex' x) == Set.'Set.empty'
-- -- -- postSet x ('edge' x y) == Set.'Set.fromList' [y]
-- -- -- postSet 2 ('edge' 1 2) == Set.'Set.empty'
-- -- -- @
-- -- postSet :: Ord a => a -> AdjacencyMapPoc a -> Set a
-- -- postSet x = Map.findWithDefault Set.empty x . AdjacencyMapPoc

-- -- -- | The /path/ on a list of vertices.
-- -- -- Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
-- -- --
-- -- -- @
-- -- -- path []        == 'empty'
-- -- -- path [x]       == 'vertex' x
-- -- -- path [x,y]     == 'edge' x y
-- -- -- path . 'reverse' == 'transpose' . path
-- -- -- @
-- -- path :: Ord a => [a] -> AdjacencyMapPoc a
-- -- path xs = case xs of []     -> empty
-- --                      [x]    -> vertex x
-- --                      (_:ys) -> edges (zip xs ys)

-- -- -- | The /circuit/ on a list of vertices.
-- -- -- Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
-- -- --
-- -- -- @
-- -- -- circuit []        == 'empty'
-- -- -- circuit [x]       == 'edge' x x
-- -- -- circuit [x,y]     == 'edges' [(x,y), (y,x)]
-- -- -- circuit . 'reverse' == 'transpose' . circuit
-- -- -- @
-- -- circuit :: Ord a => [a] -> AdjacencyMapPoc a
-- -- circuit []     = empty
-- -- circuit (x:xs) = path $ [x] ++ xs ++ [x]

-- -- -- | The /clique/ on a list of vertices.
-- -- -- Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
-- -- --
-- -- -- @
-- -- -- clique []         == 'empty'
-- -- -- clique [x]        == 'vertex' x
-- -- -- clique [x,y]      == 'edge' x y
-- -- -- clique [x,y,z]    == 'edges' [(x,y), (x,z), (y,z)]
-- -- -- clique (xs '++' ys) == 'connect' (clique xs) (clique ys)
-- -- -- clique . 'reverse'  == 'transpose' . clique
-- -- -- @
-- -- clique :: Ord a => [a] -> AdjacencyMapPoc a
-- -- clique = fromAdjacencySets . fst . go
-- --   where
-- --     go []     = ([], Set.empty)
-- --     go (x:xs) = let (res, set) = go xs in ((x, set) : res, Set.insert x set)
-- -- {-# NOINLINE [1] clique #-}

-- -- -- | The /biclique/ on two lists of vertices.
-- -- -- Complexity: /O(n * log(n) + m)/ time and /O(n + m)/ memory.
-- -- --
-- -- -- @
-- -- -- biclique []      []      == 'empty'
-- -- -- biclique [x]     []      == 'vertex' x
-- -- -- biclique []      [y]     == 'vertex' y
-- -- -- biclique [x1,x2] [y1,y2] == 'edges' [(x1,y1), (x1,y2), (x2,y1), (x2,y2)]
-- -- -- biclique xs      ys      == 'connect' ('vertices' xs) ('vertices' ys)
-- -- -- @
-- -- biclique :: Ord a => [a] -> [a] -> AdjacencyMapPoc a
-- -- biclique xs ys = AM $ Map.fromSet adjacent (x `Set.union` y)
-- --   where
-- --     x = Set.fromList xs
-- --     y = Set.fromList ys
-- --     adjacent v = if v `Set.member` x then y else Set.empty

-- -- -- TODO: Optimise.
-- -- -- | The /star/ formed by a centre vertex connected to a list of leaves.
-- -- -- Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
-- -- --
-- -- -- @
-- -- -- star x []    == 'vertex' x
-- -- -- star x [y]   == 'edge' x y
-- -- -- star x [y,z] == 'edges' [(x,y), (x,z)]
-- -- -- star x ys    == 'connect' ('vertex' x) ('vertices' ys)
-- -- -- @
-- -- star :: Ord a => a -> [a] -> AdjacencyMapPoc a
-- -- star x [] = vertex x
-- -- star x ys = connect (vertex x) (vertices ys)
-- -- {-# INLINE star #-}

-- -- -- | The /stars/ formed by overlaying a list of 'star's. An inverse of
-- -- -- 'adjacencyList'.
-- -- -- Complexity: /O(L * log(n))/ time, memory and size, where /L/ is the total
-- -- -- size of the input.
-- -- --
-- -- -- @
-- -- -- stars []                      == 'empty'
-- -- -- stars [(x, [])]               == 'vertex' x
-- -- -- stars [(x, [y])]              == 'edge' x y
-- -- -- stars [(x, ys)]               == 'star' x ys
-- -- -- stars                         == 'overlays' . 'map' ('uncurry' 'star')
-- -- -- stars . 'adjacencyList'         == id
-- -- -- 'overlay' (stars xs) (stars ys) == stars (xs '++' ys)
-- -- -- @
-- -- stars :: Ord a => [(a, [a])] -> AdjacencyMapPoc a
-- -- stars = fromAdjacencySets . map (fmap Set.fromList)

-- -- -- | Construct a graph from a list of adjacency sets; a variation of 'stars'.
-- -- -- Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
-- -- --
-- -- -- @
-- -- -- fromAdjacencySets []                                  == 'empty'
-- -- -- fromAdjacencySets [(x, Set.'Set.empty')]                    == 'vertex' x
-- -- -- fromAdjacencySets [(x, Set.'Set.singleton' y)]              == 'edge' x y
-- -- -- fromAdjacencySets . 'map' ('fmap' Set.'Set.fromList')           == 'stars'
-- -- -- 'overlay' (fromAdjacencySets xs) (fromAdjacencySets ys) == fromAdjacencySets (xs '++' ys)
-- -- -- @
-- -- fromAdjacencySets :: Ord a => [(a, Set a)] -> AdjacencyMapPoc a
-- -- fromAdjacencySets ss = AM $ Map.unionWith Set.union vs es
-- --   where
-- --     vs = Map.fromSet (const Set.empty) . Set.unions $ map snd ss
-- --     es = Map.fromListWith Set.union ss

-- -- -- | The /tree graph/ constructed from a given 'Tree' data structure.
-- -- -- Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
-- -- --
-- -- -- @
-- -- -- tree (Node x [])                                         == 'vertex' x
-- -- -- tree (Node x [Node y [Node z []]])                       == 'path' [x,y,z]
-- -- -- tree (Node x [Node y [], Node z []])                     == 'star' x [y,z]
-- -- -- tree (Node 1 [Node 2 [], Node 3 [Node 4 [], Node 5 []]]) == 'edges' [(1,2), (1,3), (3,4), (3,5)]
-- -- -- @
-- -- tree :: Ord a => Tree a -> AdjacencyMapPoc a
-- -- tree (Node x []) = vertex x
-- -- tree (Node x f ) = star x (map rootLabel f)
-- --     `overlay` forest (filter (not . null . subForest) f)

-- -- -- | The /forest graph/ constructed from a given 'Forest' data structure.
-- -- -- Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
-- -- --
-- -- -- @
-- -- -- forest []                                                  == 'empty'
-- -- -- forest [x]                                                 == 'tree' x
-- -- -- forest [Node 1 [Node 2 [], Node 3 []], Node 4 [Node 5 []]] == 'edges' [(1,2), (1,3), (4,5)]
-- -- -- forest                                                     == 'overlays' . 'map' 'tree'
-- -- -- @
-- -- forest :: Ord a => Forest a -> AdjacencyMapPoc a
-- -- forest = overlays . map tree

-- -- -- | Remove a vertex from a given graph.
-- -- -- Complexity: /O(n*log(n))/ time.
-- -- --
-- -- -- @
-- -- -- removeVertex x ('vertex' x)       == 'empty'
-- -- -- removeVertex 1 ('vertex' 2)       == 'vertex' 2
-- -- -- removeVertex x ('edge' x x)       == 'empty'
-- -- -- removeVertex 1 ('edge' 1 2)       == 'vertex' 2
-- -- -- removeVertex x . removeVertex x == removeVertex x
-- -- -- @
-- -- removeVertex :: Ord a => a -> AdjacencyMapPoc a -> AdjacencyMapPoc a
-- -- removeVertex x = AM . Map.map (Set.delete x) . Map.delete x . AdjacencyMapPoc

-- -- -- | Remove an edge from a given graph.
-- -- -- Complexity: /O(log(n))/ time.
-- -- --
-- -- -- @
-- -- -- removeEdge x y ('edge' x y)       == 'vertices' [x,y]
-- -- -- removeEdge x y . removeEdge x y == removeEdge x y
-- -- -- removeEdge x y . 'removeVertex' x == 'removeVertex' x
-- -- -- removeEdge 1 1 (1 * 1 * 2 * 2)  == 1 * 2 * 2
-- -- -- removeEdge 1 2 (1 * 1 * 2 * 2)  == 1 * 1 + 2 * 2
-- -- -- @
-- -- removeEdge :: Ord a => a -> a -> AdjacencyMapPoc a -> AdjacencyMapPoc a
-- -- removeEdge x y = AM . Map.adjust (Set.delete y) x . AdjacencyMapPoc

-- -- -- | The function @'replaceVertex' x y@ replaces vertex @x@ with vertex @y@ in a
-- -- -- given 'AdjacencyMapPoc'. If @y@ already exists, @x@ and @y@ will be merged.
-- -- -- Complexity: /O((n + m) * log(n))/ time.
-- -- --
-- -- -- @
-- -- -- replaceVertex x x            == id
-- -- -- replaceVertex x y ('vertex' x) == 'vertex' y
-- -- -- replaceVertex x y            == 'mergeVertices' (== x) y
-- -- -- @
-- -- replaceVertex :: Ord a => a -> a -> AdjacencyMapPoc a -> AdjacencyMapPoc a
-- -- replaceVertex u v = gmap $ \w -> if w == u then v else w

-- -- -- | Merge vertices satisfying a given predicate into a given vertex.
-- -- -- Complexity: /O((n + m) * log(n))/ time, assuming that the predicate takes
-- -- -- /O(1)/ to be evaluated.
-- -- --
-- -- -- @
-- -- -- mergeVertices ('const' False) x    == id
-- -- -- mergeVertices (== x) y           == 'replaceVertex' x y
-- -- -- mergeVertices 'even' 1 (0 * 2)     == 1 * 1
-- -- -- mergeVertices 'odd'  1 (3 + 4 * 5) == 4 * 1
-- -- -- @
-- -- mergeVertices :: Ord a => (a -> Bool) -> a -> AdjacencyMapPoc a -> AdjacencyMapPoc a
-- -- mergeVertices p v = gmap $ \u -> if p u then v else u

-- -- -- | Transpose a given graph.
-- -- -- Complexity: /O(m * log(n))/ time, /O(n + m)/ memory.
-- -- --
-- -- -- @
-- -- -- transpose 'empty'       == 'empty'
-- -- -- transpose ('vertex' x)  == 'vertex' x
-- -- -- transpose ('edge' x y)  == 'edge' y x
-- -- -- transpose . transpose == id
-- -- -- 'edgeList' . transpose  == 'Data.List.sort' . 'map' 'Data.Tuple.swap' . 'edgeList'
-- -- -- @
-- -- transpose :: Ord a => AdjacencyMapPoc a -> AdjacencyMapPoc a
-- -- transpose (AM m) = AM $ Map.foldrWithKey combine vs m
-- --   where
-- --     combine v es = Map.unionWith Set.union (Map.fromSet (const $ Set.singleton v) es)
-- --     vs           = Map.fromSet (const Set.empty) (Map.keysSet m)
-- -- {-# NOINLINE [1] transpose #-}

-- -- {-# RULES
-- -- "transpose/empty"    transpose empty = empty
-- -- "transpose/vertex"   forall x. transpose (vertex x) = vertex x
-- -- "transpose/overlay"  forall g1 g2. transpose (overlay g1 g2) = overlay (transpose g1) (transpose g2)
-- -- "transpose/connect"  forall g1 g2. transpose (connect g1 g2) = connect (transpose g2) (transpose g1)

-- -- "transpose/overlays" forall xs. transpose (overlays xs) = overlays (map transpose xs)
-- -- "transpose/connects" forall xs. transpose (connects xs) = connects (reverse (map transpose xs))

-- -- "transpose/vertices" forall xs. transpose (vertices xs) = vertices xs
-- -- "transpose/clique"   forall xs. transpose (clique xs)   = clique (reverse xs)
-- --  #-}

-- -- -- | Transform a graph by applying a function to each of its vertices. This is
-- -- -- similar to @Functor@'s 'fmap' but can be used with non-fully-parametric
-- -- -- 'AdjacencyMapPoc'.
-- -- -- Complexity: /O((n + m) * log(n))/ time.
-- -- --
-- -- -- @
-- -- -- gmap f 'empty'      == 'empty'
-- -- -- gmap f ('vertex' x) == 'vertex' (f x)
-- -- -- gmap f ('edge' x y) == 'edge' (f x) (f y)
-- -- -- gmap 'id'           == 'id'
-- -- -- gmap f . gmap g   == gmap (f . g)
-- -- -- @
-- -- gmap :: (Ord a, Ord b) => (a -> b) -> AdjacencyMapPoc a -> AdjacencyMapPoc b
-- -- gmap f = AM . Map.map (Set.map f) . Map.mapKeysWith Set.union f . AdjacencyMapPoc

-- -- -- | Construct the /induced subgraph/ of a given graph by removing the
-- -- -- vertices that do not satisfy a given predicate.
-- -- -- Complexity: /O(n + m)/ time, assuming that the predicate takes /O(1)/ to
-- -- -- be evaluated.
-- -- --
-- -- -- @
-- -- -- induce ('const' True ) x      == x
-- -- -- induce ('const' False) x      == 'empty'
-- -- -- induce (/= x)               == 'removeVertex' x
-- -- -- induce p . induce q         == induce (\\x -> p x && q x)
-- -- -- 'isSubgraphOf' (induce p x) x == True
-- -- -- @
-- -- induce :: (a -> Bool) -> AdjacencyMapPoc a -> AdjacencyMapPoc a
-- -- induce p = AM . Map.map (Set.filter p) . Map.filterWithKey (\k _ -> p k) . AdjacencyMapPoc

-- -- -- | Construct the /induced subgraph/ of a given graph by removing the vertices
-- -- -- that are 'Nothing'.
-- -- -- Complexity: /O(n + m)/ time.
-- -- --
-- -- -- @
-- -- -- induceJust ('vertex' 'Nothing')                               == 'empty'
-- -- -- induceJust ('edge' ('Just' x) 'Nothing')                        == 'vertex' x
-- -- -- induceJust . 'gmap' 'Just'                                    == 'id'
-- -- -- induceJust . 'gmap' (\\x -> if p x then 'Just' x else 'Nothing') == 'induce' p
-- -- -- @
-- -- induceJust :: Ord a => AdjacencyMapPoc (Maybe a) -> AdjacencyMapPoc a
-- -- induceJust = AM . Map.map catMaybesSet . catMaybesMap . AdjacencyMapPoc
-- --     where
-- --       catMaybesSet = Set.mapMonotonic     Maybe.fromJust . Set.delete Nothing
-- --       catMaybesMap = Map.mapKeysMonotonic Maybe.fromJust . Map.delete Nothing

-- -- -- | Left-to-right /relational composition/ of graphs: vertices @x@ and @z@ are
-- -- -- connected in the resulting graph if there is a vertex @y@, such that @x@ is
-- -- -- connected to @y@ in the first graph, and @y@ is connected to @z@ in the
-- -- -- second graph. There are no isolated vertices in the result. This operation is
-- -- -- associative, has 'empty' and single-'vertex' graphs as /annihilating zeroes/,
-- -- -- and distributes over 'overlay'.
-- -- -- Complexity: /O(n * m * log(n))/ time and /O(n + m)/ memory.
-- -- --
-- -- -- @
-- -- -- compose 'empty'            x                == 'empty'
-- -- -- compose x                'empty'            == 'empty'
-- -- -- compose ('vertex' x)       y                == 'empty'
-- -- -- compose x                ('vertex' y)       == 'empty'
-- -- -- compose x                (compose y z)    == compose (compose x y) z
-- -- -- compose x                ('overlay' y z)    == 'overlay' (compose x y) (compose x z)
-- -- -- compose ('overlay' x y)    z                == 'overlay' (compose x z) (compose y z)
-- -- -- compose ('edge' x y)       ('edge' y z)       == 'edge' x z
-- -- -- compose ('path'    [1..5]) ('path'    [1..5]) == 'edges' [(1,3), (2,4), (3,5)]
-- -- -- compose ('circuit' [1..5]) ('circuit' [1..5]) == 'circuit' [1,3,5,2,4]
-- -- -- @
-- -- compose :: Ord a => AdjacencyMapPoc a -> AdjacencyMapPoc a -> AdjacencyMapPoc a
-- -- compose x y = fromAdjacencySets
-- --     [ (t, ys) | v <- Set.toList vs, let ys = postSet v y, not (Set.null ys)
-- --               , t <- Set.toList (postSet v tx) ]
-- --   where
-- --     tx = transpose x
-- --     vs = vertexSet x `Set.union` vertexSet y

-- -- -- | Compute the /Cartesian product/ of graphs.
-- -- -- Complexity: /O(n * m * log(n)^2)/ time.
-- -- --
-- -- -- @
-- -- -- box ('path' [0,1]) ('path' "ab") == 'edges' [ ((0,\'a\'), (0,\'b\'))
-- -- --                                       , ((0,\'a\'), (1,\'a\'))
-- -- --                                       , ((0,\'b\'), (1,\'b\'))
-- -- --                                       , ((1,\'a\'), (1,\'b\')) ]
-- -- -- @
-- -- --
-- -- -- Up to an isomorphism between the resulting vertex types, this operation
-- -- -- is /commutative/, /associative/, /distributes/ over 'overlay', has singleton
-- -- -- graphs as /identities/ and 'empty' as the /annihilating zero/. Below @~~@
-- -- -- stands for the equality up to an isomorphism, e.g. @(x, ()) ~~ x@.
-- -- --
-- -- -- @
-- -- -- box x y               ~~ box y x
-- -- -- box x (box y z)       ~~ box (box x y) z
-- -- -- box x ('overlay' y z)   == 'overlay' (box x y) (box x z)
-- -- -- box x ('vertex' ())     ~~ x
-- -- -- box x 'empty'           ~~ 'empty'
-- -- -- 'transpose'   (box x y) == box ('transpose' x) ('transpose' y)
-- -- -- 'vertexCount' (box x y) == 'vertexCount' x * 'vertexCount' y
-- -- -- 'edgeCount'   (box x y) <= 'vertexCount' x * 'edgeCount' y + 'edgeCount' x * 'vertexCount' y
-- -- -- @
-- -- box :: (Ord a, Ord b) => AdjacencyMapPoc a -> AdjacencyMapPoc b -> AdjacencyMapPoc (a, b)
-- -- box (AM x) (AM y) = overlay (AM $ Map.fromAscList xs) (AM $ Map.fromAscList ys)
-- --   where
-- --     xs = do (a, as) <- Map.toAscList x
-- --             b       <- Set.toAscList (Map.keysSet y)
-- --             return ((a, b), Set.mapMonotonic (,b) as)
-- --     ys = do a       <- Set.toAscList (Map.keysSet x)
-- --             (b, bs) <- Map.toAscList y
-- --             return ((a, b), Set.mapMonotonic (a,) bs)

-- -- -- | Compute the /reflexive and transitive closure/ of a graph.
-- -- -- Complexity: /O(n * m * log(n)^2)/ time.
-- -- --
-- -- -- @
-- -- -- closure 'empty'           == 'empty'
-- -- -- closure ('vertex' x)      == 'edge' x x
-- -- -- closure ('edge' x x)      == 'edge' x x
-- -- -- closure ('edge' x y)      == 'edges' [(x,x), (x,y), (y,y)]
-- -- -- closure ('path' $ 'Data.List.nub' xs) == 'reflexiveClosure' ('clique' $ 'Data.List.nub' xs)
-- -- -- closure                 == 'reflexiveClosure' . 'transitiveClosure'
-- -- -- closure                 == 'transitiveClosure' . 'reflexiveClosure'
-- -- -- closure . closure       == closure
-- -- -- 'postSet' x (closure y)   == Set.'Set.fromList' ('Algebra.Graph.ToGraph.reachable' x y)
-- -- -- @
-- -- closure :: Ord a => AdjacencyMapPoc a -> AdjacencyMapPoc a
-- -- closure = reflexiveClosure . transitiveClosure

-- -- -- | Compute the /reflexive closure/ of a graph by adding a self-loop to every
-- -- -- vertex.
-- -- -- Complexity: /O(n * log(n))/ time.
-- -- --
-- -- -- @
-- -- -- reflexiveClosure 'empty'              == 'empty'
-- -- -- reflexiveClosure ('vertex' x)         == 'edge' x x
-- -- -- reflexiveClosure ('edge' x x)         == 'edge' x x
-- -- -- reflexiveClosure ('edge' x y)         == 'edges' [(x,x), (x,y), (y,y)]
-- -- -- reflexiveClosure . reflexiveClosure == reflexiveClosure
-- -- -- @
-- -- reflexiveClosure :: Ord a => AdjacencyMapPoc a -> AdjacencyMapPoc a
-- -- reflexiveClosure (AM m) = AM $ Map.mapWithKey (\k -> Set.insert k) m

-- -- -- | Compute the /symmetric closure/ of a graph by overlaying it with its own
-- -- -- transpose.
-- -- -- Complexity: /O((n + m) * log(n))/ time.
-- -- --
-- -- -- @
-- -- -- symmetricClosure 'empty'              == 'empty'
-- -- -- symmetricClosure ('vertex' x)         == 'vertex' x
-- -- -- symmetricClosure ('edge' x y)         == 'edges' [(x,y), (y,x)]
-- -- -- symmetricClosure x                  == 'overlay' x ('transpose' x)
-- -- -- symmetricClosure . symmetricClosure == symmetricClosure
-- -- -- @
-- -- symmetricClosure :: Ord a => AdjacencyMapPoc a -> AdjacencyMapPoc a
-- -- symmetricClosure m = overlay m (transpose m)

-- -- -- | Compute the /transitive closure/ of a graph.
-- -- -- Complexity: /O(n * m * log(n)^2)/ time.
-- -- --
-- -- -- @
-- -- -- transitiveClosure 'empty'               == 'empty'
-- -- -- transitiveClosure ('vertex' x)          == 'vertex' x
-- -- -- transitiveClosure ('edge' x y)          == 'edge' x y
-- -- -- transitiveClosure ('path' $ 'Data.List.nub' xs)     == 'clique' ('Data.List.nub' xs)
-- -- -- transitiveClosure . transitiveClosure == transitiveClosure
-- -- -- @
-- -- transitiveClosure :: Ord a => AdjacencyMapPoc a -> AdjacencyMapPoc a
-- -- transitiveClosure old
-- --     | old == new = old
-- --     | otherwise  = transitiveClosure new
-- --   where
-- --     new = overlay old (old `compose` old)

-- -- -- | Check that the internal graph representation is consistent, i.e. that all
-- -- -- edges refer to existing vertices. It should be impossible to create an
-- -- -- inconsistent adjacency map, and we use this function in testing.
-- -- --
-- -- -- @
-- -- -- consistent 'empty'         == True
-- -- -- consistent ('vertex' x)    == True
-- -- -- consistent ('overlay' x y) == True
-- -- -- consistent ('connect' x y) == True
-- -- -- consistent ('edge' x y)    == True
-- -- -- consistent ('edges' xs)    == True
-- -- -- consistent ('stars' xs)    == True
-- -- -- @
-- -- consistent :: Ord a => AdjacencyMapPoc a -> Bool
-- -- consistent (AM m) = referredToVertexSet m `Set.isSubsetOf` Map.keysSet m

-- -- -- The set of vertices that are referred to by the edges of an adjacency map.
-- -- referredToVertexSet :: Ord a => Map a (Set a) -> Set a
-- -- referredToVertexSet m = Set.fromList $ concat
-- --     [ [x, y] | (x, ys) <- Map.toAscList m, y <- Set.toAscList ys ]

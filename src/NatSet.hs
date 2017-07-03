module NatSet where

import qualified Data.IntSet as I

data NatSet = Finite I.IntSet | Cofinite I.IntSet deriving (Show, Eq, Ord)

fromList :: [Int] -> NatSet
fromList = Finite . I.fromList

naturals :: NatSet
naturals = Cofinite (I.fromList [])

(\\) :: NatSet -> NatSet -> NatSet
Finite a   \\ Finite b   = Finite (a I.\\ b)
Finite a   \\ Cofinite b = Finite (a `I.intersection` b)
Cofinite a \\ Finite b   = Cofinite (a `I.union` b)
Cofinite a \\ Cofinite b = Finite (b I.\\ a)

intersection :: NatSet -> NatSet -> NatSet
Finite a   `intersection` Finite b   = Finite (a `I.intersection` b)
Finite a   `intersection` Cofinite b = Finite (a I.\\ b)
Cofinite a `intersection` Finite b   = Finite (b I.\\ a)
Cofinite a `intersection` Cofinite b = Cofinite (a `I.union` b)

union :: NatSet -> NatSet -> NatSet
Finite a   `union` Finite b   = Finite (a `I.union` b)
-- a \/ N-b
Finite a   `union` Cofinite b = Cofinite (b I.\\ a)
Cofinite a `union` Finite b   = Cofinite (a I.\\ b)
Cofinite a `union` Cofinite b = Cofinite (a `I.intersection` b)

complement :: NatSet -> NatSet
complement (Finite a)   = Cofinite a
complement (Cofinite a) = Finite a

segment :: NatSet -> NatSet
segment (Finite a) = Finite (finiteSegment 0 (I.singleton 0)) where
    finiteSegment i s =
        if i `I.member` a
            then finiteSegment (i+1) (I.insert (i+1) s)
            else s
segment (Cofinite a) = Finite (I.fromList [0..I.findMin a])

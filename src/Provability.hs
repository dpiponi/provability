{-|
Module: Provability

This module provides functionality for working with the provability
logic GL.

Although GL deals with the provability (or not) of propositions in logical systems that are not complete, it is, surprisingly, a complete logic itself.
This means that checking whether a proposition is a theorem is computable.
This module provides tools to test whether a proposition of GL is a theorem.
It also provides a tool for finding fixed points in GL, i.e. propositions @P@ solving an equation of the form @P \<-\> f(P)@, for suitable logical functions @f@.

Note that the tests may take a long time to run.
The sun might become a red giant first.
I'll uses shorter examples eventually.

Refs:

* https://plato.stanford.edu/entries/logic-provability/

* https://en.wikipedia.org/wiki/Provability_logic

* The Logic of Provability, George Boolos, Cambridge, 1993

* First Order Logic, Raymond Smullyan, Dover

* http://blog.sigfpe.com/2011/04/generalising-godels-theorem-with.html
-}

{-# LANGUAGE ViewPatterns #-}
module Provability(interp,
                   valid,
                   value,
                   value',
                   dnf,
                   Prop(..),
                   (\/), (/\), (-->), (<--), (<->),
                   fixedpoint,
                   beth,
                   simplify,
                   canonical,
                   module NatSet,
                   a, b, c, d, p, q, r, s, t) where

import Control.Applicative hiding (empty)
import Control.Arrow
import Control.Monad
import Data.Function
import Data.List hiding (union)
import Data.Either
import Data.Maybe
import Text.Show
import Debug.Trace
import Test.QuickCheck hiding ((.&.))
--import qualified NatSet as N
import NatSet
import qualified Data.Bits as B

infixr 1 :->
infixr 2 :\/
infixr 3 :/\
infixr 1 -->
infixr 1 <--
infixr 1 <->
infixr 2 \/
infixr 3 /\

-- | A convenient alternative to ':\/'
(\/)    = (:\/)
-- | A convenient alternative to ':/\'
(/\)    = (:/\)
-- | A convenient alternative to ':->'
(-->)   = (:->)
-- | reverse implication, i.e. @p \<-- q = q :-\> p@
(<--)   = flip (:->)
-- | two-way implication, i.e. @p \<-\> q = (p :-> q) :/\\ (q :-> p)@
p <-> q = (p :-> q) :/\ (q :-> p)

-- | The type of a proposition of provability logic.
data Prop
    -- | a variable whose name is given by the string
    = Letter String
    -- | the disjunction of two subpropositions, ∨
    | Prop :\/ Prop
    -- | the conjunction of two subpropositions, ∧
    | Prop :/\ Prop
    -- | implication, →
    | Prop :-> Prop
    -- | the modal operator □, i.e. provability
    | Box Prop
    -- | the modal operator ⋄, i.e. ⋄p = ¬□¬p
    | Dia Prop
    -- | falsity, ⊥
    | F
    -- | truth, ⊤
    | T
    -- | negation, ¬
    | Neg Prop deriving (Eq, Ord)

instance Show Prop where
    showsPrec p (a :/\ b)  =
        showParen (p>3) $ showsPrec 3 a . showString " /\\ " . showsPrec 3 b
    showsPrec p (a :\/ b)  =
        showParen (p>2) $ showsPrec 2 a . showString " \\/ " . showsPrec 2 b
    showsPrec p (a :-> b)  =
        showParen (p>1) $ showsPrec 1 a . showString " --> " . showsPrec 1 b
    showsPrec p (Neg r)    =
        showParen (p>4) $ showString "Neg " . showsPrec 5 r
    showsPrec p (Box r)    =
        showParen (p>4) $ showString "Box " . showsPrec 5 r
    showsPrec p (Dia r)    =
        showParen (p>4) $ showString "Dia " . showsPrec 5 r
    showsPrec p (Letter n) = showParen (p>5) $ showsPrec 6 n
    showsPrec p T          = showString "T"
    showsPrec p F          = showString "F"

newtype SingleLetter = SingleLetter String deriving Show

instance Arbitrary SingleLetter where
    arbitrary = oneof $ map (\x -> return (SingleLetter [x])) ['a'..'z']

letter = do
    SingleLetter l <- arbitrary
    return $ Letter l

tree' True 0 = oneof [return T, return F, letter]
tree' False 0 = oneof [return T, return F]
tree' allowed n = oneof [tree1 allowed n, tree2 allowed n]

tree1 allowed n = do
    a <- tree' allowed (n-1)
    oneof [return $ Box a, return $ Dia a]

tree2 allowed n = do
    i <- choose (0, n-1)
    a <- tree' allowed i
    b <- tree' allowed (n-1-i)
    oneof [return $ a :\/ b, return $ a :/\ b, return $ a :-> b]

instance Arbitrary Prop where
    arbitrary = sized (tree' True)

newtype LetterFree = LetterFree Prop deriving Show

instance Arbitrary LetterFree where
    arbitrary = do
        p <- sized (tree' False)
        return (LetterFree p)

-- | Performs basic simplification of propositions.
--
-- It performs only one kind of simplification, "constant folding".
-- It will remove all redundant appearances of 'T' and 'F'.
simplify p = let simplify' (a :\/ F) = a
                 simplify' (F :\/ b) = b
                 simplify' (a :/\ T) = a
                 simplify' (T :/\ b) = b
                 simplify' (a :\/ T) = T
                 simplify' (T :\/ b) = T
                 simplify' (a :/\ F) = F
                 simplify' (F :/\ b) = F
                 simplify' (F :-> b) = T
                 simplify' (T :-> b) = b
                 simplify' (a :-> F) = Neg a
                 simplify' (a :-> T) = T
                 simplify' (Neg T) = F
                 simplify' (Neg F) = T
                 simplify' (Box T) = T
                 simplify' (Dia F) = F
                 simplify' z = z
   in case p of
       a :/\ b -> let a' = simplify a
                      b' = simplify b
                  in simplify' (a' :/\ b')
       a :\/ b -> let a' = simplify a
                      b' = simplify b
                  in simplify' (a' :\/ b')
       a :-> b -> simplify' (simplify a :-> simplify b)
       Box a   -> simplify' (Box (simplify a))
       Dia a   -> simplify' (Dia (simplify a))
       Neg (Neg a) -> simplify a
       a           -> a

-- We have multiple algorithms that recurse over proposition-like
-- structures in a similar way.
-- PropType and PropTypeable are intended to abstract out the common structure.
data PropType a = Atomic a
                | Constant a
                | DoubleNegation a
                | Disjunction a a
                | Conjunction a a
                | Provability a
                | Consistency a deriving Show

instance Functor PropType where
    fmap f (Atomic a)         = Atomic (f a)
    fmap f (Constant a)       = Constant (f a)
    fmap f (DoubleNegation a) = DoubleNegation (f a)
    fmap f (Provability a)    = Provability (f a)
    fmap f (Consistency a)    = Consistency (f a)
    fmap f (Conjunction a b)  = Conjunction (f a) (f b)
    fmap f (Disjunction a b)  = Disjunction (f a) (f b)

class PropTypeable a where
    propType :: a -> PropType a
    neg      :: a -> a
    isF      :: a -> Bool
    negative :: a -> Bool
    positiveComponent :: a -> Prop

instance PropTypeable Prop where
    propType (a :\/ b)        = Disjunction a b
    propType (a :/\ b)        = Conjunction a b
    propType (Neg (a :\/ b))  = Conjunction (Neg a) (Neg b)
    propType (Neg (a :/\ b))  = Disjunction (Neg a) (Neg b)
    propType (a :-> b)        = Disjunction (Neg a) b
    propType (Neg (a :-> b))  = Conjunction a (Neg b)
    propType (Neg (Neg a))    = DoubleNegation a
    propType (Box a)          = Provability a
    propType (Neg (Box a))    = Consistency (Neg a)
    propType (Dia a)          = Consistency a
    propType (Neg (Dia a))    = Provability (Neg a)
    propType (Letter a)       = Atomic (Letter a)
    propType (Neg (Letter a)) = Atomic (Neg (Letter a))
    propType T                = Constant T
    propType F                = Constant F
    propType (Neg F)          = Constant T
    propType (Neg T)          = Constant F
    neg                       = Neg
    isF F                     = True
    isF (Neg T)               = True
    isF _                     = False
    positiveComponent (Neg a) = a
    positiveComponent a       = a
    negative (Neg _)          = True
    negative _                = False

-- | This is the valuation from the letterless propositions to the finite or cofinite subsets of
-- the naturals
-- described on page 95 of Boolos
--
-- >>> value (Box (Box F))
-- Finite (fromList [0,1])
value :: Prop -> NatSet
value (propType -> Constant F) = empty
value (propType -> Constant T) = naturals
value (propType -> Disjunction a b) = value a `union` value b
value (propType -> Conjunction a b) = value a `intersection` value b
value (propType -> DoubleNegation a) = value a
value (propType -> Provability a) = segment (value a)
value (propType -> Consistency a) = complement $ segment $ complement $ value a
value (propType -> Atomic _) = error "value can only be applied to the letterless fragment of GL"

-- | This is the valuation from the letterless propositions to the finite or cofinite subsets of the naturals
-- described on page 95 of Boolos
-- but with the subsets of the naturals interpreted as bitsets encoded
-- as integers.
--
-- >>> value' $ value' $ Neg (Box F) <-> Neg (Box (Neg (Box F)))
-- -1
value' :: Prop -> Integer
value' (propType -> Constant F) = 0
value' (propType -> Constant T) = -1
value' (propType -> Disjunction a b) = value' a B..|. value' b
value' (propType -> Conjunction a b) = value' a B..&. value' b
value' (propType -> DoubleNegation a) = value' a
value' (propType -> Provability a) = let m = value' a in m `B.xor` (m+1)
value' (propType -> Consistency a) = let m = B.complement (value' a) in B.complement (m `B.xor` (m+1))
value' (propType -> Atomic _) = error "value' can only be applied to the letterless fragment of GL"

rmdups :: (Ord a) => [a] -> [a]
rmdups = map head . group . sort

dnf' :: Prop -> [[Prop]]
dnf' (propType -> Conjunction a b) = rmdups (dnf' a ++ dnf' b)
dnf' (propType -> Disjunction a b) = [rmdups (c ++ d) | c <- dnf' a, d <- dnf' b]
dnf' (propType -> DoubleNegation a) = dnf' a
dnf' T = []
dnf' F = [[]]
dnf' a = [[a]]

foldr1' :: (a -> a -> a) -> a -> [a] -> a
foldr1' _ e [] = e
foldr1' m _ a = foldr1 m a

-- | Put proposition into disjunctive normal form.
-- Only does minimal simplification.
-- Doesn't recurse into 'Box' or 'Dia'.
--
-- Should obey for any @t@: @valid (t \<-\> dnf t)@
--
-- >>> dnf $ Neg (a --> Box b \/ (a --> c))
-- "a" /\ Neg "c" /\ Neg (Box "b")
dnf :: Prop -> Prop
dnf p0 = let p = simplify p0 in foldr1' (/\) T [foldr1' (\/) F q | q <- dnf' p]

countBoxes :: Prop -> (Int, Prop)
countBoxes (Box p) =
    let (n, p') = countBoxes p' in (n+1, p')
countBoxes p = (0, p)

data Reduced = RTrue | RNeg Int | RPos Int deriving (Show, Eq, Ord)

reducedToProp :: Reduced -> Prop
reducedToProp RTrue = T
reducedToProp (RNeg n) = Neg (reducedToProp (RPos n))
reducedToProp (RPos 0) = F
reducedToProp (RPos n) = Box (reducedToProp (RPos (n-1)))

-- XXX boxCount needs to handle 'T'
boxCount :: Prop -> Reduced
boxCount (Neg p) =
    case boxCount p of
        RPos n -> RNeg n
        RTrue -> RPos 0
        e -> error $ "boxCount (1): " ++ show e
boxCount F = RPos 0
boxCount (Box p) =
    case boxCount p of
        RTrue -> RTrue
        RPos n -> RPos (n+1)
boxCount T = RTrue
boxCount a = error (show a)

boxCounts :: [Reduced] -> Maybe ([Int], [Int])
boxCounts [] = Just ([], [])
boxCounts (RTrue : _) = Nothing
boxCounts (p : ps) = case boxCounts ps of
    Nothing -> Nothing
    Just (ns, ms) -> case p of
        RPos n -> Just (n : ns, ms)
        RNeg m -> Just (ns, m : ms)

church :: Int -> (a -> a) -> a -> a
church 0 f x = x
church n f x = church (n-1) f (f x)

boxes :: Int -> Prop -> Prop
boxes 0 p = p
boxes n p = boxes (n-1) (Box p)

reduce :: ([Int], [Int]) -> Prop
reduce ([], ms) = reduce ([0], ms)
reduce (ns, ms) =
    let n = foldr1 max ns
    in if null ms
        then church (n+1) Box F
        else
            let m = foldr1 min ms
            in if m <= n
                then T
                else church (n+1) Box F

reduce' :: Maybe ([Int], [Int]) -> Prop
reduce' Nothing = T
reduce' (Just a) = reduce a

reduceFactor :: [Prop] -> Prop
reduceFactor ts = reduce' (boxCounts (map boxCount ts))

-- Get Box p into canonical form
boxCanonical :: Prop -> Prop
boxCanonical p = 
    let d = dnf' p
    in foldr (:/\) T (map reduceFactor d)

testCanonical :: Prop -> IO ()
testCanonical p = do
    let c = canonical p
    print c
    print $ valid $ p <-> c

canonical' :: Prop -> Prop
canonical' (Box p) = boxCanonical (canonical p)
canonical' (Dia p) = canonical (Neg (Box (Neg p)))
canonical' (a :\/ b) = canonical a :\/ canonical b
canonical' (a :/\ b) = canonical a :/\ canonical b
canonical' (a :-> b) = canonical a :-> canonical b
canonical' (Neg a) = Neg (canonical a)
canonical' a@(Letter _) = a
canonical' a@T = a
canonical' a@F = a

canonical :: Prop -> Prop
canonical = simplify . canonical' . simplify

missingSegments :: [Int] -> ([(Int, Int)], Maybe Int)
missingSegments [] = ([], Just 0)
missingSegments (0 : as) = collectSegments [] as 1
missingSegments (a : as) = collectSegments [(0, a)] as (a+1)

collectSegments :: [(Int, Int)] -> [Int] -> Int -> ([(Int, Int)], Maybe Int)
collectSegments segs [a] n = (segs, Just (a+1))
collectSegments segs (a : as) n | a > n = collectSegments (segs ++ [(n, a)]) as (a+1)
                                | otherwise = collectSegments segs as (a+1)

{-
 missingSegments [0, 1, 3]
    = collectSegments [] [1, 3] 1
    = collectSegments [] [3] 2
    = collectSegments 
 -}

-- | 'a', 'b', 'c', 'd', 'p', 'q', 'r', 's', 't' are convenience
-- definitions for @Letter "a"@ and so on.
[a, b, c, d, p, q, r, s, t] = map (Letter . return) "abcdpqrst"

placesWhere p []     = []
placesWhere p (x:xs) = let r = map (second (x:)) $ placesWhere p xs
                       in if p x then ((x, xs) : r) else r

-- | Find a single element, when possible, common to both lists
-- using the equality predicate 'eq'.
findIntersection eq a b = listToMaybe [(x, y) | x <- a, y <- b, x `eq` y]

propositional (propType -> DoubleNegation _) = True
propositional (propType -> Conjunction _ _)  = True
propositional (propType -> Disjunction _ _)  = True
propositional _                              = False

provability (propType -> Provability _) = True
provability (propType -> Consistency _) = True
provability _                           = False

data TableauRules prop result = TableauRules {
    foundF :: prop -> result,
    foundContradiction :: (prop, prop) -> result,
    disjRule :: prop -> result -> result -> result,
    processWorld :: prop -> result -> result
}

simpleClosure rules ps = case find isF ps of
   Just a  -> Just $ foundF rules a
   Nothing ->
     let (neg, pos) = partition negative ps
         maybePair = findIntersection ((==) `on` positiveComponent) neg pos
     in case maybePair of
         Just pair -> Just $ foundContradiction rules pair
         Nothing   -> Nothing
applyDNeg rules p a props = applyPropositional rules (a : delete p props)

applyConj rules p a b props = 
  applyPropositional rules (a : b : delete p props)

applyDisj rules p a b props = do
   let props' = delete p props
   left <- applyPropositional rules (a : props')
   right <- applyPropositional rules (b : props')
   return $ disjRule rules p left right

applyPropositional rules props =
    let t = simpleClosure rules props in if isJust t
        then t
        else case find propositional props of
            Nothing -> applyProvability t rules props
            Just p  -> case p of
                (propType -> DoubleNegation q) -> applyDNeg rules p q props
                (propType -> Conjunction a b)  -> applyConj rules p a b props
                (propType -> Disjunction a b)  -> applyDisj rules p a b props

applyProvability t rules props =
    let impliedWorlds = placesWhere consistency props
        consistency (propType -> Consistency _) = True
        consistency _ = False
        testWorld (p@(propType -> Consistency q), props) = do
             let provabilities = do 
                     p@(propType -> Provability q) <- props
                     [p, q]
             tableau <- runTableau rules (q : neg p : provabilities)
             return $ processWorld rules p tableau
    in foldr mplus t (map testWorld impliedWorlds)

runTableau rules props = applyPropositional rules props

validRules = TableauRules {
    foundF             = \_ -> (),
    foundContradiction = \_ -> (),
    disjRule       = \_ _ _ -> (),
    processWorld  = \_ -> id
}

interpRules = TableauRules {
    foundContradiction = \a -> case a of
       (L _, L _) -> F
       (R _, R _) -> T
       (L n, R _) -> n
       (R n, L _) -> Neg n,
    foundF = \a -> select a F T,
    disjRule = \p -> select p (:\/) (:/\),
    processWorld  = \p -> select p Dia Box
}

-- | Checks the validity of a proposition using a tableau method.
-- Returns 'True' or 'False' according to the validity of the proposition.
--
-- For example we can check Löb's theorem which is one of the axioms of
-- provability logic:
--
-- >>> valid $ Box (Box p :-> p) :-> Box p
-- True
valid :: Prop -> Bool
valid p = isJust $ runTableau validRules [neg p]

valids = [
        T,
        a :-> a,
        Box a :-> Box a,
        Box a :-> Box (Box a),
        Box (Box a :-> a) :-> Box a,
        Box F <-> Box (Dia T),
        let x = p :/\ q :-> r :-> a in Box (Box x :-> x) :-> Box x,
        F :-> Dia p,
        Box (Dia p) :-> Box (Box F :-> F),
        (Box F \/ q /\ Dia (Box F /\ Neg q)) <->
          (Dia (Box F \/ q /\ Dia (Box F /\ Neg q))
          --> q /\ Neg (Box (Box F \/ q /\ Dia (Box F /\ Neg q)
          --> q)))
    ]
invalids = [
        F,
        a :-> Box a,
        Box a :-> a,
        Box (Box a :-> a) :-> a,
        Dia T,
        Box (Dia T),
        Neg (Box F),
        (Box F \/ p /\ Dia (Box F /\ Neg q)) <->
          (Dia (Box F \/ q /\ Dia (Box F /\ Neg q))
          --> q /\ Neg (Box (Box F \/ q /\ Dia (Box F /\ Neg q)
          --> q)))
    ]

regress1 = do
    print $ (and $ map valid valids) &&
            (and $ map (not . valid) invalids)

f0 p = Neg (Box p)

test0 = valid $ let p = Dia T in p <-> f0 p

f1 p = Box p --> Box (Neg p)

test1 = valid $ let p = Box (Box F) --> Box F in p <-> f1 p

width box = foldr max 0 (map length box)

pad len b a = a ++ replicate (len - length a) b

aside a b = let w = width a
                h = max (length a) (length b)
                a' = pad h [] a
                b' = pad h [] b
                a'' = map (pad w ' ') a'
            in zipWith (++) a'' b'

frame a = let w = width a
              h = length a
              strut = replicate h "|"
              rule = "+" ++ replicate w '-' ++ "+"
          in [rule] ++ strut `aside` a `aside` strut ++ [rule]

alt a b = let h = max (length a) (length b)
              strut = replicate h " | "
          in a `aside` strut `aside` b

-- Craig interpolation makes use of "signed" propositions.
data SignedProp a = L { unsign :: a} | R { unsign :: a } deriving (Eq, Ord, Show)

select (L _) l r = l
select (R _) l r = r

instance Functor SignedProp where
    fmap f (L a) = L (f a)
    fmap f (R a) = R (f a)

--unsign (L a) = a
--unsign (R b) = b

instance PropTypeable a => PropTypeable (SignedProp a) where
    propType (L a)    = fmap L (propType a)
    propType (R a)    = fmap R (propType a)
    neg               = fmap neg
    isF               = isF . unsign
    positiveComponent = positiveComponent . unsign
    negative          = negative . unsign

-- | The 'interp' function interpolates between two logical expressions.
-- In particular, given a proposition @A :-> B@, 'interp' finds an "interpolating"
-- proposition @C@ such that @A :-> C@ and @C :-> B@ and such that @C@ contains
-- only the variables that appear in both @A@ and @C@.
--
-- For example:
--
-- >>> interp $ (Neg (p :/\ q) :-> (Neg r :/\ q)) :-> ((t :-> p) :\/ (t :-> Neg r))
-- Just ("p" \/ Neg "r")
--
-- If the proposition is not a theorem then 'interp' returns 'Nothing'
interp (p :-> q) = let t = runTableau interpRules [L p, R (Neg q)]
                   in simplify <$> t
def1 p = T --> p
def2 p = p --> T

-- | In provability logic we can define propositions implicitly.
-- This is known as Beth definability.
--
-- @beth d@ returns a proposition @P@ with the property that
-- @d(Q) -> (P <-> Q)@ is a theorem.
--
-- In order for this to work @d@ needs to satisfy the precondition that it
-- uniquely defines @p@ up to equivalence.
-- I.e. we require that if both
-- @d(P)@ and @d(Q)@ hold, then @P <-> Q@.
-- An error message indicates when this fails to hold.
--
-- >>> beth $ \p -> (Box (p --> q) --> p) /\ (p --> Box q)
-- Just (Box "q" \/ Box "q") -- which of course simplifies to Just (Box "q")
beth :: (Prop -> Prop) -> Maybe Prop
beth d = let p = Letter "__p"
             q = Letter "__q"
             cond = valid $ (d p /\ d q) --> (p <-> q)
         in if not cond
            then error $ show (d p) ++ " doesn't satisfy precondition"
            else interp (d p /\ p --> (d q --> q))

box' a = a /\ Box a

-- | Finds the fixed point of a logical function.
-- Given a function @f@ of type @Prop -\> Prop@, @fixedpoint f@
-- returns a proposition @P@ such that @P \<-\> f(P)@ and @Box (P \<-\> f(P))@.
--
-- It returns 'Nothing' if no such proposition can be found.
--
-- It can be proved that there is always a fixed point if all occurrences of the
-- argument to @f@ live within subexpressions headed by 'Box' (or 'Dia').
--
-- >>> fixedpoint $ \p -> Neg (Box p)
-- Dia T
--
-- (The assertion that this example is a fixed point for the given function
-- is Gödel's second incompleteness theorem.)
fixedpoint f = beth (\p -> box' (p <-> f p))

-- Regression tests
fpexamples = [
        (\p -> Neg (Box p), Dia T),
        (\p -> Box p, T),
        (\p -> Box (Neg p), Box F),
        (\p -> Neg (Box (Neg p)), F),
        (\p -> Neg (Box (Box p)), Dia (Dia T)),
        (\p -> Box p :-> Box (Neg p), Dia (Dia T) \/ Box F),
        (\p -> Box (Neg p :-> Box F) :-> Box (p :-> Box F),
         Dia (Dia (Neg (Box F) /\ Neg (Box F)) /\ Neg (Box F)) \/ Box (Box F)),
        (\p -> Box p :-> q, Dia (Neg q) \/ q /\ q),
        (\p -> Box (p :-> q), Box q),
        (\p -> Box p /\ q, Box q /\ q),
        (\p -> Box (p /\ q), Box q),
        (\p -> q \/ Box p, T),
        (\p -> Neg (Box (q :-> p)), Dia q),
        (\p -> Box (p :-> q) :-> Box (Neg p), Dia (Box F /\ Neg q) \/ Box F),
        (\p -> q /\ (Box (p :-> q) :-> Box (Neg p)), q /\ Box (Neg q)),
        (\p -> Dia p :-> (q /\ Neg (Box (p :-> q))),
         Box F /\ Box F \/ q /\ Dia ((Box F /\ Box F) /\ Neg q)),
        (\p -> Box (Box (p /\ q) /\ Box (p /\ r)), Box (Box q /\ Box r))
    ]

equiv p q = valid (p <-> q)

regress2 = do
    print $ and $ map (\(f, x) -> fromJust (fixedpoint f) `equiv` x) fpexamples

main = do
          regress1
          regress2

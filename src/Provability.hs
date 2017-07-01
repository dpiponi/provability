{-|
Module: Provability

This module provides functionality for working with the provability
logic GL.

Although GL deals with the provability (or not) of propositions in logical systems that are not complete, it is, surprisingly, a complete logic itself.
This means that checking whether a proposition is a theorem is computable.
This module provides tools to test whether a proposition of GL is a theorem.
It also provides a tool for finding fixed points in GL, i.e. propositions @P@ solving an equation of the form @P \<-\> f(P)@, for suitable logical functions @f@.

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
                   dnf,
                   Prop(..),
                   (\/), (/\), (-->), (<--), (<->),
                   fixedpoint,
                   beth,
                   simplify,
                   a, b, c, d, p, q, r, s, t) where

import Control.Applicative
import Control.Arrow
import Control.Monad
import Data.Function
import Data.List
import Data.Maybe
import Text.Show

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
dnf p = foldr1' (/\) T [foldr1' (\/) F q | q <- dnf' p]

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

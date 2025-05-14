{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}
--{-# LANGUAGE InstanceSigs #-}
import Data.Map (Map)
import qualified Data.Set.Monad as Set--implements monad on Set
import Control.Monad
import Data.List
import qualified Data.Bifunctor
data Json = Null
    | JsonBool Bool
    | JsonString String
    | JsonFloat Float
    | JsonList [Json]
    | JsonDict (Map String Json)
    deriving (Show)

--state machine parameterised by arbitrary types
--reduces to the case of a finite automation when states and alphabet are both finite sets e.g. enums
data StateMachine states alphabet = StateMachine {
    transitionFunction :: alphabet -> states -> states,
    initialState :: states,
    isAcceptState :: states -> Bool -- a mathematician might make this a set of accept states, but we need infinite lists to perform the subset construction
}

shiftFront :: [a] -> [Maybe a]
shiftFront xs = Nothing : fmap Just xs

append :: a->[a]->[a]
append x = foldr (:) [x]

shiftEnd :: [a] -> [Maybe a]
shiftEnd xs = append Nothing (fmap Just xs)

consecutivePairs :: [a] -> [(Maybe a, Maybe a)]
consecutivePairs xs = zip (shiftFront xs) (shiftEnd xs)

-- verifies that a single step is accepted by a state machine
-- we use a tuple type here to avoid some awkward partial specialisation + currying later
oneStepAccept :: (Ord states) => StateMachine states alphabet -> (alphabet, (Maybe states, Maybe states)) -> Bool
oneStepAccept (StateMachine _t  initial _acceptFunc) (_letter, (Nothing, Just state)) = state == initial
oneStepAccept (StateMachine t _initial _acceptFunc) (letter, (Just s1, Just s2)) = t letter s1 == s2
oneStepAccept (StateMachine _t _initial acceptFunc) (_letter,  (Just state, Nothing)) = acceptFunc state
oneStepAccept (StateMachine _t _initial _acceptFunc)  (_letter, (Nothing, Nothing)) = False--should never happen in our use of this function

-- verifies a single step of computation by a state machine
oneStepCompute :: (Eq states) => StateMachine states alphabet -> (Maybe alphabet, (Maybe states, Maybe states)) -> Bool
oneStepCompute _ (_, (Nothing, Just _ )) = True
oneStepCompute (StateMachine t _initial _acceptFunc) (Just letter, (Just s1, Just s2)) = t letter s1 == s2
oneStepCompute _ (Nothing, (Just _, Just _)) = False
oneStepCompute _ (_,  (Just _, Nothing)) = True
oneStepCompute (StateMachine _t _initial _acceptFunc)  (_letter, (Nothing, Nothing)) = False--should never happen in our use of this function

--version of zip which preserves longer original length
longZip :: [a] -> [b] -> [(Maybe a, Maybe b)]
longZip [] bs = fmap (\ b -> (Nothing, Just b)) bs
longZip as [] = fmap (\ a -> (Just a,Nothing)) as
longZip (a:as) (b:bs) = (Just a, Just b) : longZip as bs

-- Checks whether the given sequence of states exhibits the computation of the state machine on the given word
-- Lots of screwing around with Maybe here, doesn't feel very clean
exhibitCompute :: (Eq states) => StateMachine states alphabet -> [alphabet] -> [states] -> Bool
exhibitCompute machine word states = exhibitComputeHelper machine (Nothing : fmap Just word) states

exhibitComputeHelper :: (Eq states) => StateMachine states alphabet -> [Maybe alphabet] -> [states] -> Bool
exhibitComputeHelper machine word states = all (oneStepCompute machine) transitionPairs where
    transitionPairs = fmap (Data.Bifunctor.bimap join joinPair) (longZip word (consecutivePairs states)) where
        joinPair Nothing = (Nothing, Nothing)
        joinPair (Just pair) = pair

-- Checks whether the given sequence of states exhibits the *succesful* computation of the state machine on the given word
-- This is the "mathematical" definition of a state machine accepting a word, where the sequence of states required to exist
-- is supplied as an argument
-- (This is likely horribly inefficient - we have to check a condition at the *end* of the
-- input, so a singly linked list is probably not a good choice of data structure here
-- Notice that we traverse the entire list to compute consecutiePairs, traverse it again 
-- for the zip, and then again for the all)
exhibitAccept:: (Ord states) => StateMachine states alphabet -> [alphabet] -> [states] -> Bool
exhibitAccept machine word states = all (oneStepAccept machine) transitionPairs where
    transitionPairs = zip word (consecutivePairs states)

-- computes the outcome of a state machine 
compute :: (Ord states) => StateMachine states alphabet -> [alphabet] -> states
compute (StateMachine transition initial _accept) word  = foldl' (flip transition) initial word

-- performs a foldl and puts intermediate values into a list
-- general recursion code smell, but I couldn't figure out another way to write this
-- I should also maybe consider making this strict
runningFoldl :: (b -> a -> b) -> b -> [a] -> ([b],b)
runningFoldl _trans start [] = ([], start)
runningFoldl trans start (a:as) = (trans start a: fst next, snd next) where
    next = runningFoldl trans (trans start a) as

computeUnfold :: StateMachine states alphabet -> [alphabet] -> ([states], states)
computeUnfold (StateMachine t i _a) word = runningFoldl (flip t) i word

-- law: snd . computeUnfold == compute

-- Checks whether a state machine accepts a word
accept :: (Ord states) => StateMachine states alphabet -> [alphabet] -> Bool
accept (StateMachine t i a) word = a (compute (StateMachine t i a) word)

-- it might be nice to have a version of compute and accept which provides the Boolean output and 
-- additionally "unfolds" the sequence of states into a list


-- we should have the following laws:
-- exhibitAccept machine word states == accept machine word
-- exhibit (StateMachine transition initial acceptFunc) word states == Set.Member (compute (StateMachine transition initial acceptFunc) word) acceptFunc
-- TODO: add more laws here

-- non-deterministic state machine
data NDStateMachine states alphabet = NDStateMachine {
    ndTransitionFunction :: alphabet -> states -> Set.Set states,
    ndInitialState :: states,
    ndIsAcceptState :: states -> Bool
}

-- makes input and output argument of non-deterministic transition function uniform
ndFlatten :: (alphabet -> states -> Set.Set states) -> (alphabet -> Set.Set states -> Set.Set states)
(ndFlatten f) letter = join . fmap (f letter)

-- verifies a single step of computation by a non-deterministic state machine
ndOneStepCompute :: (Ord states) => NDStateMachine states alphabet -> (alphabet, (Maybe states, Maybe states)) -> Bool
ndOneStepCompute _ (_, (Nothing, Just _ )) = True
ndOneStepCompute (NDStateMachine t _initial _acceptFunc) (letter, (Just s1, Just s2)) = Set.member s2 (t letter s1)
ndOneStepCompute _ (_,  (Just _, Nothing)) = True
ndOneStepCompute (NDStateMachine _t _initial _acceptFunc)  (_letter, (Nothing, Nothing)) = False--should never happen in our use of this function

-- verifies a single step of computation by a non-deterministic state machine
ndOneStepAccept :: (Ord states) => NDStateMachine states alphabet -> (alphabet, (Maybe states, Maybe states)) -> Bool
ndOneStepAccept (NDStateMachine _t initial _acceptFunc) (_, (Nothing, Just state )) = initial == state
ndOneStepAccept (NDStateMachine t _initial _acceptFunc) (letter, (Just s1, Just s2)) = Set.member s2 (t letter s1)
ndOneStepAccept (NDStateMachine _t _initial acceptFunc)  (_,  (Just state, Nothing)) = acceptFunc state
ndOneStepAccept _machine (_letter, (Nothing, Nothing)) = False--should never happen in our use of this function

ndExhibitCompute :: (Ord states) => NDStateMachine states alphabet -> [alphabet] -> [states] -> Bool
ndExhibitCompute machine word states = all (ndOneStepCompute machine) transitionPairs where
    transitionPairs = zip word (consecutivePairs states)

ndExhibitAccept :: (Ord states) => NDStateMachine states alphabet -> [alphabet] -> [states] -> Bool
ndExhibitAccept machine word states = all (ndOneStepAccept machine) transitionPairs where
    transitionPairs = zip word (consecutivePairs states)

ndCompute :: (Ord states) => NDStateMachine states alphabet -> [alphabet] -> Set.Set states
ndCompute (NDStateMachine t i _as)  = foldl (flip (ndFlatten t)) (return i)

ndComputeUnfold :: NDStateMachine states alphabet -> [alphabet] -> ([Set.Set states], Set.Set states)
ndComputeUnfold (NDStateMachine t i _a) word = runningFoldl (flip (ndFlatten t))  (return i) word

ndAccept :: (Ord states) => NDStateMachine states alphabet -> [alphabet] -> Bool
ndAccept (NDStateMachine t i a) word = any a (ndCompute (NDStateMachine t i a) word)

-- turns non-deterministic state machine into equivalent state machine
subsetConstruction :: NDStateMachine states alphabet -> StateMachine (Set.Set states) alphabet
subsetConstruction (NDStateMachine t i acceptFunc) = StateMachine (ndFlatten t)  (return i) (any acceptFunc)

-- inclusion of state machines into non-deterministic state machines
ndInclusion :: StateMachine states alphabet -> NDStateMachine states alphabet
ndInclusion (StateMachine t i a) = NDStateMachine expandedTransition i a where
    expandedTransition b = return . t b

-- yes, this is essentially just (haha) Maybe, but it's nice to make our types descriptive of their function
data Augmented alphabet = Simply alphabet | Epsilon

-- variant of non-deterministic state machine with "null" paths
-- note that this is not equivalent to a non-deterministic state machine over arbitrary types
-- because the epsilon-closure may not be computable 
data EpsilonNDStateMachine states alphabet = EpsilonNDStateMachine {
    epsilonNdTransitionFunction :: Augmented alphabet -> states -> Set.Set states,
    episilonNdInitialState :: states,
    epsilonNdIsAcceptState :: states -> Bool
}

-- iterates a function until a fixed point is reached
stabiliseFunc :: (Eq a) => (a -> a) -> a -> [a]
stabiliseFunc f x = x : unfoldr (\ y -> if f y == y then Nothing else Just (f y,f y)) x

-- iterate and put values into list until output stabilises
stabiliseList :: (Eq b) => (b -> [b]) -> b -> [b]
stabiliseList func b = join (stabiliseFunc (join . fmap func) [b])

-- iterate and put values into set until output stabilises
-- This is a horrible definition - should be able to do this "natively" on sets
-- I've not got a good handle on how to generalise unfold yet...)
stabilise :: (Ord b) => (b -> Set.Set b) -> b -> Set.Set b
stabilise function element = Set.fromList (stabiliseList (Set.toList . function) element)

-- takes the epsilon closure of a state under the given transition function
epsilonClosure :: (Ord states) => (Augmented alphabet -> states -> Set.Set states) -> states -> Set.Set states
epsilonClosure transition = stabilise (transition Epsilon)

-- verifies a single step of computation by an epsilon-non-deterministic state machine
epsilonNdOneStepCompute :: (Ord states) => EpsilonNDStateMachine states alphabet -> (alphabet, (Maybe states, Maybe states)) -> Bool
epsilonNdOneStepCompute _ (_, (Nothing, Just _ )) = True
epsilonNdOneStepCompute (EpsilonNDStateMachine t _initial _acceptFunc) (letter, (Just s1, Just s2)) = Set.member s2 (epsilonTransition =<< regularTransition letter s1) where
    regularTransition l = t (Simply l)
    epsilonTransition = epsilonClosure t
epsilonNdOneStepCompute _ (_,  (Just _, Nothing)) = True
epsilonNdOneStepCompute (EpsilonNDStateMachine _t _initial _acceptFunc)  (_letter, (Nothing, Nothing)) = False--should never happen in our use of this function

-- verifies a single step of computation by an epsilon-non-deterministic state machine
epsilonNdOneStepAccept :: (Ord states) => EpsilonNDStateMachine states alphabet -> (alphabet, (Maybe states, Maybe states)) -> Bool
epsilonNdOneStepAccept (EpsilonNDStateMachine _t initial _acceptFunc) (_, (Nothing, Just state )) = initial == state
epsilonNdOneStepAccept (EpsilonNDStateMachine t _initial _acceptFunc) (letter, (Just s1, Just s2)) = Set.member s2 (epsilonTransition =<< regularTransition letter s1) where
    regularTransition l = t (Simply l)
    epsilonTransition = epsilonClosure t
epsilonNdOneStepAccept (EpsilonNDStateMachine _t _initial acceptFunc)  (_,  (Just state, Nothing)) = acceptFunc state
epsilonNdOneStepAccept _machine (_letter, (Nothing, Nothing)) = False--should never happen in our use of this function

epsilonNdExhibitCompute :: (Ord states) => EpsilonNDStateMachine states alphabet -> [alphabet] -> [states] -> Bool
epsilonNdExhibitCompute machine word states = all (epsilonNdOneStepCompute machine) transitionPairs where
    transitionPairs = zip word (consecutivePairs states)

epsilonNdExhibitSuccess :: (Ord states) => EpsilonNDStateMachine states alphabet -> [alphabet] -> [states] -> Bool
epsilonNdExhibitSuccess machine word states = all (epsilonNdOneStepAccept machine) transitionPairs where
    transitionPairs = zip word (consecutivePairs states)

-- the definition here is horrible because of the partial application needed to convert alphabet to Augmented alphabet
-- maybe this can be cleaned up somehow
epsilonNdCompute :: (Ord states) => EpsilonNDStateMachine states alphabet -> [alphabet] -> Set.Set states
epsilonNdCompute (EpsilonNDStateMachine t i _as) = augmentedFoldl (flip flattenedTransition) (return i) where
    --flattenedTransition letter stateSet = join (fmap (epsilonClosure t) ((join . fmap (t  letter)) stateSet))
    flattenedTransition letter stateSet = epsilonClosure t =<< t  letter =<< stateSet
    augmentedFoldl f = foldl g where
        g y x = f y (Simply x)

epsilonNdComputeUnfold :: EpsilonNDStateMachine states alphabet -> [alphabet] -> ([Set.Set states], Set.Set states)
epsilonNdComputeUnfold (EpsilonNDStateMachine t i _a) word = runningFoldl (flip (ndFlatten t)) (return i) (fmap Simply word)

epsilonNdAccept :: (Ord states) => EpsilonNDStateMachine states alphabet -> [alphabet] -> Bool
epsilonNdAccept (EpsilonNDStateMachine t i a) word = any a (epsilonNdCompute (EpsilonNDStateMachine t i a) word)

-- inclusion of nondeterministic state machines into epsilon-nondeterministic state machines
epsilonNdInclusion :: NDStateMachine states alphabet -> EpsilonNDStateMachine states alphabet
epsilonNdInclusion (NDStateMachine t i a) = EpsilonNDStateMachine expandedTransition i a where
    expandedTransition (Simply letter) ss = t letter ss
    expandedTransition Epsilon ss = return ss

-- It would be nice to have a function EpsilonNDStateMachine -> NDStateMachine which composes with subsetConstruction to give this function
-- however, I can't get the initial states right for such a function. I could modify the transition function to take the epsilon closure at both the start
-- and the end, but that feels rather inefficient
epsilonSubsetConstruction :: (Ord states) => EpsilonNDStateMachine states alphabet -> StateMachine (Set.Set states) alphabet
epsilonSubsetConstruction (EpsilonNDStateMachine t i a) = StateMachine closedTransition (epsilonClosure t i) (any a) where
    closedTransition letter ss = epsilonClosure t =<< ndFlatten t (Simply letter) ss


--alphabets and regular operations
newtype Alphabet letters = Alphabet ([letters] -> Bool)

-- splits string at each index
splits :: [a] -> [([a],[a])]
splits [] = [([],[])]
splits (a:as) = ([], a:as) : fmap (\ (xs, ys) -> (a:xs,ys) ) (splits as)

nonEmptySplits :: [a] -> [([a],[a])]
nonEmptySplits word = filter (\ (xs, ys) ->  not (null xs) && not (null ys)) (splits word)

cartesianProduct :: [a] -> [b] -> [(a,b)]
cartesianProduct xs ys = [(x,y) | x <- xs, y <- ys]

--finds all ways of splitting a string into consecutive substrings
decompositions :: [a] -> [[[a]]]
decompositions [] = [[]]
decompositions [x] = [[[x]]] --needs to be specified manually else the recursion gives [[[x]], [[x]]] and that throws everything off
decompositions (x:xs) = join [map (\ ys -> [x]:ys) (decompositions xs),map (appendToFirst x) (decompositions xs)] where
    appendToFirst :: a -> [[a]] -> [[a]]
    appendToFirst y [] = [[y]]
    appendToFirst y (z:zs) = (y:z):zs

alphabetUnion :: Alphabet letters -> Alphabet letters -> Alphabet letters
alphabetUnion (Alphabet predicate1) (Alphabet predicate2) = Alphabet (\ x -> predicate1 x || predicate2 x)

alphabetConcatenation :: Alphabet letters -> Alphabet letters -> Alphabet letters
alphabetConcatenation (Alphabet pred1) (Alphabet pred2) = Alphabet (any (\ (x,y) -> pred1 x && pred2 y) . splits )

kleeneStar :: Alphabet letters -> Alphabet letters
kleeneStar (Alphabet predicate) = Alphabet (any (all predicate) . decompositions )

-- state machine which recognises the intersection of languages recognised by each state machine
stateMachineIntersection :: StateMachine states1 alphabet -> StateMachine states2 alphabet -> StateMachine (states1, states2) alphabet
stateMachineIntersection (StateMachine t1 i1 a1) (StateMachine t2 i2 a2) = StateMachine transition (i1, i2) (\ (x,y) -> a1 x && a2 y) where
    transition w (state1, state2) = (t1 w state1, t2 w state2)

-- state machine which recognises the union of languages recognised by each state machine
stateMachineUnion :: StateMachine states1 alphabet -> StateMachine states2 alphabet -> StateMachine (states1, states2) alphabet
stateMachineUnion (StateMachine t1 i1 a1) (StateMachine t2 i2 a2) = StateMachine transition (i1, i2) (\ (x,y) -> a1 x || a2 y) where
    transition w (state1, state2) = (t1 w state1, t2 w state2)

--analogous to a "based set" in mathematics
--I would call it "Pointed", but seems there is already a typeclass with that name
data Based t = Base ()
    | Original t
    deriving (Show, Eq, Ord)

instance Functor Based where
    fmap _ (Base ()) = Base ()
    fmap func (Original x) = Original (func x)


epsilonNdStateMachineUnion :: (Ord states1, Ord states2) => EpsilonNDStateMachine states1 alphabet -> EpsilonNDStateMachine states2 alphabet -> EpsilonNDStateMachine (Based (Either states1 states2)) alphabet
epsilonNdStateMachineUnion (EpsilonNDStateMachine trans1 init1 accept1) (EpsilonNDStateMachine trans2 init2 accept2) = EpsilonNDStateMachine trans initState isAccept where
    initState = Base ()

    isAccept (Base ()) = False
    isAccept (Original (Left x)) = accept1 x
    isAccept (Original (Right x)) = accept2 x

    trans Epsilon (Base ()) = Set.union (fmap (Original . Left) (Set.singleton init1)) (fmap (Original . Right) (Set.singleton init2))
    trans (Simply _letter) (Base ()) = fmap Base Set.empty -- use of Base here is arbitrary, could use Original . Left or Original . Right
    trans letter (Original (Left state)) = fmap (Original. Left) (trans1 letter state)
    trans letter (Original (Right state)) = fmap (Original . Right) (trans2 letter state)


epsilonNdStateMachineConcatenation :: (Ord states1, Ord states2) => EpsilonNDStateMachine states1 alphabet -> EpsilonNDStateMachine states2 alphabet -> EpsilonNDStateMachine (Either states1 states2) alphabet
epsilonNdStateMachineConcatenation (EpsilonNDStateMachine transLeft initLeft acceptLeft) (EpsilonNDStateMachine transRight initRight acceptRight)  = EpsilonNDStateMachine trans initial acceptstates where
    initial = Left initLeft

    acceptstates (Left _) = False
    acceptstates (Right state) = acceptRight state

    trans Epsilon (Left state) = if acceptLeft state then Set.union (fmap Left (transLeft Epsilon state)) (Set.singleton (Right initRight)) else undefined
    trans (Simply letter) (Left state) = fmap Left (transLeft (Simply letter) state)
    trans letter (Right state) = fmap Right (transRight letter state)


-- state machine which recognises the Kleene star of the language recognised by the original state machine
stateMachineKleeneStar :: (Ord states) => EpsilonNDStateMachine states alphabet -> EpsilonNDStateMachine (Based states) alphabet
stateMachineKleeneStar (EpsilonNDStateMachine trans initial isAccept) = EpsilonNDStateMachine kleeneTrans kleeneInitial isKleeneAccept where

    isKleeneAccept (Base ()) = False
    isKleeneAccept (Original x) = isAccept x

    kleeneInitial = Base ()

    kleeneTrans Epsilon (Base ()) = Set.singleton (Original initial)
    kleeneTrans (Simply _letter) (Base ()) = Set.empty
    kleeneTrans Epsilon (Original state) = if isAccept state then Set.union (Set.singleton (Original initial)) (fmap Original (trans Epsilon state)) else fmap Original (trans Epsilon state)
    kleeneTrans (Simply letter) (Original state) = fmap Original (trans (Simply letter) state)

{-
data GoodStates = Start
    | G 
    | O1 
    | O2 
    | D
    deriving (Show, Eq, Ord)
-}

data GoodStates = Start
    | G
    | O1
    | O2
    | D
    | Bin
    deriving (Show, Eq, Ord)

data TestAlphabet = GoodToBad
    | BadToGood
    deriving (Show)


testMachine1 :: EpsilonNDStateMachine GoodStates Char
testMachine1 = EpsilonNDStateMachine trans initial isAccept where
    initial = Start
    isAccept x = x == D

    trans Epsilon G = Set.singleton D
    trans (Simply 'g') Start = Set.singleton G
    trans (Simply 'o') G  = Set.singleton O1
    trans (Simply 'o') O1  = Set.singleton O2
    trans (Simply 'd') O2  = Set.singleton D
    trans _letter _state = Set.empty

testMachine2 :: NDStateMachine GoodStates Char
testMachine2 = NDStateMachine trans initial isAccept where
    initial = Start
    isAccept x = x == D

    trans 'g' Start = Set.singleton G
    trans 'o' G  = Set.singleton O1
    trans 'o' O1  = Set.singleton O2
    trans 'd' O2  = Set.singleton D
    trans _letter _state = Set.empty

testMachine3 :: StateMachine GoodStates Char
testMachine3 = StateMachine trans initial isAccept where
    initial = Start
    isAccept x = x == D
    trans 'g' Start = G
    trans 'o' G  = O1
    trans 'o' O1  = O2
    trans 'd' O2  = D
    trans _letter _state = Bin

testStabilise :: GoodStates -> GoodStates
testStabilise G = O1
testStabilise O1 = O2
testStabilise O2 = D
testStabilise D = D
testStabilise Bin = Bin
testStabilise Start = Start

main :: IO()
main = print (exhibitCompute testMachine3 "go" [Start, G, O1])
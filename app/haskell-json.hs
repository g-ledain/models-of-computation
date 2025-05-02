import Data.Map (Map)
import qualified Data.Set.Monad as Set--implements monad on Set
import Control.Applicative
import Control.Monad
import Data.List

--Set.Monad doesn't export cartesianProduct, so we'll have to do it ourselves
--Definition taken from https://hackage.haskell.org/package/containers-0.8/docs/Data-Set.html#v:cartesianProduct
cartesianProduct :: (Ord t, Ord s) => Set.Set t -> Set.Set s -> Set.Set (t,s)
cartesianProduct xs ys = Set.fromList $ Control.Applicative.liftA2 (,) (Set.toList xs) (Set.toList ys)

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
    transitionFunction :: alphabet -> states -> states,--easier to foldr when arguments in this order
    initialState :: states,
    acceptStates :: Set.Set states
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
oneStepAccept (StateMachine _t  initial _acceptSet) (_letter, (Nothing, Just state)) = state == initial
oneStepAccept (StateMachine t _initial _acceptSet) (letter, (Just s1, Just s2)) = t letter s1 == s2
oneStepAccept (StateMachine _t _initial acceptSet) (_letter,  (Just state, Nothing)) = Set.member state acceptSet
oneStepAccept (StateMachine _t _initial _acceptSet)  (_letter, (Nothing, Nothing)) = False--should never happen in our use of this function

-- verifies a single step of computation by a state machine
oneStepCompute :: (Eq states) => StateMachine states alphabet -> (alphabet, (Maybe states, Maybe states)) -> Bool
oneStepCompute _ (_, (Nothing, Just _ )) = True
oneStepCompute (StateMachine t _initial _acceptSet) (letter, (Just s1, Just s2)) = t letter s1 == s2
oneStepCompute _ (_,  (Just _, Nothing)) = True
oneStepCompute (StateMachine _t _initial _acceptSet)  (_letter, (Nothing, Nothing)) = False--should never happen in our use of this function

-- Checks whether the given sequence of states exhibits the computation of the state machine on the given word
exhibitCompute :: (Eq states) => StateMachine states alphabet -> [alphabet] -> [states] -> Bool
exhibitCompute machine word states = all (oneStepCompute machine) transitionPairs where
    transitionPairs = zip word (consecutivePairs states)

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
compute (StateMachine transition initial _accept) word  = foldr transition initial word

-- performs a foldr and puts intermediate values into a list
-- general recursion code smell, but I couldn't figure out another way to write this
runningFoldr :: (a -> b -> b) -> b -> [a] -> ([b],b)
runningFoldr _trans start [] = ([], start)
runningFoldr trans start (b:bs) = (trans b start: fst (runningFoldr trans (trans b start) bs), trans b start)

computeUnfold :: StateMachine states alphabet -> [alphabet] -> ([states], states)
computeUnfold (StateMachine t i _a) word = runningFoldr t i word

-- law: snd . computeUnfold == compute

-- Checks whether a state machine accepts a word
accept :: (Ord states) => StateMachine states alphabet -> [alphabet] -> Bool
accept (StateMachine t i a) word = Set.member (compute (StateMachine t i a) word) a

-- it might be nice to have a version of compute and accept which provides the Boolean output and 
-- additionally "unfolds" the sequence of states into a list


-- we should have the following laws:
-- exhibitAccept machine word states == accept machine word
-- exhibit (StateMachine transition initial acceptSet) word states == Set.Member (compute (StateMachine transition initial acceptSet) word) acceptSet
-- TODO: add more laws here

stateProduct :: (Ord states1, Ord states2) => StateMachine states1 alphabet -> StateMachine states2 alphabet -> StateMachine (states1, states2) alphabet
stateProduct (StateMachine t1 i1 a1) (StateMachine t2 i2 a2) = StateMachine transition (i1, i2) (cartesianProduct a1 a2) where
    transition w (state1, state2) = (t1 w state1, t2 w state2)

-- non-deterministic state machine
data NDStateMachine states alphabet = NDStateMachine {
    ndTransitionFunction :: alphabet -> states -> Set.Set states,--easier to foldr when arguments in this order
    ndInitialState :: states,
    ndAcceptStates :: Set.Set states
}

-- verifies a single step of computation by a non-deterministic state machine
ndOneStepCompute :: (Ord states) => NDStateMachine states alphabet -> (alphabet, (Maybe states, Maybe states)) -> Bool
ndOneStepCompute _ (_, (Nothing, Just _ )) = True
ndOneStepCompute (NDStateMachine t _initial _acceptSet) (letter, (Just s1, Just s2)) = Set.member s2 (t letter s1)
ndOneStepCompute _ (_,  (Just _, Nothing)) = True
ndOneStepCompute (NDStateMachine _t _initial _acceptSet)  (_letter, (Nothing, Nothing)) = False--should never happen in our use of this function

-- verifies a single step of computation by a non-deterministic state machine
ndOneStepAccept :: (Ord states) => NDStateMachine states alphabet -> (alphabet, (Maybe states, Maybe states)) -> Bool
ndOneStepAccept (NDStateMachine _t initial _acceptSet) (_, (Nothing, Just state )) = initial == state
ndOneStepAccept (NDStateMachine t _initial _acceptSet) (letter, (Just s1, Just s2)) = Set.member s2 (t letter s1)
ndOneStepAccept (NDStateMachine _t _initial acceptSet)  (_,  (Just state, Nothing)) = Set.member state acceptSet
ndOneStepAccept _machine (_letter, (Nothing, Nothing)) = False--should never happen in our use of this function

ndExhibitCompute :: (Ord states) => NDStateMachine states alphabet -> [alphabet] -> [states] -> Bool
ndExhibitCompute machine word states = all (ndOneStepCompute machine) transitionPairs where
    transitionPairs = zip word (consecutivePairs states)

ndExhibitAccept :: (Ord states) => NDStateMachine states alphabet -> [alphabet] -> [states] -> Bool
ndExhibitAccept machine word states = all (ndOneStepAccept machine) transitionPairs where
    transitionPairs = zip word (consecutivePairs states)

ndCompute :: (Ord states) => NDStateMachine states alphabet -> [alphabet] -> Set.Set states
ndCompute (NDStateMachine t i _as)  = foldr flattenedTransition  (return i)  where
    flattenedTransition bs = (t bs =<<)

ndComputeUnfold :: NDStateMachine states alphabet -> [alphabet] -> ([Set.Set states], Set.Set states)
ndComputeUnfold = undefined

ndAccept :: (Ord states) => StateMachine states alphabet -> [alphabet] -> Bool
ndAccept (StateMachine t i a) word = Set.member (compute (StateMachine t i a) word) a

-- turns non-deterministic state machine into equivalent state machine
subsetConstruction :: NDStateMachine states alphabet -> StateMachine (Set.Set states) alphabet
subsetConstruction (NDStateMachine t i as) = StateMachine flattenedTransition (return i) (return as) where
    flattenedTransition bs = (t bs =<<)

-- inclusion of state machines into non-deterministic state machines
ndInclusion :: StateMachine states alphabet -> NDStateMachine states alphabet
ndInclusion (StateMachine t i a) = NDStateMachine expandedTransition i a where
    expandedTransition b = return . t b

data Augmented alphabet = Augmented alphabet | Epsilon

-- variant of non-deterministic state machine with "null" paths
-- note that this is not equivalent to a non-deterministic state machine over arbitrary types
-- because taking the epsilon-closure may not be computable 
data EpsilonNDStateMachine states alphabet = EpsilonNDStateMachine {
    epsilonNdTransitionFunction :: Augmented alphabet -> states -> Set.Set states,--easier to foldr when arguments in this order
    episilonNdInitialState :: states,
    epsilonNdAcceptStates :: Set.Set states
}

-- iterates a function until a fixed point is reached
stabiliseFunc :: (Eq a) => (a -> a) -> a -> [a]
stabiliseFunc f x = unfoldr (\ y -> if f y == y then Nothing else Just (f y, y)) x

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

epsilonNdExhibitCompute :: EpsilonNDStateMachine states alphabet -> [alphebet] -> [states] -> Bool
epsilonNdExhibitCompute = undefined

epsilonNdExhibitSuccess :: EpsilonNDStateMachine states alphabet -> [alphabet] -> [states] -> Bool
epsilonNdExhibitSuccess = undefined

epsilonNdCompute :: EpsilonNDStateMachine states alphabet -> [alphabet] -> Set.Set states
epsilonNdCompute = undefined

epsilonNdComputeUnfold :: EpsilonNDStateMachine states alphabet -> [alphabet] -> ([Set.Set states], Set.Set states)
epsilonNdComputeUnfold = undefined

epsilonNdAccept :: EpsilonNDStateMachine states alphabet -> [alphabet] -> Bool
epsilonNdAccept = undefined

squareAdd :: Int -> Int -> Int
squareAdd x y = x*x + y

main :: IO()
main = print (runningFoldr squareAdd 0 [1, 2, 3, 4]) 
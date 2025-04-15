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

oneStep :: (Ord states) => StateMachine states alphabet -> (alphabet, (Maybe states, Maybe states)) -> Bool
oneStep (StateMachine _t  initial _acceptSet) (_letter, (Nothing, Just state)) = state == initial
oneStep (StateMachine t _initial _acceptSet) (letter, (Just s1, Just s2)) = t letter s1 == s2
oneStep (StateMachine _t _initial acceptSet) (_letter,  (Just state, Nothing)) = Set.member state acceptSet
oneStep (StateMachine _t _initial _acceptSet)  (_letter, (Nothing, Nothing)) = False--should never happen in our use of this function

--checks whether the given sequence of states exhibits the computation of the state machine on the given word
exhibit :: (Ord states) => StateMachine states alphabet -> [alphabet] -> [states] -> Bool
exhibit machine word states = all (oneStep machine) transitionPairs where
    transitionPairs = zip word (consecutivePairs states)

compute :: (Ord states) => StateMachine states alphabet -> [alphabet] -> states
compute (StateMachine transition initial _accept)  = foldr transition initial

accept :: (Ord states) => StateMachine states alphabet -> [alphabet] -> Bool
accept (StateMachine t i a) word = Set.member (compute (StateMachine t i a) word) a


-- we should have the following laws:
-- exhibit machine word states == accept machine word
-- exhibit (StateMachine transition initial acceptSet) word states == Set.Member (compute (StateMachine transition initial acceptSet) word) acceptSet

stateProduct :: (Ord states1, Ord states2) => StateMachine states1 alphabet -> StateMachine states2 alphabet -> StateMachine (states1, states2) alphabet
stateProduct (StateMachine t1 i1 a1) (StateMachine t2 i2 a2) = StateMachine transition (i1, i2) (cartesianProduct a1 a2) where
    transition w (state1, state2) = (t1 w state1, t2 w state2)

data NDStateMachine states alphabet = NDStateMachine {
    ndTransitionFunction :: alphabet -> states -> Set.Set states,--easier to foldr when arguments in this order
    ndInitialState :: states,
    ndAcceptStates :: Set.Set states
}

ndCompute :: (Ord states) => NDStateMachine states alphabet -> [alphabet] -> Set.Set states
ndCompute (NDStateMachine t i _as)  = foldr flattenedTransition  (return i)  where
    flattenedTransition bs = (t bs =<<)

subsetConstruction :: NDStateMachine states alphabet -> StateMachine (Set.Set states) alphabet
subsetConstruction (NDStateMachine t i as) = StateMachine flattenedTransition (return i) (return as) where
    flattenedTransition bs = (t bs =<<)

ndInclusion :: StateMachine states alphabet -> NDStateMachine states alphabet
ndInclusion (StateMachine t i a) = NDStateMachine expandedTransition i a where
    expandedTransition b = return . t b

data Augmented alphabet = Augmented alphabet | Epsilon

data EpsilonNDStateMachine states alphabet = EpsilonNDStateMachine {
    epsilonNdTransitionFunction :: Augmented alphabet -> states -> Set.Set states,--easier to foldr when arguments in this order
    episilonNdInitialState :: states,
    epsilonNdAcceptStates :: Set.Set states
}

stabiliseList :: (Eq b) => (b -> [b]) -> b -> [b]
stabiliseList func b = join (stabiliseFunc (join . fmap func ) [b])

stabiliseFunc :: (Eq a) => (a -> a) -> a -> [a]
stabiliseFunc f x = unfoldr (\ y -> if f y == y then Nothing else Just (f y, y)) x

--iterate until output stabilises
--this is a horrible definition - should be able to do this "natively" on lists
--I've not got a good handle on how to generalise unfold yet...
stabilise :: (Ord b) => (b -> Set.Set b) -> b -> Set.Set b
stabilise function element = Set.fromList (stabiliseList (Set.toList . function) element)

--takes the epsilon closure of a state under the given transition function
epsilonClosure :: (Ord states) => (Augmented alphabet -> states -> Set.Set states) -> states -> Set.Set states
epsilonClosure transition = stabilise (transition Epsilon)

main :: IO()
main = print (consecutivePairs ["test1", "test2"])
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# HLINT ignore "Eta reduce" #-}
--{-# LANGUAGE InstanceSigs #-}
import Data.Map (Map)
import qualified Data.Set.Monad as Set--implements monad on Set
import Control.Monad
import Data.List
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

-- performs a foldl and puts intermediate values into a list
-- consider trying to turn this into a fold (I couldn't figure out how)
-- I should also maybe consider making this strict
runningFoldl :: (b -> a -> b) -> b -> [a] -> ([b],b)
runningFoldl _trans start [] = ([], start)
runningFoldl trans start (a:as) = (trans start a: fst next, snd next) where
    next = runningFoldl trans (trans start a) as

exhibitCompute :: (Ord states) => StateMachine states alphabet -> [alphabet] -> [states] -> Bool
exhibitCompute _machine [] [_state] = True
exhibitCompute machine@(StateMachine trans _initial _acceptFunc) (letter:letters) (first:second:rest) = trans letter first == second && exhibitCompute machine letters (second:rest)
exhibitCompute _ _ _ = False

exhibitComputeToAcceptState :: (Ord states) => StateMachine states alphabet -> [alphabet] -> [states] -> Bool
exhibitComputeToAcceptState (StateMachine _trans _initial acceptFunc) [] [state] = acceptFunc state
exhibitComputeToAcceptState machine@(StateMachine trans _initial _acceptFunc) (letter:letters) (first:second:rest) = trans letter first == second && exhibitComputeToAcceptState machine letters (second:rest)
exhibitComputeToAcceptState _ _ _ = False

exhibitAccept :: (Ord states) => StateMachine states alphabet -> [alphabet] -> [states] -> Bool
exhibitAccept machine word states@(start:_rest) = start == initialState machine && exhibitComputeToAcceptState machine word states
exhibitAccept _ _ _ = False

-- computes the outcome of a state machine 
compute :: (Ord states) => StateMachine states alphabet -> [alphabet] -> states
compute (StateMachine transition initial _accept) word  = foldl' (flip transition) initial word

computeUnfold :: StateMachine states alphabet -> [alphabet] -> ([states], states)
computeUnfold (StateMachine t i _a) word = runningFoldl (flip t) i word

-- Checks whether a state machine accepts a word
accept :: (Ord states) => StateMachine states alphabet -> [alphabet] -> Bool
accept (StateMachine t i a) word = a (compute (StateMachine t i a) word)


-- we should have the following laws:
-- exhibitAccept machine word states == accept machine word
-- exhibit (StateMachine transition initial acceptFunc) word states == Set.Member (compute (StateMachine transition initial acceptFunc) word) acceptFunc
-- law: snd . computeUnfold == compute
-- TODO: add more laws here

-- non-deterministic state machine
data NDStateMachine states alphabet = NDStateMachine {
    ndTransitionFunction :: alphabet -> states -> Set.Set states,
    ndInitialState :: states,
    ndIsAcceptState :: states -> Bool
}

-- makes input and output argument of non-deterministic transition function uniform
ndFlatten :: (alphabet -> states -> Set.Set states) -> (alphabet -> Set.Set states -> Set.Set states)
(ndFlatten f) letter = (f letter =<<)

ndExhibitCompute :: (Ord states) => NDStateMachine states alphabet -> [alphabet] -> [states] -> Bool
ndExhibitCompute _machine [] [_state] = True
ndExhibitCompute machine@(NDStateMachine trans _initial _acceptFunc) (letter:letters) (first:second:rest) = Set.member second (trans letter first)  && ndExhibitCompute machine letters (second:rest)
ndExhibitCompute _ _ _ = False

-- helper function for ndExhibitAccept
-- determines whether the word exhibits the computation *and* whether the computation ends in an accept state
ndExhibitComputeToAcceptState :: (Ord states) => NDStateMachine states alphabet -> [alphabet] -> [states] -> Bool
ndExhibitComputeToAcceptState (NDStateMachine _trans _start isAccept) [] [state] = isAccept state
ndExhibitComputeToAcceptState machine@(NDStateMachine trans _initial _acceptFunc) (letter:letters) (first:second:rest) = Set.member second (trans letter first)  && ndExhibitCompute machine letters (second:rest)
ndExhibitComputeToAcceptState _ _ _ = False

ndExhibitAccept :: (Ord states) => NDStateMachine states alphabet -> [alphabet] -> [states] -> Bool
ndExhibitAccept machine@(NDStateMachine _trans initial _isAccept) word states@(first:_rest) = initial == first && ndExhibitComputeToAcceptState machine word states
ndExhibitAccept _ _ _ = False

ndCompute :: (Ord states) => NDStateMachine states alphabet -> [alphabet] -> Set.Set states
ndCompute (NDStateMachine t i _as)  = foldl (flip (ndFlatten t)) (return i)

ndComputeUnfold :: NDStateMachine states alphabet -> [alphabet] -> ([Set.Set states], Set.Set states)
ndComputeUnfold (NDStateMachine t i _a) word = runningFoldl (flip (ndFlatten t))  (return i) word

ndAccept :: (Ord states) => NDStateMachine states alphabet -> [alphabet] -> Bool
ndAccept (NDStateMachine t i a) word = any a (ndCompute (NDStateMachine t i a) word)

-- inclusion of state machines into non-deterministic state machines
ndInclusion :: StateMachine states alphabet -> NDStateMachine states alphabet
ndInclusion (StateMachine t i a) = NDStateMachine expandedTransition i a where
    expandedTransition b = return . t b

-- turns non-deterministic state machine into equivalent state machine
subsetConstruction :: NDStateMachine states alphabet -> StateMachine (Set.Set states) alphabet
subsetConstruction (NDStateMachine t i acceptFunc) = StateMachine (ndFlatten t)  (return i) (any acceptFunc)

-- yes, this is essentially just (haha) Maybe, but it's nice to make our types descriptive of their function
data Augmented alphabet = Simply alphabet | Epsilon deriving (Eq, Ord, Show)

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

epsilonNdExhibitCompute :: (Ord states) => EpsilonNDStateMachine states alphabet -> [alphabet] -> [states] -> Bool
epsilonNdExhibitCompute machine@(EpsilonNDStateMachine trans _initial _acceptFunc) (letter:letters) (first:second:rest) = Set.member second (epsilonClosure trans =<< trans (Simply letter) first)  && epsilonNdExhibitCompute machine letters (second:rest)
epsilonNdExhibitCompute _ _ _ = False

epsilonNdExhibitComputeToAcceptState :: (Ord states) => EpsilonNDStateMachine states alphabet -> [alphabet] -> [states] -> Bool
epsilonNdExhibitComputeToAcceptState (EpsilonNDStateMachine _trans _initial acceptFunc) [] [state] = acceptFunc state
epsilonNdExhibitComputeToAcceptState machine@(EpsilonNDStateMachine trans _initial _acceptFunc) (letter:letters) (first:second:rest) = Set.member second (epsilonClosure trans =<< trans (Simply letter) first)  && epsilonNdExhibitCompute machine letters (second:rest)
epsilonNdExhibitComputeToAcceptState _ _ _ = False

epsilonNdExhibitSuccess :: (Ord states) => EpsilonNDStateMachine states alphabet -> [alphabet] -> [states] -> Bool
epsilonNdExhibitSuccess machine@(EpsilonNDStateMachine _trans initial _acceptFunc) word states@(first:_rest) = first == initial && epsilonNdExhibitComputeToAcceptState machine word states
epsilonNdExhibitSuccess _ _ _ = False

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
newtype Language letters = Language ([letters] -> Bool)

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
decompositions (x:xs) = join [map (singletonAtFront x) tailDecomps, map (appendToFirst x) tailDecomps] where
    tailDecomps = decompositions xs
    appendToFirst :: a -> [[a]] -> [[a]]
    appendToFirst y [] = [[y]]
    appendToFirst y (z:zs) = (y:z):zs
    singletonAtFront :: a -> [[a]] -> [[a]]
    singletonAtFront y zs = [y]:zs

languageUnion :: Language letters -> Language letters -> Language letters
languageUnion (Language predicate1) (Language predicate2) = Language (\ x -> predicate1 x || predicate2 x)

languageConcatenation :: Language letters -> Language letters -> Language letters
languageConcatenation (Language pred1) (Language pred2) = Language (any (\ (x,y) -> pred1 x && pred2 y) . splits )

kleeneStar :: Language letters -> Language letters
kleeneStar (Language predicate) = Language (any (all predicate) . decompositions )

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


data Regex alphabet = Empty 
    | FromAlphabet (Augmented alphabet)
    | Union (Regex alphabet) (Regex alphabet)
    | Concatenation (Regex alphabet) (Regex alphabet)
    | KleeneStar (Regex alphabet)
    deriving (Eq, Ord, Show)

-- rather defeats the point of constructing state machines, but useful to test that the
-- two approaches are equivalent, and the pattern-matching makes it too nice not to
-- implement it this way
languageFromRegex :: (Eq alphabet) => Regex alphabet -> Language alphabet
languageFromRegex Empty = Language (const False)
languageFromRegex (FromAlphabet Epsilon) = Language (== [])
languageFromRegex (FromAlphabet (Simply letter)) = Language (==[letter])
languageFromRegex (Union regex1 regex2) = languageUnion (languageFromRegex regex1) (languageFromRegex regex2)
languageFromRegex (Concatenation regex1 regex2) = languageConcatenation (languageFromRegex regex1) (languageFromRegex regex2)
languageFromRegex (KleeneStar regex) = kleeneStar (languageFromRegex regex)

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

epsilonNdStateMachineUnionWrapper :: AgnosticStateMachine alphabet -> AgnosticStateMachine alphabet -> AgnosticStateMachine alphabet
epsilonNdStateMachineUnionWrapper (EraseStates machine1) (EraseStates machine2) = EraseStates (epsilonNdStateMachineUnion machine1 machine2)


epsilonNdStateMachineConcatenation :: (Ord states1, Ord states2) => EpsilonNDStateMachine states1 alphabet -> EpsilonNDStateMachine states2 alphabet -> EpsilonNDStateMachine (Either states1 states2) alphabet
epsilonNdStateMachineConcatenation (EpsilonNDStateMachine transLeft initLeft acceptLeft) (EpsilonNDStateMachine transRight initRight acceptRight)  = EpsilonNDStateMachine trans initial acceptstates where
    initial = Left initLeft

    acceptstates (Left _) = False
    acceptstates (Right state) = acceptRight state

    trans Epsilon (Left state) = if acceptLeft state then Set.union (fmap Left (transLeft Epsilon state)) (Set.singleton (Right initRight)) else undefined
    trans (Simply letter) (Left state) = fmap Left (transLeft (Simply letter) state)
    trans letter (Right state) = fmap Right (transRight letter state)

epsilonNdStateMachineConcatenationWrapper :: AgnosticStateMachine alphabet -> AgnosticStateMachine alphabet -> AgnosticStateMachine alphabet
epsilonNdStateMachineConcatenationWrapper (EraseStates machine1) (EraseStates machine2) = EraseStates (epsilonNdStateMachineConcatenation machine1 machine2)

-- state machine which recognises the Kleene star of the language recognised by the original state machine
epsilonNdStateMachineKleeneStar :: (Ord states) => EpsilonNDStateMachine states alphabet -> EpsilonNDStateMachine (Based states) alphabet
epsilonNdStateMachineKleeneStar (EpsilonNDStateMachine trans initial isAccept) = EpsilonNDStateMachine kleeneTrans kleeneInitial isKleeneAccept where

    isKleeneAccept (Base ()) = False
    isKleeneAccept (Original x) = isAccept x

    kleeneInitial = Base ()

    kleeneTrans Epsilon (Base ()) = Set.singleton (Original initial)
    kleeneTrans (Simply _letter) (Base ()) = Set.empty
    kleeneTrans Epsilon (Original state) = if isAccept state then Set.union (Set.singleton (Original initial)) (fmap Original (trans Epsilon state)) else fmap Original (trans Epsilon state)
    kleeneTrans (Simply letter) (Original state) = fmap Original (trans (Simply letter) state)

epsilonNdStateMachineKleeneStarWrapper :: AgnosticStateMachine alphabet -> AgnosticStateMachine alphabet
epsilonNdStateMachineKleeneStarWrapper (EraseStates machine) = EraseStates (epsilonNdStateMachineKleeneStar machine)


-- the return type of statemachineFromRegex should be parameterised by the input value
-- this is because different regexes require different state types
-- however, Haskell cannot achieve this because it does not have dependent types
-- Instead, we fudge things with existential types - we know that *some* state type with the right constraints exists
-- and that's good enough
data AgnosticStateMachine alphabet = forall states. (Ord states) => EraseStates (EpsilonNDStateMachine states alphabet)

stateMachineFromRegex :: (Eq alphabet) => Regex alphabet ->  AgnosticStateMachine alphabet
stateMachineFromRegex Empty = EraseStates (EpsilonNDStateMachine trans initial isAccept) where 
    initial = ()
    isAccept = const False
    trans _letter  () = Set.singleton ()

stateMachineFromRegex (FromAlphabet Epsilon) = EraseStates (EpsilonNDStateMachine trans initial isAccept) where 
    initial = True
    isAccept = (== True)
    trans _letter True = Set.singleton False
    trans _letter False = Set.singleton False

stateMachineFromRegex (FromAlphabet (Simply targetLetter)) = EraseStates (EpsilonNDStateMachine trans initial isAccept) where 
    initial = False
    isAccept = (== True)
    trans letter False = if letter == Simply targetLetter then Set.singleton True else Set.empty
    trans _letter True = Set.empty
    

stateMachineFromRegex (Union regex1 regex2) = epsilonNdStateMachineUnionWrapper (stateMachineFromRegex regex1) (stateMachineFromRegex regex2)
stateMachineFromRegex (Concatenation regex1 regex2) = epsilonNdStateMachineConcatenationWrapper (stateMachineFromRegex regex1) (stateMachineFromRegex regex2)
stateMachineFromRegex (KleeneStar regex) = epsilonNdStateMachineKleeneStarWrapper (stateMachineFromRegex regex) 


data GoodStates = Start
    | G
    | O1
    | O2
    | D
    | Bin
    deriving (Show, Eq, Ord)


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

main :: IO()
main = print (exhibitAccept testMachine3 "good" [Start, G, O1, O2, D])
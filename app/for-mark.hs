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
oneStepAccept :: (Ord states) => StateMachine states alphabet -> (Maybe alphabet, (Maybe states, Maybe states)) -> Bool
oneStepAccept (StateMachine _t  initial _acceptFunc) (_letter, (Nothing, Just state)) = state == initial
oneStepAccept (StateMachine t _initial _acceptFunc) (Just letter, (Just s1, Just s2)) = t letter s1 == s2
oneStepAccept _ (Nothing, (Just _, Just _)) = False
oneStepAccept (StateMachine _t _initial acceptFunc) (_letter,  (Just state, Nothing)) = acceptFunc state
oneStepAccept (StateMachine _t _initial _acceptFunc)  (_letter, (Nothing, Nothing)) = False--should never happen in our use of this function

--version of zip which preserves longer original length
longZip :: [a] -> [b] -> [(Maybe a, Maybe b)]
longZip [] bs = fmap (\ b -> (Nothing, Just b)) bs
longZip as [] = fmap (\ a -> (Just a,Nothing)) as
longZip (a:as) (b:bs) = (Just a, Just b) : longZip as bs

exhibitAccept:: (Ord states) => StateMachine states alphabet -> [alphabet] -> [states] -> Bool
exhibitAccept machine word states = exhibitAcceptHelper machine (Nothing : fmap Just word) states 

exhibitAcceptHelper :: (Eq states) => StateMachine states alphabet -> [Maybe alphabet] -> [states] -> Bool
exhibitAcceptHelper machine word states = all (oneStepCompute machine) transitionPairs where
    transitionPairs = fmap (Data.Bifunctor.bimap join joinPair) (longZip word (consecutivePairs states)) where
        joinPair Nothing = (Nothing, Nothing)
        joinPair (Just pair) = pair


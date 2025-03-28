import Data.Map (Map)
--import qualified Data.Set as Set
import qualified Data.Set.Monad as Set--implements monad on Set
import Control.Applicative
import Control.Monad

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

contains :: (Eq a) => [a] -> a -> Bool
contains xs c = foldr (\current acc -> acc || (current == c || acc) ) False xs

--state machine parameterised by arbitrary types
--reduces to the case of a finite automation when states and alphabet are both finite sets e.g. enums
data StateMachine states alphabet = StateMachine {
    transitionFunction :: alphabet -> states -> states,--easier to foldr when arguments in this order
    initialState :: states,
    acceptStates :: Set.Set states
}

compute :: (Ord states) => StateMachine states alphabet -> [alphabet] -> states
compute (StateMachine t i a)  = foldr t i 

accept :: (Ord states) => StateMachine states alphabet -> [alphabet] -> Bool
accept (StateMachine t i a) word = Set.member (compute (StateMachine t i a) word) a

stateProduct :: (Ord states1, Ord states2) => StateMachine states1 alphabet -> StateMachine states2 alphabet -> StateMachine (states1, states2) alphabet
stateProduct (StateMachine t1 i1 a1) (StateMachine t2 i2 a2) = StateMachine transition (i1, i2) (cartesianProduct a1 a2) where
    transition w (state1, state2) = (t1 w state1, t2 w state2)


data NDStateMachine states alphabet = NDStateMachine {
    ndtransitionFunction :: alphabet -> states -> Set.Set states,--easier to foldr when arguments in this order
    ndinitialState :: states,
    ndacceptStates :: Set.Set states
}


ndcompute :: (Ord states) => NDStateMachine states alphabet -> [alphabet] -> Set.Set states
ndcompute (NDStateMachine t i as)  = foldr flattenedTransition  (return i)  where
    flattenedTransition bs = join . fmap (t bs)

subsetConstruction :: NDStateMachine states alphabet -> StateMachine (Set.Set states) alphabet
subsetConstruction (NDStateMachine t i as) = StateMachine flattenedTransition (return i) (return as) where
    flattenedTransition bs = join . fmap (t bs)

ndInclusion :: StateMachine states alphabet -> NDStateMachine states alphabet
ndInclusion (StateMachine t i a) = NDStateMachine expandedTransition i a where
    expandedTransition b = return . t b  

main :: IO ()
main =
    print (contains " a bcd  " ' ')
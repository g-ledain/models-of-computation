import Data.Map (Map)
--import qualified Data.Set as Set
import Data.Set.Monad

data Json = Null 
    | JsonBool Bool 
    | JsonString String 
    | JsonFloat Float 
    | JsonList [Json] 
    | JsonDict (Map String Json)  
    deriving (Show)

stripWhitespace :: String -> String
stripWhitespace xs = xs >>= ( \ x -> if x == ' ' then "" else [x])

contains :: (Eq a) => [a] -> a -> Bool
contains xs c = foldr (\current -> \acc -> if acc then True else current == c || acc ) False xs

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

stateProduct :: StateMachine states1 alphabet -> StateMachine states2 alphabet -> StateMachine (states1, states2) alphabet
stateProduct (StateMachine t1 i1 a1) (StateMachine t2 i2 a2) = StateMachine transition (i1, i2) (Set.cartesianProduct a1 a2) where
    transition w (state1, state2) = (t1 w state1, t2 w state2)


data NDStateMachine states alphabet = NDStateMachine {
    ndtransitionFunction :: alphabet -> states -> Set.Set states,--easier to foldr when arguments in this order
    ndinitialState :: states,
    ndacceptStates :: Set.Set states
}


ndcompute :: (Ord states) => NDStateMachine states alphabet -> [alphabet] -> Set.Set states
ndcompute (NDStateMachine t i as)  = foldr flattenedTransition  (return i)  where
    flattenedTransition a = (join . fmap (ndtransitionFunction a))
--need to import SetMonad


main :: IO ()
main =
    print (contains " a bcd  " ' ')
module EsumOsum

import Help

data State : Type where 
  Esum : State 
  Osum : State
  
delta : Int -> State -> State
delta x Osum = if even x then Osum else Esum
delta x Esum = if odd  x then Osum else Esum

data Word : Nat -> State -> (Int -> State -> State) -> Type where 
            Eps  : Word Z Esum EsumOsum.delta 
            Cons : Word n state f -> (x : Int) -> Word (S n) (f x state) f 

data AccRun : Nat -> State -> State -> (Int -> State -> State) -> Type where
            Start : (s : State) -> AccRun Z s s EsumOsum.delta
            Step  : (w : Int) -> AccRun n q_0 q_n f -> AccRun (S n) (f w q_0) q_n f

h : Word n state f ->AccRun n state Esum f
h Eps = Start Esum
h (Cons ws w) = Step w $ h ws




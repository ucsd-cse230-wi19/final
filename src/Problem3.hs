--------------------------------------------------------------------------------
-- | FINAL PROBLEM 3: Loop Invariants
--------------------------------------------------------------------------------

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--diff"        @-}
{-@ LIQUID "--short-names" @-}

{-# LANGUAGE GADTs #-}

module Problem3 where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified State as S
import           Expressions  
import           Imp 
import           BigStep hiding (And)
import           Axiomatic 
import           Problem2 

----------------------------------------------------------------------------------
-- An automatic `verifier` 
----------------------------------------------------------------------------------

{-@ verify :: p:_ -> c:_ -> q:_ -> Valid (vc' p c q) -> () @-}
verify :: Assertion -> ICom -> Assertion -> Valid -> () 
verify _ _ _ _ = () 

----------------------------------------------------------------------------------
-- | PROBLEM 3.a : What loop `inv` lets us `verify` the following triple?
----------------------------------------------------------------------------------

problem3a   :: () -> () 
problem3a _ = verify p c q (\_ -> ())
  where 
    p   = (V "x" `Equal` V "a")                            -- { x == a } 

    c   = IAssign "y" (N 0) `ISeq`                         -- y := 0;
          IWhile inv (Not (V "x" `Equal` N 0))             -- WHILE (x != 0)
            (IAssign "x" ((V "x") `Minus` (N 1))  `ISeq`   --   x := x - 1;
             IAssign "y" ((V "y") `Plus`  (N 1)))          --   y := y + 1

    q   = (V "y" `Equal` V "a")                            -- { y == a }

    inv = impossible "TBD"

-- HINT: It may be faster to try "candidate" invariants using DAFNY 
--         https://rise4fun.com/Dafny/EX35 
--       Try to get DAFNY to accept that program after replacing the line 
--         invariant true;
--       with a better loop invariant i.e. other than 'true' and then plug that in for `inv`

----------------------------------------------------------------------------------
-- | PROBLEM 3.b : What loop `inv` lets us `verify` the following triple?
----------------------------------------------------------------------------------

problem3b   :: () -> () 
problem3b _ = verify p c q (\_ -> ())
  where 
    p   = (V "n" `Equal` (N 10))                                  -- { n == 10 } 

    c   = IAssign "i" (N 0) `ISeq`                                --   i := 0;
          IAssign "r" (N 0) `ISeq`                                --   r := 0;
          IWhile inv (Not (V "i" `Equal` V "n"))                  --   WHILE (i != n)
            ( IAssign "r" (V "r" `Plus` V "i") `ISeq`             --     r := r + i;
              IAssign "i" (V "i" `Plus` N 1)                      --     i := i + 1
            )
    q   = (V "r" `Equal` (N 45))                                  -- { r == 45 }

    inv = impossible "TBD"

-- HINT: It may be faster to try "candidate" invariants using DAFNY 
--         https://rise4fun.com/Dafny/VowP
--       Try to get DAFNY to accept that program after replacing the line 
--         invariant true;
--       with a better loop invariant i.e. other than 'true' and then plug that in for `inv`

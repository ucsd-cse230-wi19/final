---------------------------------------------------------------------------------
-- | PROBLEM 2: Soundness of Verification Conditions. We will prove that 
--              if the `vc p c q` is valid, then the triple {p} c {q} is legit.
---------------------------------------------------------------------------------

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--diff"        @-}
{-@ LIQUID "--short-names" @-}

{-# LANGUAGE GADTs #-}

module Problem2 where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified State as S
import           Expressions  
import           Imp 
import           BigStep hiding (And)
import           Axiomatic 

---------------------------------------------------------------------------------
-- | PROBLEM 2.a: Complete the following lemma relating `vc` and `pre`.
--------------------------------------------------------------------------------

-- HINT: Notice that the proof is "by induction" on the `ICom`, returning for each 
--       case of `ICom`, the corresponding `FH` proof tree. Make sure you understand 
--       the proofs for the `ISkip`, `IAssign` and `IIf` cases before proceeding.

{-@ lem_vc :: c:_ -> q:_ -> Valid (vc c q) -> Prop (FH (pre c q) (strip c) q) @-}
lem_vc :: ICom -> Assertion -> Valid -> FHProof 

lem_vc ISkip          q _ = FHSkip q

lem_vc (IAssign x a)  q _ = FHAssign q x a 

{- let p1 = pre c1 q 
       p2 = pre c2 q 
       p  = bIte b p1 p2 
       
    [lem_valid]    [lem_vc c1 q v]                  [lem_valid]      [lem_vc c2 q v]
    -------------  ----------------                 --------------   ---------------- 
    |- p&b => p1   |- {p1} c1 {q}                   |- p&!b => p2    |- {p2} c2 {q}
    ------------------------------ [FHConPre]       ------------------------------ [FHConPre]
    |- {p&b} c1 {q}                                 |- {p&!b} c2 {q}
    ------------------------------------------------------------------------------ [FHIf]
    |- { p } If b c1 c2 { q }

 -}

lem_vc (IIf b c1 c2)  q v = FHIf p q b (strip c1) (strip c2) pb_c1_q pnotb_c2_q 
  where 
    p                     = bIte b p1 p2 
    p1                    = pre c1 q 
    p2                    = pre c2 q 
    p1_c1_q               = lem_vc c1 q v 
    p2_c2_q               = lem_vc c2 q v 
    pb_c1_q               = FHConPre (bAnd p b)       p1 q (strip c1) v1 p1_c1_q
    pnotb_c2_q            = FHConPre (bAnd p (Not b)) p2 q (strip c2) v2 p2_c2_q
    v1                    = lem_valid_imp  b p1 p2
    v2                    = lem_valid_imp' b p1 p2

{- HINT: 

   let p = pre c1 q 
       q = pre c2 r
    
    [lem_vc c1 q v]  [lem_vc c2 r v]
    ---------------  ----------------
    |- {p} c1 {q}    |- {q} c2 {r}
    ------------------------------------[FHSeq]
    |- {p} c1;c2 {r}

 -}

lem_vc (ISeq c1 c2)   r v = impossible "TBD" 


{- 

    ---------------------- [v]   ------------------- [lem_vc c i v]
    |- (i & b) => pre c i        |- {pre c i} c {i}
    ------------------------------------------------ [FHConPre] 
    |- {i & b} c {i}
    -------------------------- [FHWhile]    ---------------- [v]
    |- {i} while b c {i & ~b}               |- (i & ~b) => q 
    -------------------------------------------------------- [FHConPost]
    |- {i} while b c {q} 

    c_        = strip c 
    ib_c_i    = FHConPre (bAnd i b) (pre c i) i c_ v (lem_vc c i v)
    i_w_inotb = FHWhile i b c_ ib_c_i
    i_w_q     = FHConPost i (bAnd i (Not b)) (While b c_) v 

 -}

lem_vc (IWhile i b c) q v = impossible "TBD" 


----------------------------------------------------------------------------------
-- helper lemmas used for `IIf` case, you can ignore them for `ISeq` and `IWhile`

{-@ lem_valid_imp :: b:_ -> p1:_ -> p2:_ -> (Imply (bAnd (bIte b p1 p2) b) p1) @-}
lem_valid_imp :: BExp -> BExp -> BExp -> Valid 
lem_valid_imp b p1 p2 = \_ -> () 

{-@ lem_valid_imp' :: b:_ -> p1:_ -> p2:_ -> (Imply (bAnd (bIte b p1 p2) (Not b)) p2) @-}
lem_valid_imp' :: BExp -> BExp -> BExp -> Valid 
lem_valid_imp' b p1 p2 = \_ -> () 

---------------------------------------------------------------------------------
-- | PROBLEM 2.b: Use `thm_fh_legit` and `lem_vc` to prove that `vc` is "sound"
--------------------------------------------------------------------------------

{-@ thm_vc :: c:_ -> q:_ -> Valid (vc c q) -> Legit (pre c q) (strip c) q @-}
thm_vc :: ICom -> Assertion -> Valid -> Legit 
thm_vc c q v = impossible "TBD" 


-- | Lets extend `vc` to check triples `{p} c {q}`, by generating a `vc' p c q` defined 

{-@ reflect vc' @-}
vc' :: Assertion -> ICom -> Assertion -> Assertion 
vc' p c q = bAnd (bImp p (pre c q)) (vc c q) 


--------------------------------------------------------------------------------
-- | PROBLEM 2.c: Prove that `vc'` is sound, that is, that 
--                the validity of `vc' p c q` implies `{p} c {q}` is legit
--------------------------------------------------------------------------------

{- HINT: here's a proof tree 

   [v]                      [lem_vc c q v]
   ---------------          ------------------
   |- p => pre c q          |- {pre c q} c {q} 
   ------------------------------------------- [FHConPre]
   |- {p} c {q}

 -}

{-@ lem_vc' :: p:_ -> c:_ -> q:_ -> Valid (vc' p c q) -> Prop (FH p (strip c) q) @-}
lem_vc' :: Assertion -> ICom -> Assertion -> Valid -> FHProof 
lem_vc' p c q v = impossible "TBD" 

{-@ thm_vc' :: p:_ -> c:_ -> q:_ -> Valid (vc' p c q) -> Legit p (strip c) q @-}
thm_vc' :: Assertion -> ICom -> Assertion -> Valid -> Legit 
thm_vc' p c q v = impossible "TBD" 

-- HINT: This is very similar to how you used `lem_vc` to prove `thm_vc` ...

-------------------------------------------------------------------------------
-- silly import bug
-------------------------------------------------------------------------------
imports = (FH undefined undefined undefined)


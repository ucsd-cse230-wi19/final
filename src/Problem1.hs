--------------------------------------------------------------------------------
-- | FINAL PROBLEM 1, 2: Meta-theory for Axiomatic semantics 
--------------------------------------------------------------------------------
	
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--diff"        @-}
{-@ LIQUID "--short-names" @-}

{-# LANGUAGE GADTs #-}

module Problem1 where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified State as S
import           Expressions  
import           Imp 
import           BigStep hiding (And)
import           Axiomatic 

--------------------------------------------------------------------------------
-- | Problem 1: Legit 
--------------------------------------------------------------------------------

{- Recall the definition of `Legit` given in Axiomatic.hs 
  
   type Legit P C Q =  s:{State | bval P s} 
                    -> s':_ -> Prop (BStep C s s') 
                    -> {bval Q s'} 

 -}

--------------------------------------------------------------------------------
-- | The following lemmas prove our rules for `Consequence` are `Legit`
--------------------------------------------------------------------------------
{-@ lem_conseq_pre :: p':_ -> p:_ -> q:_ -> c:_ 
                   -> Imply p' p -> Legit p c q 
                   -> Legit p' c q
  @-}
lem_conseq_pre :: Assertion -> Assertion -> Assertion -> Com -> Valid -> Legit -> Legit 
lem_conseq_pre p' p q c impl pcq = \s s' c_s_s' -> pcq (s ? (impl s)) s' c_s_s'

{-@ lem_conseq_post :: p:_ -> q:_ -> q':_ -> c:_ 
                    -> Legit p c q -> Imply q q' 
                    -> Legit p c q'
  @-}
lem_conseq_post :: Assertion -> Assertion -> Assertion -> Com -> Legit -> Valid -> Legit 
lem_conseq_post p q q' c pcq impl = \s s' c_s_s' -> pcq s s' c_s_s' ? (impl s') 

--------------------------------------------------------------------------------
-- | The following lemma proves that our rule for `Skip` is `Legit` 
--------------------------------------------------------------------------------
{-@ lem_skip :: p:_ -> (Legit p Skip p) @-}
lem_skip :: Assertion -> Legit 
lem_skip p = \s s' (BSkip {}) -> () 

--------------------------------------------------------------------------------
-- | The following lemma proves that our rule for `Assign` is `Legit` 
--------------------------------------------------------------------------------
{-@ lem_asgn :: x:_ -> a:_ -> q:_ -> 
      Legit (bsubst x a q) (Assign x a) q 
  @-}
lem_asgn :: Vname -> AExp -> Assertion -> Legit 
lem_asgn x a q = \s s' (BAssign {}) -> lem_bsubst x a q s

--------------------------------------------------------------------------------
-- | PROBLEM 1.a : Complete the proof that the rule for `Seq` is `Legit`
--------------------------------------------------------------------------------
{-@ lem_seq :: c1:_ -> c2:_ -> p:_ -> q:_ -> r:_ 
            -> Legit p c1 q 
            -> Legit q c2 r 
            -> Legit p (Seq c1 c2) r 
  @-}
lem_seq :: Com -> Com -> Assertion -> Assertion -> Assertion -> Legit -> Legit -> Legit 
lem_seq c1 c2 p q r l1 l2 = \s s' (BSeq _ _ _ smid _ t1 t2) -> 
  impossible "TBD"

-- HINT: Your goal is to prove that `bval r s'` -- i.e. s' "satisfies" the postcondition `r` 
--       What are the types of `l1` and `l2`, and `t1` and `t2`? How can you use them 
--       to prove your goal?


--------------------------------------------------------------------------------
-- | PROBLEM 1.b: Complete the proof that the rule for `If` is `Legit` 
--------------------------------------------------------------------------------
{-@ lem_if :: b:_ -> c1:_ -> c2:_ -> p:_ -> q:_ 
           -> Legit (bAnd p b)       c1 q 
           -> Legit (bAnd p (Not b)) c2 q 
           -> Legit p (If b c1 c2)  q
  @-}
lem_if :: BExp -> Com -> Com -> Assertion -> Assertion -> Legit -> Legit -> Legit
lem_if b c1 c2 p q l1 l2 = \s s' bs -> case bs of 
  BIfF _ _ _ _ _ c2_s_s' -> 
    impossible "TBD"
  BIfT _ _ _ _ _ c1_s_s' -> 
    impossible "TBD"

--------------------------------------------------------------------------------
-- | PROBLEM 1.c: Complete the proof that the rule for `While` is `Legit`
--------------------------------------------------------------------------------
{-@ lem_while :: b:_ -> c:_ -> p:_ 
              -> Legit (bAnd p b) c p 
              -> Legit p (While b c) (bAnd p (Not b)) 
  @-}
lem_while :: BExp -> Com -> Assertion -> Legit -> Legit 
lem_while b c p lbody = \s s' ws -> case ws of 
  BWhileF {} -> 
    ()
  BWhileT _ _ _ smid _ c_s_smid w_smid_s' -> 
    impossible "TBD"

-- HINT: What are `smid`, `c_s_smid` and `w_smid_s'` ? 
--       What assertion does `smid` satisfy? 
--       How can you use `smid` and `lbody` to deduce that the output state `s'` 
--       satisfies the postcondition?

--------------------------------------------------------------------------------
-- | PROBLEM 1.d: Use the above `lem_skip`, `lem_asgn`, `lem_seq` etc to prove 
--                the Soundness of Floyd-Hoare Logic 
--                The definition of `FH` is given in Axiomatic.hs
--------------------------------------------------------------------------------

{-@ thm_fh_legit :: p:_ -> c:_ -> q:_ -> Prop (FH p c q) -> Legit p c q @-}
thm_fh_legit :: Assertion -> Com -> Assertion -> FHProof -> Legit 
thm_fh_legit p _ _ (FHSkip {})      
  = impossible "TBD" 

thm_fh_legit _ _ q (FHAssign _ x a) 
  = impossible "TBD" 

thm_fh_legit _ _ _ (FHSeq p c1 q c2 r p_c1_q q_c2_r) 
  = impossible "TBD" 

thm_fh_legit _ _ _ (FHIf p q b c1 c2 fh_c1 fh_c2)
  = impossible "TBD" 

thm_fh_legit _ _ _ (FHWhile p b c p_c_p) 
  = impossible "TBD" 

thm_fh_legit _ _ _ (FHConPre p' p q c p'_imp_p p_c_q)
  = impossible "TBD" 

thm_fh_legit _ _ _ (FHConPost p q q' c p_c_q q_imp_q')
  = impossible "TBD" 



















-------------------------------------------------------------------------------
-- silly import bug
-------------------------------------------------------------------------------
imports = (FH undefined undefined undefined)


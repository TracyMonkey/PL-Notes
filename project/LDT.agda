module LDT where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; _∷_; []; _++_)
open import Data.Vec using (Vec; reverse) renaming (_∷_ to _::_) renaming ([] to `[])
open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (refl; sym; cong; _≡_; subst; trans)
open import Data.Nat.Properties
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Agda.Builtin.Sigma
open import Data.Bool


open import util

mutual
  data DT : Set where 
    Leaf : Nat -> DT
    Prod : DT -> DT -> DT
    Sigma : (t : DT) -> (interp t -> DT) -> DT
    Indicator : DT -> DT  

  interp : DT -> Set
  interp (Leaf n)     = Vec Bit n 
  interp (Prod left right) = interp left × interp right
  interp (Sigma t f) = Σ (interp t) (λ value → interp (f value))
  interp (Indicator t) = Maybe (interp t)

-- 1. Basic parsing process without verify IsLowLevel

-- parse : (f : DT) -> List Bit -> Maybe (interp f × List Bit)
-- -- parse (Leaf n) bs = splitList n bs `[]
-- parse (Leaf n) bs = mapMaybe adjustResult (splitList n bs `[])
--   where
--     adjustResult : (Vec Bit (n + 0) × List Bit) -> (Vec Bit n × List Bit)
--     adjustResult (v , rest) with (+-identityʳ n)
--     ... | p = subst (λ m → Vec Bit m × List Bit) p (v , rest)
-- parse (Prod left right) bs = maybeBind (parse left bs) λ {(v1 , rest) -> mapMaybe (adjustResult v1) (parse right rest)}
--   where
--     adjustResult : interp left -> (interp right × List Bit) -> (interp (Prod left right) × List Bit)
--     adjustResult v1 (v2 , rest) = ((v1 , v2), rest)
-- parse (Sigma t f) bs = maybeBind (parse t bs) λ {(rt , rest) -> maybeBind (parse (f rt) rest) λ {(rf , rest2) -> just ((rt , rf) , rest2)}}
-- parse (Indicator t) bs with bs
-- ... | [] = nothing
-- ... | (b ∷ rest) with decEqBit b I
-- ...   | yes = maybeBind (parse t rest) λ {(rt , rest') -> just (just rt , rest')}
-- ...   | no = just (nothing , rest)

-- 2. Only these verified types can be used at low level

data IsLowLevel : DT -> Set where
  LeafILL  : {n : Nat} -> IsLowLevel (Leaf n)
  ProdILL  : {left right : DT} -> IsLowLevel left -> IsLowLevel right -> IsLowLevel (Prod left right)
  SigmaILL : {t : DT} {f : interp t -> DT} -> IsLowLevel t -> ((result : interp t) -> IsLowLevel (f result)) -> IsLowLevel (Sigma t f)
  IndicatorILL : {t : DT} -> IsLowLevel t -> IsLowLevel (Indicator t)

-- only parse data IsLowLevel 
parse : {f : DT} -> IsLowLevel f -> List Bit -> Maybe (interp f × List Bit)
parse (LeafILL {n}) bs = mapMaybe adjustResult (splitList n bs `[])
  where
    adjustResult : (Vec Bit (n + 0) × List Bit) -> (Vec Bit n × List Bit)
    adjustResult (v , rest) with (+-identityʳ n)
    ... | p = subst (λ m → Vec Bit m × List Bit) p (v , rest)
parse {f = Prod left right} (ProdILL leftILL rightILL) bs = maybeBind (parse leftILL bs) λ {(rl , rest) -> mapMaybe (adjustResult rl) (parse rightILL rest)}
  where
    adjustResult : interp left -> (interp right × List Bit) -> (interp (Prod left right) × List Bit)
    adjustResult v1 (v2 , rest) = ((v1 , v2), rest)
parse (SigmaILL tILL fILL) bs = maybeBind (parse tILL bs) λ {(rt , rest) -> maybeBind (parse (fILL rt) rest) λ {(rf , rest2) -> just ((rt , rf) , rest2)}}
parse (IndicatorILL tILL) bs with bs
... | [] = nothing
... | (b ∷ rest) with decEqBit b I
...   | yes = maybeBind (parse tILL rest) λ {(rt , rest') -> just (just rt , rest')}
...   | no = just (nothing , rest)


-- Pretty print
pp : (f : DT) -> interp f -> List Bit
pp (Leaf n) vec = toList vec
pp (Prod left right) (vecl , vecr) = pp left vecl ++ pp right vecr   
pp (Sigma t f) (vect , vecf) = pp t vect ++ pp (f vect) vecf
pp (Indicator f) nothing  = O ∷ [] 
pp (Indicator f) (just vec) = I ∷ pp f vec


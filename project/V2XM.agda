module V2XM where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; _∷_; [])
open import Data.Vec using (Vec; reverse) renaming (_∷_ to _::_) renaming ([] to `[])
open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (refl; sym; cong; _≡_; subst; trans)
open import Data.Nat.Properties
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import util

data FT : Set where
  Word : Nat -> FT
  Prod : FT -> FT -> FT

interp : FT -> Set
interp (Word n)     = Vec Bit n 
interp (Prod t1 t2) = interp t1 × interp t2


parse : (f : FT) -> List Bit -> Maybe (interp f × List Bit)
-- parse (Word n) xs = splitList n xs `[]
parse (Word n) xs = mapMaybe adjustResult (splitList n xs `[])
  where
    adjustResult : (Vec Bit (n + 0) × List Bit) -> (Vec Bit n × List Bit)
    adjustResult (v , rest) with (+-identityʳ n)
    ... | p = subst (λ m → Vec Bit m × List Bit) p (v , rest)
parse (Prod t1 t2) xs = maybeBind (parse t1 xs) λ {(v1 , rest) -> mapMaybe (adjustResult v1) (parse t2 rest)}
  where
    adjustResult : interp t1 -> (interp t2 × List Bit) -> (interp (Prod t1 t2) × List Bit)
    adjustResult v1 (v2 , rest) = ((v1 , v2), rest)

-- pp : (f : FT) -> interp f -> List Bit
-- pp (Word n)     bs       = toList bs
-- pp (Prod t1 t2) (x1, x2) = pp t1 x1 ++ pp t2 x2  
module util where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; _∷_; [])
open import Data.Vec using (Vec; reverse) renaming (_∷_ to _::_) renaming ([] to `[])
open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (refl; sym; cong; _≡_; subst; trans)
open import Data.Nat.Properties
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning

Nat = ℕ

data Bit : Set where
    O : Bit
    I : Bit

suc-+-comm : ∀ (k m : ℕ) -> suc (k + m) ≡ k + suc m
suc-+-comm zero m = refl 
suc-+-comm (suc k) m = begin
    suc (suc k + m)
    ≡⟨ cong suc (suc-+-comm k m) ⟩
    suc (k + suc m)
    ≡⟨ refl ⟩
    suc k + suc m ∎

splitList : ∀ {m} → (k : Nat) -> List Bit -> Vec Bit m -> Maybe (Vec Bit ( k + m ) × List Bit)
splitList {m} zero rem acc = just (reverse acc , rem)
splitList {m} (suc k) [] _ = nothing
splitList {m} (suc k) (r ∷ rem) acc with splitList k rem (r :: acc)
... | nothing = nothing
... | just result with sym (suc-+-comm k m)
...   | p = just (subst (λ l → Vec Bit l) p (proj₁ result), proj₂ result)

test : Maybe (Vec Bit (2 + 3) × List Bit)
test = splitList 2 (I ∷ O ∷ I ∷ []) (I :: I :: O :: `[])


mapMaybe : {A B : Set} -> (A -> B) -> Maybe A -> Maybe B
mapMaybe f (just x) = just (f x)
mapMaybe _ nothing = nothing

maybeBind : ∀ {A B : Set} -> Maybe A -> (A -> Maybe B) -> Maybe B
maybeBind nothing _ = nothing
maybeBind (just x) f = f x
 
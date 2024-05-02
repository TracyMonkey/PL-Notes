module util where

open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.List using (List; _∷_; [])
open import Data.Vec using (Vec; reverse) renaming (_∷_ to _::_) renaming ([] to `[])
open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (refl; sym; cong; _≡_; subst; trans; _≢_)
open import Data.Nat.Properties
open import Data.Product -- using (_×_; _,_; proj₁; proj₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Bool using (Bool; if_then_else_)
open import Relation.Nullary
-- open import Agda.Builtin.Sigma using (fst; snd)

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

-- decide equality of Bit
decEqBit : (x y : Bit) -> Dec (x ≡ y)
decEqBit O O = yes refl
decEqBit I I = yes refl
decEqBit O I = no λ ()
decEqBit I O = no λ ()

-- Calculate nat to length of bits. Like 4 (I ∷ I ∷ O) use 3 bits
open import Data.Nat.DivMod 
open import Relation.Nullary

record NonZero : Set where
  constructor nz
  field
    value : Nat
    isNonZero : value ≢ 0

_-_ : ℕ → ℕ → ℕ
zero - _ = zero
(suc m) - zero = suc m
(suc m) - suc n = m - n

-- -- test
-- 3n0 : 3 ≢ 0
-- nonZeroThree : NonZero
-- nonZeroThree = nz 3 3n0

fst : {A B : Set} → A × B → A
fst (x , _) = x

snd : {A B : Set} → A × B → B
snd (_ , y) = y

{-# TERMINATING #-}
divMod : ℕ → NonZero → ℕ × ℕ
divMod n (nz d _) = divModHelper n d 0
  where
    divModHelper : ℕ → ℕ → ℕ → ℕ × ℕ
    divModHelper n d q with n <? d
    ... | yes _ = (q , n)
    ... | no _  = divModHelper (n - d) d (suc q)

exampleUse : ℕ × ℕ
exampleUse = divMod 10 (nz 3 λ ())

div : ℕ → NonZero → ℕ
div n d = fst (divMod n d)

nonZeroTwo : NonZero
nonZeroTwo = nz 2 λ()

{-# TERMINATING #-}
Nat2Bits : Nat -> Nat 
Nat2Bits n = go n 0
  where
    go : Nat -> Nat -> Nat
    go 0 acc = acc + 1
    go n acc = go (div n nonZeroTwo) (acc + 1)

-- Convert Vec Bit to List Bit
toList : {n : ℕ} -> Vec Bit n -> List Bit
toList {zero} `[] = []
toList {suc n} (x :: xs) = x ∷ toList xs



  
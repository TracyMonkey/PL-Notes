module Tests where

open import util
open import LDT 
open import V2XM

open import Data.List
open import Data.Maybe
open import Data.Product using (_×_; _,_)
open import Data.Vec

-- Tests
testMsgCount : DT
testMsgCount = Leaf 7

testPair : DT
testPair = Prod (Leaf 2) (Leaf 3) 

testPosition3D : DT
testPosition3D = Sigma (Leaf 1) (λ _ → Leaf 4) 

IndicatorField : DT
IndicatorField = Indicator (Leaf 8) 

MsgCountILL : IsLowLevel testMsgCount
MsgCountILL = LeafILL

testPairILL : IsLowLevel testPair
testPairILL = ProdILL LeafILL LeafILL

Position3DILL : IsLowLevel testPosition3D
Position3DILL = SigmaILL LeafILL (λ _ → LeafILL)

IndicatorFieldLowLevel : IsLowLevel IndicatorField
IndicatorFieldLowLevel = IndicatorILL LeafILL


-- Test for Sigma parse
testBitList : List Bit
testBitList = I ∷ I ∷ O ∷ O ∷ I ∷ I ∷ [] -- length 3: I ∷ I ∷ O, data payload: O ∷ I ∷ I

testFunc : Vec Bit 3 -> DT
testFunc _ = Leaf 3 

testFuncILL : Vec Bit 3 -> IsLowLevel (Leaf 3)
testFuncILL _ = LeafILL

testSigmaParse : Maybe (interp (Sigma (Leaf 3) testFunc) × List Bit)
testSigmaParse = parse (SigmaILL (LeafILL {3}) testFuncILL) testBitList

-- Tests for pp
interpMsgCount : interp testMsgCount
interpMsgCount = I ∷ O ∷ I ∷ O ∷ I ∷ I ∷ I ∷ []
testPPMsgCount : List Bit
testPPMsgCount = pp testMsgCount interpMsgCount

interptestPair : interp testPair
interptestPair = (I ∷ O ∷ [] , I ∷ O ∷ I ∷ [])
testPPtestPair : List Bit
testPPtestPair = pp testPair interptestPair

interpSigma : interp testPosition3D
interpSigma = (I ∷ [] , O ∷ O ∷ O ∷ I ∷ [])
testPPPosition3D : List Bit
testPPPosition3D = pp testPosition3D interpSigma

interpIndicator : interp IndicatorField
interpIndicator = just (I ∷ O ∷ O ∷ O ∷ I ∷ O ∷ O ∷ I ∷ [])
testPPIndicatorField : List Bit
testPPIndicatorField = pp IndicatorField interpIndicator

-- Test parser for BasicSafetyMessage
BSMBits : List Bit
BSMBits = I ∷ O ∷ I ∷ O ∷ O ∷ I ∷ I ∷ O ∷ I ∷ O ∷ O ∷ I ∷ []

record ParseResult (A : Set) : Set where
  constructor mkParseResult
  field
    result : A
    remainingBits : List Bit


testParseComplete : Maybe (ParseResult (interp BasicSafetyMessage))
testParseComplete = parse BasicSafetyMessage BSMBits

testParseIncomplete : Maybe (ParseResult (interp BasicSafetyMessage))
testParseIncomplete = parse BasicSafetyMessage BSMBits
-- Contain one type of message called BSM (BasicSafetyMessage)
module V2XM where 

open import LDT
open import util
open import Data.Nat using (_*_)

open import Data.Vec

-- Types in specification
ENUMERATED : Nat -> DT
ENUMERATED n = Leaf (Nat2Bits n)

BIT_STRING : Nat -> DT
BIT_STRING n = Leaf (Nat2Bits n)

-- TODO: support negative number
INTEGER : Nat -> Nat -> DT
INTEGER min max = ENUMERATED (max - min)

OCTET_STRING : Nat -> DT
OCTET_STRING n = Leaf (8 * n)

-- High level types
MsgCount : DT
MsgCount = Leaf 7

DSecond : DT
DSecond = Leaf 16

Latitude : DT
Latitude = Leaf 31

Longitude : DT
Longitude = Leaf 32

Elevation : DT
Elevation = Leaf 14

TransmissionState : DT
TransmissionState = ENUMERATED 8

Speed : DT
Speed = Leaf 13

Heading : DT 
Heading = Leaf 15

Acceleration : DT 
Acceleration = Leaf 12

long = Acceleration 
lat = Acceleration

VerticalAcceleration : DT
VerticalAcceleration = Leaf 8

YawRate : DT
YawRate = Leaf 16

AccelerationSet4Way : DT
AccelerationSet4Way = Prod long
                     (Prod lat
                     (Prod VerticalAcceleration
                     YawRate))

-- TODO: this field contains 7 optional
BrakeSystemStatus : DT
BrakeSystemStatus = Leaf 7 

VehicleWidth : DT 
VehicleWidth = Leaf 10

VehicleLength : DT 
VehicleLength = Leaf 12

VehicleSize : DT 
VehicleSize = Prod VehicleWidth VehicleLength
            --  VehicleHeight) -- TODO

BasicVehicleClass : DT
BasicVehicleClass = Leaf 8

VehicleClassification : DT
VehicleClassification = BasicVehicleClass 
                        -- FuelType OPTIONAL -- TODO

SemiMajorAxisAccuracy : DT 
SemiMajorAxisAccuracy = Leaf 7

semiMajor = SemiMajorAxisAccuracy
semiMinor = SemiMajorAxisAccuracy

SemiMajorAxisOrientation : DT
SemiMajorAxisOrientation = Leaf 16

PositionConfidence : DT
PositionConfidence = Leaf 4

ElevationConfidence : DT
ElevationConfidence = Leaf 4

SpeedConfidence : DT
SpeedConfidence = ENUMERATED 8

HeadingConfidence : DT
HeadingConfidence = ENUMERATED 8

SteeringWheelAngleConfidence : DT 
SteeringWheelAngleConfidence = ENUMERATED 4

-- TODO: BIT STRING extension using Sigma, for now, just use fixed size 13
VehicleEventFlags : DT
VehicleEventFlags = ENUMERATED 13

DYear : DT
DYear = INTEGER 0 4095

DMonth : DT
DMonth = INTEGER 0 12

DDay : DT
DDay = INTEGER 0 31

DHour : DT
DHour = INTEGER 0 31

DMinute : DT
DMinute = INTEGER 0 60

DTimeOffset : DT
DTimeOffset = INTEGER 0 1680

GNSSstatus : DT
GNSSstatus = BIT_STRING 8

RadiusOfCurvature : DT
RadiusOfCurvature = INTEGER 0 65535 -- INTEGER (-32767..32767)

Confidence : DT
Confidence = INTEGER 0 200

PathPrediction : DT
PathPrediction = Prod RadiusOfCurvature
                Confidence
                -- extension

ExteriorLights : DT
ExteriorLights = BIT_STRING 9 -- extension

SteeringWheelAngle : DT
SteeringWheelAngle = INTEGER 0 254 -- actually INTEGER (-126..127)

ResponseType : DT
ResponseType = ENUMERATED 7 -- extension

SirenInUse : DT
SirenInUse = ENUMERATED 4 

LightbarInUse : DT
LightbarInUse = ENUMERATED 8


-- Optional fields
DDateTime : DT
DDateTime = Prod (Indicator DYear)
           (Prod (Indicator DMonth)
           (Prod (Indicator DDay)
           (Prod (Indicator DHour)
           (Prod (Indicator DMinute)
           (Prod (Indicator DSecond)
           (Indicator DTimeOffset))))))

Position3D : DT
Position3D = Prod Latitude
            (Prod Longitude
            (Indicator Elevation))

PositionConfidenceSet : DT
PositionConfidenceSet = Prod PositionConfidence
                       (Indicator ElevationConfidence)

TimeConfidence : DT
TimeConfidence = Indicator (ENUMERATED 40)

MotionConfidenceSet : DT
MotionConfidenceSet = Prod (Indicator SpeedConfidence)
                      (Prod (Indicator HeadingConfidence)
                      (Indicator SteeringWheelAngleConfidence))
                      
FullPositionVector : DT
FullPositionVector = Prod (Indicator DDateTime)
                    (Prod Position3D
                    (Prod (Indicator Heading)
                    (Prod (Indicator TransmissionState)
                    (Prod (Indicator Speed)
                    (Prod (Indicator PositionConfidenceSet)
                    (Prod (Indicator TimeConfidence)
                    (Indicator MotionConfidenceSet)))))))

PathHistory : DT
PathHistory = Prod (Indicator FullPositionVector)
              (Indicator GNSSstatus)
            --  PathHistoryPointList) -- SEQUENCE OF, length is not fixed


PositionalAccuracy : DT 
PositionalAccuracy = Prod semiMajor
                    (Prod semiMinor
                    SemiMajorAxisOrientation)

VehicleEmergencyExtensions : DT
VehicleEmergencyExtensions = Prod (Indicator ResponseType)
                            (Prod (Indicator SirenInUse)
                            (Indicator LightbarInUse))

VehicleSafetyExtensions : DT
VehicleSafetyExtensions = Prod (Indicator VehicleEventFlags)
                      (Prod (Indicator PathHistory)
                      (Prod (Indicator PathPrediction)
                      (Indicator ExteriorLights)))

BasicSafetyMessage : DT
BasicSafetyMessage = Prod MsgCount
         (Prod (OCTET_STRING 8)
         (Prod DSecond 
         (Prod TimeConfidence -- TODO: optional for a DT (This version only implement optional next to next field)
         (Prod Position3D 
         (Prod PositionalAccuracy 
         (Prod PositionConfidenceSet
         (Prod TransmissionState
         (Prod Speed
         (Prod Heading
         (Prod SteeringWheelAngle
         (Prod MotionConfidenceSet
         (Prod AccelerationSet4Way
         (Prod BrakeSystemStatus
         (Prod VehicleSize 
         (Prod VehicleClassification
         (Prod VehicleSafetyExtensions
         VehicleEmergencyExtensions
        -- TODO extension mark ... using Sigma
         ))))))))))))))))

-- Test BasicSafetyMessage


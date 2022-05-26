{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutarch.SafeMoney (
    PDiscrete (..),
) where

import Data.Kind (Type)
import Generics.SOP (I (I))
import Generics.SOP.TH (deriveGeneric)
import Plutarch (
    DerivePNewtype (DerivePNewtype),
    PlutusType,
    S,
    Term,
 )
import Plutarch.Bool (PEq, POrd)
import Plutarch.Builtin (PIsData)
import Plutarch.Extra.Tagged (PTagged)
import Plutarch.Integer (PInteger)
import Plutarch.Show (PShow)

-- | @since 1.0.0
newtype PDiscrete (tag :: S -> Type) (s :: S)
    = PDiscrete (Term s (PTagged tag PInteger))

deriveGeneric ''PDiscrete

-- | @since 1.0.0
deriving via
    (DerivePNewtype (PDiscrete tag) (PTagged tag PInteger))
    instance
        (PlutusType (PDiscrete tag))

-- | @since 1.0.0
deriving via
    (DerivePNewtype (PDiscrete tag) (PTagged tag PInteger))
    instance
        PIsData (PDiscrete tag)

-- | @since 1.0.0
deriving via
    (DerivePNewtype (PDiscrete tag) (PTagged tag PInteger))
    instance
        PEq (PDiscrete tag)

-- | @since 1.0.0
deriving via
    (DerivePNewtype (PDiscrete tag) (PTagged tag PInteger))
    instance
        POrd (PDiscrete tag)

-- | @since 1.0.0
deriving anyclass instance PShow (PDiscrete tag)

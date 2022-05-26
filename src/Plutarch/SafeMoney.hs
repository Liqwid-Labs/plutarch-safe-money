{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutarch.SafeMoney (
    PDiscrete (..),
) where

import Data.Bifunctor (first)
import Generics.SOP (I (I))
import Generics.SOP.TH (deriveGeneric)
import Plutarch (
    DerivePNewtype (DerivePNewtype),
    PlutusType,
    S,
    Term,
 )
import Plutarch.Bool (PEq, POrd)
import Plutarch.Builtin (PAsData, PData, PIsData)
import Plutarch.Extra.Tagged (PTagged)
import Plutarch.Integer (PInteger)
import Plutarch.Show (PShow)
import Plutarch.TryFrom (PTryFrom (PTryFromExcess, ptryFrom'))
import Plutarch.Unsafe (punsafeCoerce)

-- | @since 1.0.0
newtype PDiscrete (tag :: k) (s :: S)
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

-- | @since 1.0.0
deriving via
    (DerivePNewtype (PDiscrete tag) (PTagged tag PInteger))
    instance
        (PTryFrom a PInteger) => PTryFrom a (PDiscrete tag)

-- | @since 1.0.0
instance--     (PTryFrom PData (PAsData PInteger)) =>
    PTryFrom PData (PAsData (PDiscrete tag)) where
    type
        PTryFromExcess PData (PAsData (PDiscrete tag)) =
            PTryFromExcess PData (PAsData PInteger)
    ptryFrom' d k = ptryFrom' @_ @(PAsData PInteger) d $ k . first punsafeCoerce

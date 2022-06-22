{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ViewPatterns #-}


{-# OPTIONS_GHC -Wno-all #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Plutarch.SafeMoney (
    PDiscrete (..),
    pvalueDiscrete,
    pvalueDiscrete',
    pdiscreteValue,
    pdiscreteValue',
) where

import Data.Bifunctor (first)
import Data.Kind (Type)
import Data.Tagged (Tagged (Tagged))
import Generics.SOP (I (I))
import Generics.SOP.TH (deriveGeneric)
import Plutarch (
    DerivePNewtype (DerivePNewtype),
    PlutusType,
    S,
    Term,
    pto,
    pcon,
    phoistAcyclic,
    plam,
    unTermCont,
    (#),
    (#$),
    (:-->),
 )
import Plutarch.Api.V1 (PValue)
import "plutarch" Plutarch.Api.V1 (
    AmountGuarantees,
    KeyGuarantees,
 )
import Plutarch.Api.V1.AssetClass (
    PAssetClass,
    passetClass,
    passetClassValueOf,
 )
import "liqwid-plutarch-extra" Plutarch.Api.V1.Value (
    passetClassValue,
    psingletonValue,
 )
import Plutarch.Bool (PEq, POrd)
import Plutarch.Builtin (PAsData, PData, PIsData)
import Plutarch.Extra.Applicative (ppure)
import Plutarch.Extra.Comonad (pextract)
import Plutarch.Extra.Tagged (PTagged(..))
import Plutarch.Extra.TermCont (pletC, pmatchC)
import Plutarch.Integer 
import Plutarch.Lift (pconstant)
import Plutarch.Numeric.Additive (
    AdditiveMonoid (zero),
    AdditiveSemigroup ((+)),
 )
import Plutarch.Show (PShow)
import Plutarch.TryFrom (PTryFrom (PTryFromExcess, ptryFrom'))
import Plutarch.Unsafe (punsafeCoerce)
import PlutusLedgerApi.V1.Value (AssetClass (AssetClass))
import Prelude hiding ((+))
import GHC.TypeLits
import Data.Proxy

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
instance PTryFrom PData (PAsData (PDiscrete tag)) where
    type
        PTryFromExcess PData (PAsData (PDiscrete tag)) =
            PTryFromExcess PData (PAsData PInteger)
    ptryFrom' d k =
        ptryFrom' @_ @(PAsData PInteger) d $ k . first punsafeCoerce

-- | @since 1.0.0
instance AdditiveSemigroup (Term s (PDiscrete tag)) where
    t1 + t2 = unTermCont $ do
        PDiscrete t1' <- pmatchC t1
        PDiscrete t2' <- pmatchC t2
        t1'' <- pletC (pextract # t1')
        t2'' <- pletC (pextract # t2')
        pure . pcon . PDiscrete $ ppure # (t1'' + t2'')

-- | @since 1.0.0
instance AdditiveMonoid (Term s (PDiscrete tag)) where
    zero = pcon . PDiscrete $ ppure # 0

{- | Downcast a 'PValue' to a 'PDiscrete' unit, providing a witness of the 'PAssetClass'.
     @since 0.3
-}
pvalueDiscrete ::
    forall k.
    forall (tag :: k) (keys :: KeyGuarantees) (amounts :: AmountGuarantees) (s :: S).
    Term s (PAssetClass :--> PValue keys amounts :--> PDiscrete tag)
pvalueDiscrete = phoistAcyclic $
    plam $ \ac f -> pcon . PDiscrete $ ppure # (passetClassValueOf # f # ac)

{- | Downcast a 'PValue' to a 'PDiscrete' unit, providing a witness of the 'AssetClass', which gets inlined. If you use this 'AssetClass' twice, prefer 'pvalueDiscrete'.
     @since 0.3
-}
pvalueDiscrete' ::
    forall k.
    forall (tag :: k) (keys :: KeyGuarantees) (amounts :: AmountGuarantees) (s :: S).
    Tagged tag AssetClass ->
    Term s (PValue keys amounts :--> PDiscrete tag)
pvalueDiscrete' (Tagged (AssetClass (cs, tn))) = phoistAcyclic $
    plam $ \f ->
        pcon . PDiscrete $
            ppure # (passetClassValueOf # f #$ passetClass # pconstant cs # pconstant tn)

{- | Get a 'PValue' from a 'PDiscrete', providing a witness of the 'AssetClass'.
     __NOTE__: `pdiscreteValue` after `pvalueDiscrete` is not a round-trip.
     It filters for a particular tag.
     @since 0.3
-}
pdiscreteValue ::
    forall k.
    forall (tag :: k) (keys :: KeyGuarantees) (amounts :: AmountGuarantees) (s :: S).
    Term s (PAssetClass :--> PDiscrete tag :--> PValue keys amounts)
pdiscreteValue = phoistAcyclic $
    plam $ \ac p -> unTermCont $ do
        PDiscrete t <- pmatchC p
        v <- pletC (pextract # t)
        pure $ passetClassValue # ac # v

{- | Get a 'PValue' from a 'PDiscrete', providing a witness of the 'AssetClass'.
     __NOTE__: `pdiscreteValue` after `pvalueDiscrete` is not a round-trip.
     It filters for a particular tag.
     If you use this 'AssetClass' twice, prefer 'pvalueDiscrete'.
     @since 0.3
-}
pdiscreteValue' ::
    forall (tag :: Type) (keys :: KeyGuarantees) (amounts :: AmountGuarantees) (s :: S).
    Tagged tag AssetClass ->
    Term s (PDiscrete tag :--> PValue keys amounts)
pdiscreteValue' (Tagged (AssetClass (cs, tn))) =
    phoistAcyclic $
        plam $ \p -> unTermCont $ do
            PDiscrete t <- pmatchC p
            pure $ psingletonValue # pconstant cs # pconstant tn # (pextract # t)

type family Fst (ab :: (ka, kb)) :: ka where Fst '(a,b) = a
type family Snd (ab :: (ka, kb)) :: ka where Snd '(a,b) = b            

data GT
data Ada
data Lovelace

type family ConversionScale (from :: k) (to :: k) :: (Nat, Nat)

type instance ConversionScale GT Ada = '(1, 1)
type instance ConversionScale Ada Lovelace = '(1, 1000000)
type instance ConversionScale Lovelace Ada = '(1000000, 1)

type GoodScale (scale :: (Nat, Nat)) =
  ( CmpNat 0 (Fst scale) ~ 'LT
  , CmpNat 0 (Snd scale) ~ 'LT
  , KnownNat (Fst scale)
  , KnownNat (Snd scale)
  )

scale ::
    forall (scale :: (Nat, Nat)).
    GoodScale scale =>
    (Integer, Integer)
scale = (natVal (Proxy @(Fst scale)), natVal (Proxy @(Snd scale)))
                
pconvert ::
    forall (to :: *) (from :: *) (sc :: (Nat, Nat)) (s :: S).
    ( ConversionScale from to ~ sc
    , GoodScale sc
    ) =>
    Term s (PDiscrete from :--> PDiscrete to)
pconvert = phoistAcyclic $ plam $
           \f' -> unTermCont $ do
             PDiscrete f <- pmatchC f'
             pure . pcon . PDiscrete $
               ppure # (pdiv # ((pextract # f) * (pconstant n)) # pconstant d)
  where
    (n, d) = scale @sc

-- class (GoodScale (ConversionScale from to)) => Convertable (from :: *) (to :: *) where
--   pconvert' :: Term s (PDiscrete from :--> PDiscrete to)

-- class Convertable (from :: *) (to :: *) where
--   convert :: Term s (PDiscrete from :--> PDiscrete to)

-- $> :set -XTypeApplications

-- $> import Data.Proxy

-- $> a = pcon $ PDiscrete $ pcon $ PTagged 5 :: Term s (PDiscrete Ada)

-- $> :t pconvert @GT # a

-- $> :t pconvert @Lovelace # a


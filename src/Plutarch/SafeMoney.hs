{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Plutarch.SafeMoney (
    PDiscrete (..),
    pvalueDiscrete,
    pvalueDiscrete',
    pdiscreteValue,
    pdiscreteValue',
    PExchangeRate (..),
    pexchange',
    pexchange,
    pexchangeRatio',
    pexchangeRatio,
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
    pcon,
    phoistAcyclic,
    plam,
    unTermCont,
    (#),
    (#$),
    (:-->),
 )
import Plutarch.Api.V1 (AmountGuarantees, KeyGuarantees, PValue)
import Plutarch.Api.V1.AssetClass (
    PAssetClass,
    passetClass,
    passetClassValueOf,
 )
import "liqwid-plutarch-extra" Plutarch.Api.V1.Value (
    passetClassValue,
    psingletonValue,
 )
import Plutarch.Bool (PEq, POrd, pif, (#==))
import Plutarch.Builtin (PAsData, PData, PIsData)
import Plutarch.Extra.Applicative (ppure)
import Plutarch.Extra.Comonad (pextract)
import Plutarch.Extra.FixedDecimal (
    DivideSemigroup (divide),
    PFixedDecimal,
    fromPInteger,
    toPInteger,
 )
import Plutarch.Extra.Tagged (PTagged)
import Plutarch.Extra.TermCont (pletC, pmatchC)
import Plutarch.Integer (PInteger)
import Plutarch.Lift (pconstant)
import Plutarch.Maybe (PMaybe (..))
import Plutarch.Numeric.Additive (
    AdditiveMonoid (zero),
    AdditiveSemigroup ((+)),
 )
import Plutarch.Show (PShow)
import Plutarch.TryFrom (PTryFrom (PTryFromExcess, ptryFrom'))
import Plutarch.Unsafe (punsafeCoerce)
import PlutusLedgerApi.V1.Value (AssetClass (AssetClass))
import Prelude (Applicative (pure), Num ((*)), ($), (.))

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

-- | @since 1.0.1
type PRateDecimal = PFixedDecimal 1000000

-- | @since 1.0.1
newtype PExchangeRate (from :: k) (to :: k') (s :: S)
    = PExchangeRate (Term s (PTagged '(from, to) PRateDecimal))

deriveGeneric ''PExchangeRate

-- | @since 1.0.1
deriving via
    (DerivePNewtype (PExchangeRate from to) (PTagged '(from, to) PRateDecimal))
    instance
        PlutusType (PExchangeRate from to)

-- | @since 1.0.1
deriving via
    (DerivePNewtype (PExchangeRate from to) (PTagged '(from, to) PRateDecimal))
    instance
        PIsData (PExchangeRate from to)

-- | @since 1.0.1
deriving via
    (DerivePNewtype (PExchangeRate from to) (PTagged '(from, to) PRateDecimal))
    instance
        PEq (PExchangeRate from to)

-- | @since 1.0.1
deriving via
    (DerivePNewtype (PExchangeRate from to) (PTagged '(from, to) PRateDecimal))
    instance
        POrd (PExchangeRate from to)

-- | @since 1.0.1
deriving anyclass instance PShow (PExchangeRate from to)

-- | @since 1.0.1
instance PTryFrom PData (PAsData (PExchangeRate from to)) where
    type
        PTryFromExcess PData (PAsData (PExchangeRate from to)) =
            PTryFromExcess PData (PAsData PRateDecimal)
    ptryFrom' d k = ptryFrom' @_ @(PAsData PRateDecimal) d $ k . first punsafeCoerce

{- | Make @PExchangeRation@ with given @PIntegers. Two Integers are nominator and denominator.

 @since 1.0.1
-}
pexchangeRatio ::
    forall k.
    forall (to :: k) (from :: k) (s :: S).
    Term s (PInteger :--> PInteger :--> PMaybe (PExchangeRate from to))
pexchangeRatio = phoistAcyclic $ plam $ \n d -> pexchangeRatio' n d

{- | Same as @pexchangeRation@ but in Haskell level.

 @since 1.0.1
-}
pexchangeRatio' ::
    forall k.
    forall (to :: k) (from :: k) (s :: S).
    Term s PInteger ->
    Term s PInteger ->
    Term s (PMaybe (PExchangeRate from to))
pexchangeRatio' n d =
    pif
        (d #== 0)
        (pcon PNothing)
        ( pcon . PJust $
            pcon . PExchangeRate $
                ppure #$ (fromPInteger # n) `divide` (fromPInteger # d)
        )

{- | Change one @PDiscrete@ to other with given exchange rate.

 @since 1.0.1
-}
pexchange ::
    forall k.
    forall (to :: k) (from :: k) (s :: S).
    Term s (PExchangeRate from to :--> PDiscrete from :--> PDiscrete to)
pexchange = phoistAcyclic $ plam $ \rate x -> pexchange' rate x

{- | Same as @pexchange@ but in Haskell level.

 @since 1.0.1
-}
pexchange' ::
    forall k.
    forall (to :: k) (from :: k) (s :: S).
    Term s (PExchangeRate from to) ->
    Term s (PDiscrete from) ->
    Term s (PDiscrete to)
pexchange' rate' x' = unTermCont $ do
    PExchangeRate ((pextract #) -> rate) <- pmatchC rate'
    PDiscrete ((fromPInteger #) . (pextract #) -> x) <- pmatchC x'
    pure . pcon . PDiscrete $ ppure #$ toPInteger # (x * rate)

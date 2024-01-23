{-# LANGUAGE GADTs, MonoLocalBinds, DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
module BabySingleton where

import Data.Kind (Type)
import Data.Type.Equality
import GHC.TypeNats
import Data.Maybe (isJust)

type family Sing k :: k -> Type

class Demote k where
    type Val k :: Type
    toSing :: Val k -> (forall x. Sing k x -> r) -> r
    fromSing :: Sing k x -> Val k

singEq :: TestEquality (Sing k) => Sing k a -> Sing k b -> Bool
singEq a b = isJust (testEquality a b)

class ISing k (x :: k) where
    sing :: Sing k x

-- * Unit

data SUnit (u :: ()) where SU :: SUnit '()

type instance Sing () = SUnit

instance Demote () where
    type Val () = ()
    toSing _ body = body SU
    fromSing SU = ()

instance ISing () '() where sing = SU

-- * Nat

type instance Sing Nat = SNat

instance Demote Nat where
    type Val Nat = Natural
    toSing = withSomeSNat
    fromSing = fromSNat

instance KnownNat n => ISing Nat n where
    sing = natSing

-- * Bool

data SBool (b :: Bool) where
    STrue :: SBool True
    SFalse :: SBool False

type instance Sing Bool = SBool

instance TestEquality SBool where
    testEquality SFalse SFalse = Just Refl
    testEquality STrue STrue = Just Refl
    testEquality _ _ = Nothing

instance Demote Bool where
    type Val Bool = Bool

    toSing False b = b SFalse
    toSing True b = b STrue

    fromSing SFalse = False
    fromSing STrue = True

instance ISing Bool False where sing = SFalse
instance ISing Bool True where sing = STrue
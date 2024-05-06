{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Data.Bool.Singletons where

import Data.Singletons
import Data.Kind (Type)

type SBool :: Bool -> Type
data SBool b where
  SFalse :: SBool False
  STrue :: SBool True

type instance Sing = SBool

instance SingI False where sing = SFalse
instance SingI True where sing = STrue

instance SingKind Bool where
  type Demote Bool = Bool

  fromSing sb = case sb of
    SFalse -> False
    STrue -> True

  toSing False = SomeSing SFalse
  toSing True  = SomeSing STrue
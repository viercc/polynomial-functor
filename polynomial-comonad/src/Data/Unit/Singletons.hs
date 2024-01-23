{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Data.Unit.Singletons where
import Data.Kind (Type)
import Data.Singletons

type SUnit :: () -> Type
data SUnit b where
  SU :: SUnit '()

type instance Sing = SUnit

instance SingI '() where sing = SU

instance SingKind () where
  type Demote () = ()

  fromSing _ = ()
  toSing _ = SomeSing SU
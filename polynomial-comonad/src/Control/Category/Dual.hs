{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
module Control.Category.Dual where

import Prelude hiding (id, (.))
import Control.Category
import Data.Kind (Type)

type Dual :: forall k. (k -> k -> Type) -> k -> k -> Type
newtype Dual cat a b = Dual { getDual :: cat b a }

instance Category cat => Category (Dual cat) where
    id = Dual id
    Dual cb . Dual ba = Dual (ba . cb)

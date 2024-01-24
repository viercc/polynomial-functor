module SemigroupDo where

(>>) :: Semigroup a => a -> a -> a
(>>) = (<>)

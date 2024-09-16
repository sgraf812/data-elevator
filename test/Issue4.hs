{-# OPTIONS_GHC -O2              #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE UnboxedTuples       #-}
module Issue4 (
    StrictArray,
    primArrayToStrictArray,
    indexStrictArray,
    sizeofStrictArray,
) where

import           Data.Elevator (Strict (Strict))
import qualified Data.Primitive as P
import qualified GHC.Exts as GHC
import           GHC.Exts ((+#))
import           GHC.ST (ST(ST), runST)

data StrictArray a = StrictArray !(GHC.Array# (Strict a))

primArrayToStrictArray :: forall a. P.Array a -> StrictArray a
primArrayToStrictArray (P.Array a) =
    runST $ ST $ \s0 ->
    case GHC.newArray# (GHC.sizeofArray# a) (Strict (P.indexArray (P.Array a) 0)) s0 of
      (# s1, a#  #) ->
        case go a# 0# s1 of
          s2 -> case GHC.unsafeFreezeArray# a# s2 of
                  (# s3, a'# #) -> (# s3, StrictArray a'# #)
  where
    go :: forall s.
          GHC.MutableArray# s (Strict a)
       -> GHC.Int#
       -> GHC.State# s
       -> GHC.State# s
    go a# i# s =
      case i# GHC.<# GHC.sizeofArray# a of
        1# ->
          case GHC.indexArray# a i# of
            (# x #) ->
              -- We have to use seq# here to force the array element to WHNF
              -- before putting it into the strict array. This should not be
              -- necessary. https://github.com/sgraf812/data-elevator/issues/4
{-              case GHC.seq# x s of
                (# s', x' #) ->
-}
                  case GHC.writeArray# a# i# (Strict x) s of
                    s' -> go a# (i# +# 1#) s'
        _  -> s

{-# INLINE indexStrictArray #-}
indexStrictArray :: StrictArray a -> Int -> a
indexStrictArray (StrictArray a#) (GHC.I# i#) =
    case GHC.indexArray# a# i# of
      (# Strict x #) -> x

{-# INLINE sizeofStrictArray #-}
sizeofStrictArray :: StrictArray a -> Int
sizeofStrictArray (StrictArray a#) =
    GHC.I# (GHC.sizeofArray# a#)

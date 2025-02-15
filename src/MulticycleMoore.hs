module MulticycleMoore
  ( delay'
  , unsafeLatch0
  , latch'
  , map0
  , map'
  , foldl0
  , foldr0
  , foldl'
  , foldr'
  ) where

import Data.Proxy (Proxy(..))
import Clash.Prelude

-- $

-- $setup
-- >>> :set -fplugin GHC.TypeLits.Extra.Solver -fplugin GHC.TypeLits.Normalise -fplugin GHC.TypeLits.KnownNat.Solver
-- >>> import Prelude ((++), repeat)
-- >>> import Clash.Prelude hiding ((++), repeat)

incr :: forall n. (KnownNat n) => Index n -> Index n -> Index n
incr z i = if i < maxBound then i + 1 else z

prescaler :: forall d dom. (KnownNat d, 1 <= d, HiddenClockResetEnable dom)
          => Proxy d
          -> Signal dom Bool
          -> Signal dom Bool
prescaler _ resetTrigger = resetTrigger .||. (0 ==) <$> d where
  d = register 0 d' :: Signal dom (Index d)
  d' = mux resetTrigger (incr 0 <$> 0) (incr 0 <$> d)

counter :: forall n dom. (KnownNat n, 1 <= n, HiddenClockResetEnable dom)
        => Signal dom Bool
        -> Signal dom Bool
        -> Signal dom (Index n)
counter resetTrigger trigger = mux trigger n' n where
  n = regEn maxBound trigger n'
  n' = mux resetTrigger 0 $ incr maxBound <$> n

--

delay' :: forall n m dom
        . ( KnownNat n
          , 1 <= n
          , HiddenClockResetEnable dom
          )
       => DSignal dom m Bool
       -> DSignal dom (m + n) Bool
delay' trigger = unsafeFromSignal trigger' where
  s 0 False = 0
  s i b = if i < maxBound then i + 1 else if b then 1 else 0
  o = (maxBound ==)
  z = 0 :: Index (n + 1)
  trigger' = moore s o z $ toSignal trigger

--

unsafeLatch0 :: forall l m a dom
              . ( NFDataX a
              , HiddenClockResetEnable dom
              )
             => DSignal dom m Bool
             -> DSignal dom m a
             -> DSignal dom (m + l) a
unsafeLatch0 trigger' din' = dout' where
  rout = register undefined rin
  rin = mux (toSignal trigger') (toSignal din') rout
  dout' = unsafeFromSignal rin

latch' :: forall l m a dom
        . ( 1 <= l
          , NFDataX a
          , HiddenClockResetEnable dom
          )
       => DSignal dom m Bool
       -> DSignal dom m a
       -> DSignal dom (m + l) a
latch' trigger' din' = dout' where
  rout = register undefined rin
  rin = mux (toSignal trigger') (toSignal din') rout
  dout' = unsafeFromSignal rout

-- | map0 & map'
-- >>> f a b = a * b
-- >>> tr = fromSignal . fromList $ [undefined, True, False, False, True] ++ repeat False
-- >>> a = fromSignal . fromList $ [undefined, 2, 2, 2, 3, 3, 3, 5, 5, 5 :: Int]
-- >>> bs = fromSignal . fromList $ fmap (iterateI @2 (+ 10)) [undefined, 2, 2, 2, 3, 3, 3, 5, 5, 5 :: Int]
-- >>> bs' = toSignal $ map0 f tr a bs
-- >>> printX $ sampleWithResetN @System d1 9 $ fmap head bs'
-- [undefined,2,4,4,3,9,9,9,9]
-- >>> printX $ sampleWithResetN @System d1 9 $ fmap last bs'
-- [undefined,12,12,24,13,13,39,39,39]
-- >>> f' tr' a' b' = unsafeFromSignal . register undefined . regEn undefined (toSignal tr') $ f <$> toSignal a' <*> toSignal b'
-- >>> tr = fromSignal . fromList $ [undefined, True, False, False, False, False, True] ++ repeat False
-- >>> a = fromSignal . fromList $ [undefined, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 5, 5 :: Int]
-- >>> bs = fromSignal . fromList $ fmap (iterateI @2 (+ 10)) [undefined, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 5, 5 :: Int]
-- >>> bs' = toSignal $ map' @0 @_ @_ @2 f' tr a bs
-- >>> printX $ sampleWithResetN @System d1 12 $ fmap head bs'
-- [undefined,2,2,4,4,4,3,3,9,9,9,9]
-- >>> printX $ sampleWithResetN @System d1 12 $ fmap last bs'
-- [undefined,12,12,12,12,24,13,13,13,13,39,39]

map0 :: forall l m n a b dom
      . ( KnownNat n
        , 1 <= n
        , NFDataX b
        , HiddenClockResetEnable dom
        )
     => (a -> b -> b)
     -> DSignal dom m Bool
     -> DSignal dom m a
     -> DSignal dom m (Vec n b)
     -> DSignal dom (m + (n + 1) + l) (Vec n b)
map0 f = map' f' where
  f' :: DSignal dom 0 Bool -> DSignal dom 0 a -> DSignal dom 0 b -> DSignal dom 1 b
  f' trigger' a' b' = unsafeFromSignal . regEn undefined (toSignal trigger') $ f <$> toSignal a' <*> toSignal b'

map' :: forall l m n d a b dom
      . ( KnownNat n
        , KnownNat d
        , 1 <= n
        , 1 <= d
        , NFDataX b
        , HiddenClockResetEnable dom
        )
     => (DSignal dom 0 Bool -> DSignal dom 0 a -> DSignal dom 0 b -> DSignal dom d b)
     -> DSignal dom m Bool
     -> DSignal dom m a
     -> DSignal dom m (Vec n b)
     -> DSignal dom (m + (n * d + 1) + l) (Vec n b)
map' f' trigger' a' bsin' = unsafeFromSignal bs' where
  trigger = toSignal trigger'
  tr = prescaler @d Proxy trigger
  i = counter @(n + 1) trigger tr
  iLTn = (maxBound >) <$> i
  b' = toSignal $ f' (fromSignal $ tr .&&. iLTn) (fromSignal $ toSignal a') (fromSignal b)
  b = mux iLTn (liftA2 (!!) bs i) $ pure undefined
  bs' = regEn undefined tr bs
  bs = mux ((0 ==) <$> i) (toSignal bsin') $ replace <$> (flip (-) 1 <$> i) <*> b' <*> bs'

--

fold0 :: forall l m n a b dom
       . ( KnownNat n
         , 1 <= n
         , NFDataX b
         , HiddenClockResetEnable dom
         )
      => Either () ()
      -> (a -> b -> b)
      -> DSignal dom m Bool
      -> DSignal dom m b
      -> DSignal dom m (Vec n a)
      -> DSignal dom (m + n + l) b
fold0 lr f = fold' lr f' where
  f' :: DSignal dom 0 Bool -> DSignal dom 0 a -> DSignal dom 0 b -> DSignal dom 1 b
  f' trigger' a' b' = unsafeFromSignal . regEn undefined (toSignal trigger') $ f <$> toSignal a' <*> toSignal b'

fold' :: forall l m n d a b dom
       . ( KnownNat n
         , KnownNat d
         , 1 <= n
         , 1 <= d
         , NFDataX b
         , HiddenClockResetEnable dom
         )
      => Either () ()
      -> (DSignal dom 0 Bool -> DSignal dom 0 a -> DSignal dom 0 b -> DSignal dom d b)
      -> DSignal dom m Bool
      -> DSignal dom m b
      -> DSignal dom m (Vec n a)
      -> DSignal dom (m + n * d + l) b
fold' lr f' trigger' b0' as' = unsafeFromSignal b' where
  trigger = toSignal trigger'
  tr = prescaler @d Proxy trigger
  i = counter @(n + 1) trigger tr
  iLTn = (maxBound >) <$> i
  b' = toSignal $ f' (fromSignal $ tr .&&. iLTn) (fromSignal a) (fromSignal b)
  b = mux ((0 ==) <$> i) (toSignal b0') . toSignal $ unsafeLatch0 (fromSignal tr) (fromSignal b')
  a = mux iLTn (liftA2 (!!) (toSignal as') j) $ pure undefined
  j = (\ k -> if lr == Left () then k else maxBound - 1 - k) <$> i

-- | fold*
-- >>> f x a b = if a then x * b * b else b * b
-- >>> tr = fromSignal . fromList $ [undefined, True, False, False, True] ++ repeat False
-- >>> b = fromSignal $ fromList [undefined, 1, 1, 1, 2, 2, 2, 3, 3, 3 :: Int]
-- >>> as = pure $ False :> True :> True :> Nil
-- >>> b' = toSignal $ foldl0 (f 2) tr b as
-- >>> printX $ sampleWithResetN @System d1 9 b'
-- [undefined,1,2,8,4,32,2048,2048,2048]
-- >>> b' = toSignal $ foldr0 (f 2) tr b as
-- >>> printX $ sampleWithResetN @System d1 9 b'
-- [undefined,2,8,64,8,128,16384,16384,16384]
-- >>> f' x' tr' a' b' = unsafeFromSignal . register undefined . regEn undefined (toSignal tr') $ f <$> toSignal x' <*> toSignal a' <*> toSignal b'
-- >>> tr = fromSignal . fromList $ [undefined, True, False, False, False, False, False, True] ++ repeat False
-- >>> x = fromSignal . fromList $ [undefined, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5 :: Int]
-- >>> b = fromSignal . fromList $ undefined : repeat (1 :: Int)
-- >>> as = pure $ False :> True :> True :> Nil
-- >>> b' = toSignal $ foldl' @0 @_ @_ @2 (f' x) tr b as
-- >>> printX $ sampleWithResetN @System d1 18 b'
-- [undefined,undefined,1,1,2,2,8,8,1,1,3,3,27,27,27,27,27,27]
-- >>> b' = toSignal $ foldr' @0 @_ @_ @2 (f' x) tr b as
-- >>> printX $ sampleWithResetN @System d1 18 b'
-- [undefined,undefined,2,2,8,8,64,64,3,3,27,27,729,729,729,729,729,729]

foldl0 :: forall l m n a b dom
        . ( KnownNat n
          , 1 <= n
          , NFDataX b
          , HiddenClockResetEnable dom
          )
       => (a -> b -> b)
       -> DSignal dom m Bool
       -> DSignal dom m b
       -> DSignal dom m (Vec n a)
       -> DSignal dom (m + n + l) b
foldl0 = fold0 $ Left ()

foldr0 :: forall l m n a b dom
        . ( KnownNat n
          , 1 <= n
          , NFDataX b
          , HiddenClockResetEnable dom
          )
       => (a -> b -> b)
       -> DSignal dom m Bool
       -> DSignal dom m b
       -> DSignal dom m (Vec n a)
       -> DSignal dom (m + n + l) b
foldr0 = fold0 $ Right ()

foldl' :: forall l m n d a b dom
        . ( KnownNat n
          , KnownNat d
          , 1 <= n
          , 1 <= d
          , NFDataX b
          , HiddenClockResetEnable dom
          )
       => (DSignal dom 0 Bool -> DSignal dom 0 a -> DSignal dom 0 b -> DSignal dom d b)
       -> DSignal dom m Bool
       -> DSignal dom m b
       -> DSignal dom m (Vec n a)
       -> DSignal dom (m + n * d + l) b
foldl' = fold' $ Left ()

foldr' :: forall l m n d a b dom
        . ( KnownNat n
          , KnownNat d
          , 1 <= n
          , 1 <= d
          , NFDataX b
          , HiddenClockResetEnable dom
          )
       => (DSignal dom 0 Bool -> DSignal dom 0 a -> DSignal dom 0 b -> DSignal dom d b)
       -> DSignal dom m Bool
       -> DSignal dom m b
       -> DSignal dom m (Vec n a)
       -> DSignal dom (m + n * d + l) b
foldr' = fold' $ Right ()

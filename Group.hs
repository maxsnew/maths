module Group where

import Control.Applicative
import Data.Monoid

class (Monoid g) => Group g where
  inv  :: g -> g

  {- LAWS, assume monoid laws -}
  -- | forall x, mempty <> x = x <> mempty = x
  -- | forall x, x <> inv x = inv x <> x = mempty

instance Group () where
  inv () = ()

instance Num a => Group (Sum a) where
  inv = Sum . negate . getSum

instance Group a => Group (Maybe a) where
  inv m = inv <$> m

instance (Group a, Group b) => Group (a,b) where
  inv (g,h) = (inv g, inv h)

data FreeProd g h =
  Empty
  | StartL g (Alt h g)
  | StartR h (Alt g h)
  deriving (Show, Read, Eq, Ord)

data Alt a b =
  Done
  | a :#: Alt b a
  deriving (Show, Read, Eq, Ord)

infixr 5 :#:

instance (Eq g, Group g, Eq h, Group h) => Monoid (FreeProd g h) where
  mempty = Empty
  Empty `mappend` _ = Empty
  _ `mappend` Empty = Empty
  ls `mappend` rs = case ls of
    StartL g hgs ->
      alt_append (g :#: hgs) $ case rs of
        StartL g' hgs' -> Left (g' :#: hgs')
        StartR h ghs   -> Right (h :#: ghs)
    StartR h ghs ->
      swap_prod . alt_append (h :#: ghs) $ case rs of
        StartL g hgs   -> Right (g :#: hgs)
        StartR h' ghs' -> Left (h' :#: ghs')

type SomeAlt a b = Either (Alt a b) (Alt b a)

alt_append :: (Group g, Eq g, Group h, Eq h) =>
              Alt g h -> SomeAlt g h -> FreeProd g h
alt_append ls rs = case (alt_rev ls, rs) of
  (Left ghs, Left ghs')   -> smush ghs ghs'
  (Left ghs, Right hgs)   -> swap_prod $ rev_append ghs hgs
  (Right hgs, Left ghs)   -> rev_append hgs ghs
  (Right hgs, Right hgs') -> swap_prod $ smush hgs hgs'

swap_prod :: FreeProd a b -> FreeProd b a
swap_prod p = case p of
  Empty -> Empty
  StartL g hgs -> StartR g hgs
  StartR h ghs -> StartL h ghs

smush :: (Eq g, Eq h, Group g, Group h) =>
         Alt g h -- reversed list
         -> Alt g h
         -> FreeProd g h
smush ls rs = case (ls, rs) of
  (Done, Done) -> Empty
  (Done, (g :#: hgs)) -> StartL g hgs
  (ghs, Done) -> swap_prod $ rev_append ghs Done
  (g :#: hgs, g' :#: hgs') ->
    if newG == mempty
    then swap_prod $ smush hgs hgs'
    else rev_append hgs (newG :#: hgs')
    where newG = g <> g'

rev_append :: Alt b a -> Alt a b -> FreeProd a b
rev_append Done r = case r of
  Done      -> Empty
  g :#: hgs -> StartL g hgs
rev_append (h :#: ghs) r = swap_prod $ rev_append ghs (h :#: r)

type BN = Alt Bool Int
type NB = Alt Int Bool

rev_append_tests =
  [ ((Done :: BN)  `rev_append` Done)
    == Empty
  , ((0 :#: Done) `rev_append` (Done :: BN))
    == StartR 0 Done
  , ((True :#: 0 :#: Done) `rev_append` (1 :#: False :#: Done))
    == StartL 0 (True :#: 1 :#: False :#: Done)
  ]

alt_rev :: Alt a b -> Either (Alt a b) (Alt b a)
alt_rev ghs = go ghs Done
  where go :: Alt a b -> Alt b a -> Either (Alt a b) (Alt b a)
        go Done r = Right r
        go (g :#: hgs) r = swap $ go hgs (g :#: r)

swap :: Either a b -> Either b a
swap = either Right Left

module Bound (
    class Bound, subst, flipSubst, (=<<<), (>>>=), substDefault,
    Var(..),
    Scope(..), unScope,
    fromScope, toScope,
    abstract, abstract1,
    instantiate, instantiate1,
    splat,
    bindings,
    mapBound, mapScope,
    foldMapBound, foldMapScope,
    traverseBound, traverseScope,
    traverseBound_, traverseScope_,
    hoistScope
    ) where

import Control.Apply (lift2)
import Control.Monad.Trans.Class (class MonadTrans, lift)
import Control.Monad.Cont (ContT)
import Control.Monad.Except (ExceptT)
import Control.Monad.List.Trans (ListT)
import Control.Monad.Maybe.Trans (MaybeT)
import Control.Monad.RWS (RWST)
import Control.Monad.Reader (ReaderT)
import Control.Monad.State (StateT)
import Control.Monad.Writer (WriterT)
import Data.Bifunctor (class Bifunctor, bimap)
import Data.Bifoldable (class Bifoldable, bifoldMap, bifoldrDefault, bifoldlDefault)
import Data.Bitraversable (class Bitraversable, bitraverse, bisequenceDefault)
import Data.Foldable (class Foldable, foldMap, foldrDefault, foldlDefault)
import Data.Generic (class Generic, gShow)
import Data.Traversable (class Traversable, traverse, sequenceDefault)
import Data.Maybe (Maybe(..))
import Data.Monoid (class Monoid, mempty)
import Prelude


class Bound t where
    subst :: forall f a c. Monad f => (a -> f c) -> t f a -> t f c

substDefault :: forall t f a c. (MonadTrans t, Monad f, Monad (t f)) => (a -> f c) -> t f a -> t f c
substDefault f m = m >>= (f >>> lift)

flipSubst :: forall f t a c. (Bound t, Monad f) => t f a -> (a -> f c) -> t f c
flipSubst = flip subst

infixl 1 subst as =<<<
infixr 1 flipSubst as >>>=


instance boundContT :: Bound (ContT r) where
    subst = substDefault
instance boundExceptT :: Bound (ExceptT e) where
    subst = substDefault
instance boundListT :: Bound ListT where
    subst = substDefault
instance boundMaybeT :: Bound MaybeT where
    subst = substDefault
instance boundRWST :: Monoid w => Bound (RWST r w s) where
    subst = substDefault
instance boundReaderT :: Bound (ReaderT r) where
    subst = substDefault
instance boundStateT :: Bound (StateT s) where
    subst = substDefault
instance boundWriterT :: Monoid w => Bound (WriterT w) where
    subst = substDefault


data Var b a = B b | F a

derive instance genericVar :: (Generic b, Generic a) => Generic (Var b a)
derive instance eqVar :: (Eq b, Eq a) => Eq (Var b a)
derive instance ordVar :: (Ord b, Ord a) => Ord (Var b a)
instance showVar :: (Generic b, Generic a) => Show (Var b a) where
    show = gShow

instance functorVar :: Functor (Var b) where
    map = liftA1
instance applyVar :: Apply (Var b) where
    apply = ap
instance applicativeVar :: Applicative (Var b) where
    pure = F
instance bindVar :: Bind (Var b) where
    bind (B x) f = B x
    bind (F y) f = f y
instance monadVar :: Monad (Var b)

instance foldableVar :: Foldable (Var b) where
    foldMap f (B x) = mempty
    foldMap f (F y) = f y
    foldr f = foldrDefault f
    foldl f = foldlDefault f
instance traversableVar :: Traversable (Var b) where
    traverse f (B x) = pure (B x)
    traverse f (F y) = F <$> f y
    sequence x = sequenceDefault x

instance bifunctorVar :: Bifunctor Var where
    bimap f g (B x) = B (f x)
    bimap f g (F y) = F (g y)
instance bifoldableVar :: Bifoldable Var where
    bifoldMap f g (B x) = f x
    bifoldMap f g (F y) = g y
    bifoldr f = bifoldrDefault f
    bifoldl f = bifoldlDefault f
instance bitraversableVar :: Bitraversable Var where
    bitraverse f g (B x) = B <$> f x
    bitraverse f g (F y) = F <$> g y
    bisequence x = bisequenceDefault x


newtype Scope b f a = Scope (f (Var b (f a)))
unScope :: forall b f a. Scope b f a -> f (Var b (f a))
unScope (Scope x) = x

fromScope :: forall b f a. Monad f => Scope b f a -> f (Var b a)
fromScope scope = do
    var <- unScope scope
    case var of
        F expr -> map F expr
        B b -> pure (B b)

toScope :: forall b f a. Monad f => f (Var b a) -> Scope b f a
toScope = Scope <<< map (map pure)

derive instance genericScope :: (Generic b, Generic (f (Var b (f a))), Generic a) => Generic (Scope b f a)
derive instance eqScope :: (Eq b, Eq (f (Var b (f a))), Eq a) => Eq (Scope b f a)
derive instance ordScope :: (Ord b, Ord (f (Var b (f a))), Ord a) => Ord (Scope b f a)
instance showScope :: (Generic b, Generic (f (Var b (f a))), Generic a) => Show (Scope b f a) where
    show = gShow

instance functorScope :: Functor f => Functor (Scope b f) where
    map f = Scope <<< map (map (map f)) <<< unScope
instance applyScope :: Monad f => Apply (Scope b f) where
    apply = ap
instance applicativeScope :: Monad f => Applicative (Scope b f) where
    pure = Scope <<< pure <<< pure <<< pure
instance bindScope :: Monad f => Bind (Scope b f) where
    bind (Scope expr) f = Scope $ do
        var <- expr
        case var of
             B b -> pure (B b)
             F fx -> fx >>= (f >>> unScope)
instance monadScope :: Monad f => Monad (Scope b f)

instance monadTransScope :: MonadTrans (Scope b) where
    lift m = Scope (pure (F m))
instance boundScope :: Bound (Scope b) where
    subst = substDefault

instance foldableScope :: Foldable f => Foldable (Scope b f) where
    foldMap f = foldMap (foldMap (foldMap f)) <<< unScope
    foldr f = foldrDefault f
    foldl f = foldlDefault f
instance traversableScope :: Traversable f => Traversable (Scope b f) where
    traverse f = map Scope <<< traverse (traverse (traverse f)) <<< unScope
    sequence s = sequenceDefault s


abstract :: forall a b f. Monad f => (a -> Maybe b) -> f a -> Scope b f a
abstract f = Scope <<< map g
    where g var = case f var of
            Nothing -> F (pure var)
            Just b -> B b
abstract1 :: forall a f. (Eq a, Monad f) => a -> f a -> Scope Unit f a
abstract1 x = abstract (\y -> if x == y then Just unit else Nothing)


instantiate :: forall a b f. Monad f => (b -> f a) -> Scope b f a -> f a
instantiate f scope = do
    var <- unScope scope
    case var of
        B b -> f b
        F a -> a
instantiate1 :: forall a b f. Monad f => f a -> Scope b f a -> f a
instantiate1 expr = instantiate (const expr)

splat :: forall a b c f. Monad f => (a -> f c) -> (b -> f c) -> Scope b f a -> f c
splat f g s = do
    var <- unScope s
    case var of
        B b -> g b
        F expr -> expr >>= f

bindings :: forall a b f. Foldable f => Scope b f a -> Array b
bindings = foldMap f <<< unScope
    where f (B v) = [v]
          f _ = []

mapBound :: forall a b c f. Functor f => (b -> c) -> Scope b f a -> Scope c f a
mapBound f = mapScope f id

mapScope :: forall a b c d f. Functor f => (b -> d) -> (a -> c) -> Scope b f a -> Scope d f c
mapScope f g = Scope <<< map (bimap f (map g)) <<< unScope

foldMapBound :: forall a b m f. (Foldable f, Monoid m) => (b -> m) -> Scope b f a -> m
foldMapBound f = foldMapScope f (const mempty)

foldMapScope :: forall a b m f. (Foldable f, Monoid m) => (b -> m) -> (a -> m) -> Scope b f a -> m
foldMapScope f g = foldMap (bifoldMap f (foldMap g)) <<< unScope

traverseBound :: forall a b c f m. (Traversable f, Applicative m) => (b -> m c) -> Scope b f a -> m (Scope c f a)
traverseBound f = traverseScope f pure

traverseScope :: forall a b c d f m. (Traversable f, Applicative m) => (b -> m d) -> (a -> m c) -> Scope b f a -> m (Scope d f c)
traverseScope f g = map Scope <<< traverse (bitraverse f (traverse g)) <<< unScope

newtype AM f a = AM (f a)  -- for "Applicative Monoid"
getAM :: forall f a. AM f a -> f a
getAM (AM x) = x

instance semigroupAM :: (Semigroup a, Apply f) => Semigroup (AM f a) where
    append (AM x) (AM y) = AM (lift2 append x y)
instance monoidAM :: (Monoid a, Applicative f) => Monoid (AM f a) where
    mempty = AM $ pure mempty


traverseBound_ :: forall a b c f m. (Foldable f, Applicative m) => (b -> m c) -> Scope b f a -> m Unit
traverseBound_ f = getAM <<< foldMapBound (AM <<< map (const unit) <<< f)

traverseScope_ :: forall a b c d f m. (Foldable f, Applicative m) => (b -> m d) -> (a -> m c) -> Scope b f a -> m Unit
traverseScope_ f g = getAM <<< foldMapScope (AM <<< map (const unit) <<< f) (AM <<< map (const unit) <<< g)

hoistScope :: forall f g a b. Functor f => (forall x. f x -> g x) -> Scope b f a -> Scope b g a
hoistScope eta = Scope <<< eta <<< map (map eta) <<< unScope





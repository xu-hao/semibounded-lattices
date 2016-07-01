{-# LANGUAGE FlexibleInstances #-}
{-|
Module      : Algebra.SemiBoundedLattice
Description : Haskell typeclasses and instances of semibounded lattices, Heyting algebra, co-Heyting algebra, and Boolean algebra
Copyright   : (c) Hao Xu, 2016
License     : BSD-3
Maintainer  : xuh@email.unc.edu
Stability   : experimental
Portability : portable

Haskell typeclasses and instances of semibounded lattices, Heyting algebra, co-Heyting algebra, and Boolean algebra
-}
module Algebra.SemiBoundedLattice (
  Complemented (..), (/\\), (//\),
  DistributiveLattice, LowerBoundedLattice, UpperBoundedLattice, LowerBoundedDistributiveLattice, UpperBoundedDistributiveLattice, BooleanAlgebra (..),
  HeytingAlgebra, CoHeytingAlgebra, SemiHeytingAlgebra (..), SemiCoHeytingAlgebra (..), BiHeytingAlgebra) where

-- import Data.List (union, intersect, (\\))
import Data.Set (union, intersection, (\\), Set)

import Algebra.Lattice

-- | The combination of a JoinSemiLattice and a BoundedMeetSemiLattice makes an UpperBoundedLattice if the absorption law holds:
--
-- > Absorption: a \/ (a /\ b) == a /\ (a \/ b) == a
class (JoinSemiLattice a, BoundedMeetSemiLattice a) => UpperBoundedLattice a where

-- | The combination of a BoundedJoinSemiLattice and a MeetSemiLattice makes an LowerBoundedLattice if the absorption law holds:
--
-- > Absorption: a \/ (a /\ b) == a /\ (a \/ b) == a
class (BoundedJoinSemiLattice a, MeetSemiLattice a) => LowerBoundedLattice a where

-- | A lattice is distributive if the distributivity law holds:
--
-- > Distributivity: a /\ (b \/ c) == (a /\ b) \/ (a /\ c)
-- see <https://en.wikipedia.org/wiki/Distributive_lattice>
class Lattice a => DistributiveLattice a where

-- | A lattice is distributive if the distributivity law holds:
--
-- > Distributivity: a /\ (b \/ c) == (a /\ b) \/ (a /\ c)
-- see <https://en.wikipedia.org/wiki/Distributive_lattice>
class LowerBoundedLattice a => LowerBoundedDistributiveLattice a where

-- | A lattice is distributive if the distributivity law holds:
--
-- > Distributivity: a /\ (b \/ c) == (a /\ b) \/ (a /\ c)
-- see <https://en.wikipedia.org/wiki/Distributive_lattice>
class UpperBoundedLattice a => UpperBoundedDistributiveLattice a where

-- | A semi-co-Heyting Algebra is dual of a semi-Heyting algebra where the following law holds:
--
-- > x \\\ y <= z if and only if x <= y \/ z
-- see <https://ncatlab.org/nlab/show/co-Heyting+algebra>
class LowerBoundedDistributiveLattice a => SemiCoHeytingAlgebra a where
  subtraction :: a -> a -> a
  (\\\) :: a -> a -> a
  (\\\) = subtraction
  subtraction = (\\\)

-- | supplement
-- see <https://ncatlab.org/nlab/show/co-Heyting+negation>
class (BoundedLattice a, SemiCoHeytingAlgebra a) => CoHeytingAlgebra a where
  supplement :: a -> a
  supplement a = top \\\ a

-- | In most literature, a Heyting algebra requires a bounded lattice.
-- We only require a UpperBoundedDistributiveLattice here for semi-Heyting algebra. (here the lattice must be upper bounded)
-- The following law holds:
--
-- > x /\ a <= b if and only if x <= (a --> b)
-- see <https://ncatlab.org/nlab/show/Heyting+algebra>
-- Heyting algebras are always distributive. see <https://en.wikipedia.org/wiki/Heyting_algebra#Distributivity>
--
class UpperBoundedDistributiveLattice a => SemiHeytingAlgebra a where
  implication :: a -> a -> a
  (-->) :: a -> a -> a
  (-->) = implication
  implication = (-->)

-- | negation
-- see <https://ncatlab.org/nlab/show/Heyting+algebra>
class (BoundedLattice a, SemiHeytingAlgebra a) => HeytingAlgebra a where
  negation :: a -> a
  negation a = a --> bottom

-- | A lattice that is both a Heyting algebra and a co-Heyting algebra is a bi-Heyting algebra
class (HeytingAlgebra a, CoHeytingAlgebra a) => BiHeytingAlgebra a where

-- | A Boolean Algebra is a complemented distributive lattice, see <https://en.wikipedia.org/wiki/Boolean_algebra_(structure)>
-- or equivalently a Heyting algebra where
--
-- > negation (negation a) == a
-- in a Boolean algebra
--
-- > supplement == negation
class BiHeytingAlgebra a => BooleanAlgebra a where
  complement :: a -> a
  complement = supplement

data Complemented a = Include a | Exclude a deriving Show

instance SemiCoHeytingAlgebra a => JoinSemiLattice (Complemented a) where
    join (Include vars) (Include vars2) = Include (vars \/ vars2)
    join (Include vars) (Exclude vars2) = Exclude (vars2 \\\ vars)
    join (Exclude vars) (Include vars2) = Exclude (vars \\\ vars2)
    join (Exclude vars) (Exclude vars2) = Exclude (vars2 /\ vars)

instance SemiCoHeytingAlgebra a => MeetSemiLattice (Complemented a) where
    meet (Include vars) (Include vars2) = Include (vars /\ vars2)
    meet (Exclude vars) (Include vars2) = Include (vars2 \\\ vars)
    meet (Include vars) (Exclude vars2) = Include (vars \\\ vars2)
    meet (Exclude vars) (Exclude vars2) = Exclude (vars \/ vars2)

instance SemiCoHeytingAlgebra a => BoundedJoinSemiLattice (Complemented a) where
    bottom = bottom

instance SemiCoHeytingAlgebra a => BoundedMeetSemiLattice (Complemented a) where
    top = Exclude bottom

instance SemiCoHeytingAlgebra a => Lattice (Complemented a) where
instance SemiCoHeytingAlgebra a => LowerBoundedLattice (Complemented a) where
instance SemiCoHeytingAlgebra a => UpperBoundedLattice (Complemented a) where
instance SemiCoHeytingAlgebra a => BoundedLattice (Complemented a) where
instance SemiCoHeytingAlgebra a => DistributiveLattice (Complemented a) where
instance SemiCoHeytingAlgebra a => LowerBoundedDistributiveLattice (Complemented a) where
instance SemiCoHeytingAlgebra a => UpperBoundedDistributiveLattice (Complemented a) where
instance SemiCoHeytingAlgebra a => SemiCoHeytingAlgebra (Complemented a) where
  Include a \\\ Include b = Include (a \\\ b)
  Include a \\\ Exclude b = Include (a /\ b)
  Exclude a \\\ Include b = Exclude (a \/ b)
  Exclude a \\\ Exclude b = Include (b \\\ a)

instance SemiCoHeytingAlgebra a => SemiHeytingAlgebra (Complemented a) where
  a --> b = (top \\\ a) \/ b

instance SemiCoHeytingAlgebra a => CoHeytingAlgebra (Complemented a) where
instance SemiCoHeytingAlgebra a => HeytingAlgebra (Complemented a) where
instance SemiCoHeytingAlgebra a => BiHeytingAlgebra (Complemented a) where
instance SemiCoHeytingAlgebra a => BooleanAlgebra (Complemented a) where

instance Ord a => LowerBoundedLattice (Set a)
instance Ord a => LowerBoundedDistributiveLattice (Set a)
instance Ord a => SemiCoHeytingAlgebra (Set a) where
  subtraction = (\\)

(/\\), rmeetproj :: SemiCoHeytingAlgebra a => a -> Complemented a -> a
rmeetproj vars (Include vars2) = vars /\ vars2
rmeetproj vars (Exclude vars2) = vars \\\ vars2
(/\\) = rmeetproj

(//\), lmeetproj :: SemiCoHeytingAlgebra a => Complemented a -> a -> a
lmeetproj (Include vars2) vars = vars /\ vars2
lmeetproj (Exclude vars2) vars = vars \\\ vars2
(//\) = lmeetproj

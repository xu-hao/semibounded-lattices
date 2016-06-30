{-# LANGUAGE FlexibleInstances #-}

module Algebra.SemiBoundedLattice (Complemented (..), (\\\), (/\\), (//\)) where

import Data.List (union, intersect, (\\))

import Algebra.Lattice

-- | The combination of a JoinSemiLattice and a BoundedMeetSemiLattice makes an UpperBoundedLattice if the absorption law holds:
-- > Absorption: a \/ (a /\ b) == a /\ (a \/ b) == a
class (JoinSemiLattice a, BoundedMeetSemiLattice a) => UpperBoundedLattice a where

-- | The combination of a BoundedJoinSemiLattice and a MeetSemiLattice makes an LowerBoundedLattice if the absorption law holds:
-- > Absorption: a \/ (a /\ b) == a /\ (a \/ b) == a
class (BoundedJoinSemiLattice a, MeetSemiLattice a) => LowerBoundedLattice a where

class Lattice a => DistributiveLattice a where

class LowerBoundedLattice a => LowerBoundedDistributiveLattice a where

class UpperBoundedLattice a => UpperBoundedDistributiveLattice a where

-- | A co-Heyting Algebra requires a bounded lattice.
-- here the lattice must be lower bounded
class LowerBoundedDistributiveLattice a => SemiCoHeytingAlgebra a where
  subtraction :: a -> a -> a
  (\\\) :: a -> a -> a
  (\\\) = subtraction
  subtraction = (\\\)

-- | A Boolean Algebra is a complemented distributive lattice, see <https://en.wikipedia.org/wiki/Boolean_algebra_(structure)>
class (BoundedLattice a, DistributiveLattice a) => BooleanAlgebra a where
  complement :: a -> a

newtype BA_SCHA_Inj a = BA_SCHA_Inj a

instance BooleanAlgebra a => MeetSemiLattice (BA_SCHA_Inj a) where
  (BA_SCHA_Inj a) /\ (BA_SCHA_Inj b) = BA_SCHA_Inj (a /\ b)

instance BooleanAlgebra a => JoinSemiLattice (BA_SCHA_Inj a) where
  (BA_SCHA_Inj a) \/ (BA_SCHA_Inj b) = BA_SCHA_Inj (a \/ b)

instance BooleanAlgebra a => BoundedJoinSemiLattice (BA_SCHA_Inj a) where
  bottom = BA_SCHA_Inj bottom

instance BooleanAlgebra a => BoundedMeetSemiLattice (BA_SCHA_Inj a) where
  top = BA_SCHA_Inj top

instance BooleanAlgebra a => LowerBoundedLattice (BA_SCHA_Inj a) where
instance BooleanAlgebra a => LowerBoundedDistributiveLattice (BA_SCHA_Inj a) where
instance BooleanAlgebra a => Lattice (BA_SCHA_Inj a) where
instance BooleanAlgebra a => DistributiveLattice (BA_SCHA_Inj a) where
instance BooleanAlgebra a => BoundedLattice (BA_SCHA_Inj a) where

instance BooleanAlgebra a => BooleanAlgebra (BA_SCHA_Inj a) where
    complement (BA_SCHA_Inj s) = BA_SCHA_Inj (complement s)

instance BooleanAlgebra a => SemiCoHeytingAlgebra (BA_SCHA_Inj a) where
    subtraction s1 s2 = s1 /\ complement s2

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

instance SemiCoHeytingAlgebra a => BooleanAlgebra (Complemented a) where
    complement (Include vars) = Exclude vars
    complement (Exclude vars) = Include vars

instance SemiCoHeytingAlgebra a => BoundedJoinSemiLattice (Complemented a) where
    bottom = bottom

instance SemiCoHeytingAlgebra a => BoundedMeetSemiLattice (Complemented a) where
    top = Exclude bottom

instance SemiCoHeytingAlgebra a => Lattice (Complemented a) where
instance SemiCoHeytingAlgebra a => BoundedLattice (Complemented a) where
instance SemiCoHeytingAlgebra a => LowerBoundedLattice (Complemented a) where
instance SemiCoHeytingAlgebra a => DistributiveLattice (Complemented a) where
instance SemiCoHeytingAlgebra a => LowerBoundedDistributiveLattice (Complemented a) where
instance SemiCoHeytingAlgebra a => SemiCoHeytingAlgebra (Complemented a) where
    a \\\ b = case BA_SCHA_Inj a \\\ BA_SCHA_Inj b of BA_SCHA_Inj c -> c

instance Eq a => JoinSemiLattice [a] where
  join = union

instance Eq a => MeetSemiLattice [a] where
  meet = intersect

instance Eq a => BoundedJoinSemiLattice [a] where
  bottom = []
instance Eq a => LowerBoundedLattice [a]
instance Eq a => LowerBoundedDistributiveLattice [a]
instance Eq a => SemiCoHeytingAlgebra [a] where
  subtraction = (\\)

(/\\), rmeetproj :: SemiCoHeytingAlgebra a => a -> Complemented a -> a
rmeetproj vars (Include vars2) = vars /\ vars2
rmeetproj vars (Exclude vars2) = vars \\\ vars2
(/\\) = rmeetproj

(//\), lmeetproj :: SemiCoHeytingAlgebra a => Complemented a -> a -> a
lmeetproj (Include vars2) vars = vars /\ vars2
lmeetproj (Exclude vars2) vars = vars \\\ vars2
(//\) = lmeetproj

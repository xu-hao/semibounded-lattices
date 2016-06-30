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

-- | supplement
-- see <https://ncatlab.org/nlab/show/co-Heyting+negation>
class (BoundedLattice a, SemiCoHeytingAlgebra a) => CoHeytingAlgebra a where
  supplement :: a -> a
  supplement a = top \\\ a

-- | A Heyting Algebra requires a bounded lattice.
-- here the lattice must be lower bounded
class UpperBoundedDistributiveLattice a => SemiHeytingAlgebra a where
  implication :: a -> a -> a
  (-->) :: a -> a -> a
  (-->) = implication
  implication = (-->)

-- | supplement
-- see <https://ncatlab.org/nlab/show/co-Heyting+negation>
class (BoundedLattice a, SemiHeytingAlgebra a) => HeytingAlgebra a where
  negation :: a -> a
  negation a = a --> bottom

class (HeytingAlgebra a, CoHeytingAlgebra a) => BiHeytingAlgebra a where

-- | A Boolean Algebra is a complemented distributive lattice, see <https://en.wikipedia.org/wiki/Boolean_algebra_(structure)>
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

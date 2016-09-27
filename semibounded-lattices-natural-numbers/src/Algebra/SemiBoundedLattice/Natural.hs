{-# LANGUAGE FlexibleInstances #-}
{-|
Module      : Algebra.SemiBoundedLattice.Natural
Description : Instances of semibounded lattices for natural numbers
Copyright   : (c) Hao Xu, 2016
License     : BSD-3
Maintainer  : xuh@email.unc.edu
Stability   : experimental
Portability : portable

This module defines instances of semibounded lattices for natural numbers.
-}
module Algebra.SemiBoundedLattice.Natural () where

import Data.Natural (Natural, monus)
import Algebra.Lattice (JoinSemiLattice(..), MeetSemiLattice(..), BoundedJoinSemiLattice(..))
import Algebra.SemiBoundedLattice(LowerBoundedLattice(..),LowerBoundedDistributiveLattice(..),SemiCoHeytingAlgebra(..))

instance MeetSemiLattice Natural where
  (/\) = min

instance JoinSemiLattice Natural where
  (\/) = max

instance BoundedJoinSemiLattice Natural where
  bottom = 0

instance LowerBoundedLattice Natural

instance LowerBoundedDistributiveLattice Natural

instance SemiCoHeytingAlgebra Natural where
  subtraction = monus

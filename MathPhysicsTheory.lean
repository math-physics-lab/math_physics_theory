module

-- This module serves as the root of the `MathPhysicsTheory` library.
-- Import every module of the library here.
public import MathPhysicsTheory.BoundaryConditions.Dirichlet
public import MathPhysicsTheory.BoundaryConditions.Neumann
public import MathPhysicsTheory.BoundaryConditions.Robin
public import MathPhysicsTheory.SturmLiouville.Eigenvalues
public import MathPhysicsTheory.SturmLiouville.InverseProblem
public import MathPhysicsTheory.SturmLiouville.Operator
public import MathPhysicsTheory.SturmLiouville.Problem
public import MathPhysicsTheory.SturmLiouville.Uniqueness

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

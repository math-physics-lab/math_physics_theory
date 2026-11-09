module

-- This module serves as the root of the `MathPhysicsTheory` library.
-- Import every module of the library here.
public import MathPhysicsTheory.BoundaryConditions.Dirichlet
public import MathPhysicsTheory.BoundaryConditions.Neumann
public import MathPhysicsTheory.BoundaryConditions.Robin
public import MathPhysicsTheory.ODE.SelfAdjoint
public import MathPhysicsTheory.SturmLiouville.Eigenvalues
public import MathPhysicsTheory.SturmLiouville.InverseProblem
public import MathPhysicsTheory.SturmLiouville.InverseProblem.Basic
public import MathPhysicsTheory.SturmLiouville.InverseProblem.Uniqueness
public import MathPhysicsTheory.SturmLiouville.Operator
public import MathPhysicsTheory.SturmLiouville.Problem

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

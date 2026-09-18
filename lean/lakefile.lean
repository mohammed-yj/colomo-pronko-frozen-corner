import Lake
open Lake DSL
package CPFiniteAlgebra where
  version := v!"0.1.0"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "c44e0c8ee63ca166450922a373c7409c5d26b00b"
lean_lib CP

/-- Check every project module through the official Lean frontend with trustLevel = 0.
This avoids executable-location discovery in restricted process namespaces.
Each source is checked in a fresh process; an error fails the build. -/
@[default_target]
target checked pkg : Unit := do
  let env ← getAugmentedEnv
  let lakeEnv ← getLakeEnv
  let mods := #["CP.Polynomial", "CP.BinomialMatrices", "CP.BinomialMatrices.Truncation", "CP.BinomialMatrices.KernelTruncation", "CP.Polynomial.Fractional",
    "CP.Polynomial.Recurrence", "CP.Polynomial.Adjacent", "CP.Kernel.Univariate", "CP.Kernel.Transport", "CP.Kernel.Theta", "CP.Kernel.Bivariate", "CP.Kernel.Roots", "CP.Kernel.Bidegree", "CP.Kernel.Reflection", "CP.Kernel.ReflectionIdentity", "CP.Kernel.ActualC", "CP.Kernel.CReflection", "CP.Kernel.DescentAlgebra", "CP.Kernel.SeriesCoefficients", "CP.EvenBridge", "CP.Kernel.ExactTruncation", "CP.Kernel.EvenInverse",
    "CP.OddBridge", "CP.Kernel.Odd.Lift", "CP.Kernel.Odd.KernelLift", "CP.Kernel.Odd.Upgrade", "CP.Kernel.Odd.NullPolynomial", "CP.Kernel.Odd.NullSubstitution", "CP.Kernel.Odd.SigmaSeries", "CP.Kernel.Odd.NullVector", "CP.Kernel.Odd.Projection", "CP.Kernel.Odd.Nullspace", "CP.BlockElimination", "CP.FiniteBridge", "CP.Connection.Coordinates", "CP.Connection.BinomialBlocks", "CP.Connection.EvenFold", "CP.Connection.CandidateCongruence", "CP.Connection.EvenElimination", "CP.Connection.EvenGram", "CP.Connection.EvenNative", "CP.Connection.OddFold", "CP.Connection.OddInverseFold", "CP.Connection.OddCandidate", "CP.Connection.OddNormalization", "CP.Connection.OddGram", "CP.Connection.OddConnection", "CP.Normalization.DiagonalBridge", "CP.Normalization.OddBorder", "CP.Normalization.Scalar", "CP.StageOne", "CP", "CP.Axioms"]
  Job.async do
    for mod in mods do
      let relative := mod.replace "." "/"
      let source := pkg.dir / (relative ++ ".lean")
      let output := pkg.buildDir / "lib" / "lean" / (relative ++ ".olean")
      if let some parent := output.parent then IO.FS.createDirAll parent
      let res ← IO.Process.output {
        cmd := (lakeEnv.lean.binDir / "lake").toString
        args := #["-f", (pkg.dir / "tools" / "frontend.lean").toString, "run", "check",
          source.toString, mod, output.toString]
        env := env }
      if !res.stdout.isEmpty then logInfo res.stdout
      if !res.stderr.isEmpty then logInfo res.stderr
      if res.exitCode != 0 then error s!"Lean checking failed: {mod}, exit {res.exitCode}"
      logInfo s!"kernel checked {mod}"

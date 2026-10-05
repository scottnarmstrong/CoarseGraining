module

public import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Kernel
public import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.SmoothRepresentative
public import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.WeakDerivComp
public import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.WeakDerivSmoothing
public import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Continuity
public import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.PointwiseBounds
public import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Convergence

/-!
# Convex-domain smoothing operator (aggregate re-export)

Previously a 3373-line monolithic module; now split along thematic boundaries
into the seven files imported above. This shim re-exports everything so
existing downstream consumers keep working unchanged.
-/

@[expose] public section

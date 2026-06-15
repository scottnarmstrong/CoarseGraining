import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Kernel
import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.SmoothRepresentative
import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.WeakDerivComp
import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.WeakDerivSmoothing
import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Continuity
import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.PointwiseBounds
import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Convergence

/-!
# Convex-domain smoothing operator (aggregate re-export)

Previously a 3373-line monolithic module; now split along thematic boundaries
into the seven files imported above. This shim re-exports everything so
existing downstream consumers keep working unchanged.
-/

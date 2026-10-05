import DaveyThesis2024.BasisDataIntegrity.PentagonTriangleFree
import DaveyThesis2024.BasisDataIntegrity.PentagonBlackIndep
import DaveyThesis2024.BasisDataIntegrity.PentagonAnchored
import DaveyThesis2024.BasisDataIntegrity.PentagonFirstBlack
import DaveyThesis2024.BasisDataIntegrity.SecAnchored
import DaveyThesis2024.BasisDataIntegrity.SecBipAnchored
import DaveyThesis2024.BasisDataIntegrity.SecColours

/-!
# Data-integrity regressions for the parsed flag bases

Each flag basis in this development is shipped as one long comma-separated hex
string literal and decoded at elaboration time.  Nothing downstream checks that
the decode is *faithful*: `AxiomCheck.lean` pins axiom names, and a basis is not
an axiom but a `def`.

On 2026-09-20 that gap bit.  The literals are wrapped across source lines, so the
token ending a line carried an embedded `'\n'`; `hexCharToNat` mapped it to `0`
but `parseHexStr` still applied `acc * 16`, shifting the packed integer left by
four bits.  **225** general-SEC, **117** pentagon-Q and **48** bipartite-SEC
entries decoded to a different flag than the generator emitted — and 104 of the
general ones carry a nonzero certificate coefficient.  The symptom was
misdiagnosed for most of a day as a falsity in the SEC locality axioms.

The theorems below pin, for each basis, a property that its **generator
guarantees by construction**.  They are `native_decide`, and any one of them
fails the moment the decode drifts again.  They were for a long time the most
expensive thing in the development; `reach8`'s closure chain was the reason,
and since that was replaced by a materialised set they are cheap.

See the development notes.

**Split 2026-10-05.** The seven checks now live one per module under
`BasisDataIntegrity/`, their shared definitions in `Common`, so that Lake
builds them concurrently rather than serially.  This module imports them and
remains the name every consumer uses; the checks themselves are unchanged.
-/

import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part1
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part3


/-!
# Blob-schedule and result-store blocks

Re-export of `BlobSchedule.Part1`–`Part3`. This was one 4,418-line module of 128 declarations, all
but a handful independent of each other, elaborated strictly in sequence.

Lean elaborates a module on essentially one core (this one measured 125% CPU) and Lake parallelises
only *across* modules, so a wide module is a serial segment of the build however independent its
contents are. The parts are cut only at boundaries no later declaration crosses -- including the
three `private theorem`s, which is what makes the cut set small -- so the parts do not depend on each
other and Lake runs them concurrently.

**Add new blocks to whichever part is smallest**, not to a new part named after a phase: the split is
a build-parallelism device, not a semantic grouping, and the parts must stay mutually independent. If
a new declaration needs one from another part, move them into the same part rather than importing
across.
-/

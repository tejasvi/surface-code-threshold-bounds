import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2636 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2636 = true := by
  decide +kernel

theorem tot2636 : totK PA10K2 A10K2.t2636 = [0, 0, 521496223102, 1840667073206, 1864884576983, 494174336536, 31222411477, 0, 0, 0] := by
  decide +kernel

theorem rows2637 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2637 = true := by
  decide +kernel

theorem tot2637 : totK PA10K2 A10K2.t2637 = [0, 0, 0, 707567720083, 2056631345277, 1577013342617, 379860345113, 25239774317, 0, 0] := by
  decide +kernel

theorem rows2638 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2638 = true := by
  decide +kernel

theorem tot2638 : totK PA10K2 A10K2.t2638 = [0, 0, 288959908659, 1231341700542, 1908267251345, 1064622120625, 179011815622, 5410721913, 0, 0] := by
  decide +kernel

theorem rows2639 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2639 = true := by
  decide +kernel

theorem tot2639 : totK PA10K2 A10K2.t2639 = [0, 0, 452531813626, 1771349948461, 1893831718671, 485557630077, 22043507873, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

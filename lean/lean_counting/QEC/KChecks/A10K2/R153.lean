import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows612 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t612 = true := by
  decide +kernel

theorem tot612 : totK PA10K2 A10K2.t612 = [0, 277626483571, 1052665551207, 1621304801384, 1326237206072, 357581902178, 31333686660, 0, 0, 0] := by
  decide +kernel

theorem rows613 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t613 = true := by
  decide +kernel

theorem tot613 : totK PA10K2 A10K2.t613 = [0, 447579769628, 1579231927442, 1834417311403, 644798933448, 52232171148, 0, 0, 0, 0] := by
  decide +kernel

theorem rows614 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t614 = true := by
  decide +kernel

theorem tot614 : totK PA10K2 A10K2.t614 = [0, 84682089283, 1179148818517, 2286132663121, 1048122524759, 87662614912, 0, 0, 0, 0] := by
  decide +kernel

theorem rows615 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t615 = true := by
  decide +kernel

theorem tot615 : totK PA10K2 A10K2.t615 = [0, 0, 508042328970, 1879982462096, 1846198762542, 459724730652, 26601763172, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

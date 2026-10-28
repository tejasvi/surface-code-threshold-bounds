import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2692 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2692 = true := by
  decide +kernel

theorem tot2692 : totK PA10K2 A10K2.t2692 = [0, 0, 480510875824, 1775101895674, 2085694077776, 755382488503, 55464635836, 0, 0, 0] := by
  decide +kernel

theorem rows2693 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2693 = true := by
  decide +kernel

theorem tot2693 : totK PA10K2 A10K2.t2693 = [0, 213371739588, 784082558162, 1558385793916, 1764488506433, 666271705946, 50889683698, 0, 0, 0] := by
  decide +kernel

theorem rows2694 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2694 = true := by
  decide +kernel

theorem tot2694 : totK PA10K2 A10K2.t2694 = [0, 442998173320, 1715088023805, 1958716978552, 555844961695, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2695 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2695 = true := by
  decide +kernel

theorem tot2695 : totK PA10K2 A10K2.t2695 = [0, 104635838397, 907335091120, 1943778826685, 1461392771839, 369525112805, 25371180993, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5140 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5140 = true := by
  decide +kernel

theorem tot5140 : totK PA10K2 A10K2.t5140 = [0, 450165197568, 1743078835814, 1995797494343, 588762264806, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5141 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5141 = true := by
  decide +kernel

theorem tot5141 : totK PA10K2 A10K2.t5141 = [0, 0, 673955539699, 2028859059866, 1640478712779, 360037145407, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows5142 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5142 = true := by
  decide +kernel

theorem tot5142 : totK PA10K2 A10K2.t5142 = [0, 269820170423, 1161283417201, 1888056637077, 1211649992600, 202951153390, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows5143 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5143 = true := by
  decide +kernel

theorem tot5143 : totK PA10K2 A10K2.t5143 = [0, 582523478866, 1910003000631, 1765370658521, 493886227946, 31941609474, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

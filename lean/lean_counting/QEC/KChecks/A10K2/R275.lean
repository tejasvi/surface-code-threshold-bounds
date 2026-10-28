import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1100 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1100 = true := by
  decide +kernel

theorem tot1100 : totK PA10K2 A10K2.t1100 = [0, 0, 0, 675366446968, 2189215783113, 1790736386074, 288731968587, 6066958478, 0, 0] := by
  decide +kernel

theorem rows1101 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1101 = true := by
  decide +kernel

theorem tot1101 : totK PA10K2 A10K2.t1101 = [0, 0, 132111021157, 645088613372, 1585630175800, 1828260985176, 673843212904, 55043167628, 0, 0] := by
  decide +kernel

theorem rows1102 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1102 = true := by
  decide +kernel

theorem tot1102 : totK PA10K2 A10K2.t1102 = [0, 0, 485507649260, 1842154793363, 1854108028951, 509511852188, 31362375073, 0, 0, 0] := by
  decide +kernel

theorem rows1103 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1103 = true := by
  decide +kernel

theorem tot1103 : totK PA10K2 A10K2.t1103 = [0, 0, 173008522523, 1110317440315, 2094011619998, 1331245605744, 264069399154, 12477124820, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

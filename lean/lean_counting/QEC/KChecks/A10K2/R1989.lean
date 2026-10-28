import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7956 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7956 = true := by
  decide +kernel

theorem tot7956 : totK PA10K2 A10K2.t7956 = [0, 0, 0, 598716725487, 2078705782321, 2030056643539, 477241487078, 18363904575, 0, 0] := by
  decide +kernel

theorem rows7957 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7957 = true := by
  decide +kernel

theorem tot7957 : totK PA10K2 A10K2.t7957 = [0, 0, 312139800791, 1099704175298, 1527206529692, 1362282923262, 550603198124, 50425690648, 0, 0] := by
  decide +kernel

theorem rows7958 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7958 = true := by
  decide +kernel

theorem tot7958 : totK PA10K2 A10K2.t7958 = [0, 0, 498402015416, 1872706422617, 2009102405393, 526964436672, 18752395928, 0, 0, 0] := by
  decide +kernel

theorem rows7959 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7959 = true := by
  decide +kernel

theorem tot7959 : totK PA10K2 A10K2.t7959 = [0, 0, 0, 511852277535, 1889082900681, 1844780441562, 431698399599, 18722998264, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

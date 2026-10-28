import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t404 = true := by
  decide +kernel

theorem tot404 : totK PD2M8K2 D2M8K2.t404 = [0, 209288779891, 497279099964, 180026860688, 5253830308, 0, 0, 0] := by
  decide +kernel

theorem rows405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t405 = true := by
  decide +kernel

theorem tot405 : totK PD2M8K2 D2M8K2.t405 = [0, 170971736763, 453371294704, 227493889983, 16891742343, 0, 0, 0] := by
  decide +kernel

theorem rows406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t406 = true := by
  decide +kernel

theorem tot406 : totK PD2M8K2 D2M8K2.t406 = [0, 67615601996, 366141892344, 361312834649, 58943233323, 1138244013, 0, 0] := by
  decide +kernel

theorem rows407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t407 = true := by
  decide +kernel

theorem tot407 : totK PD2M8K2 D2M8K2.t407 = [0, 90858976459, 413377750472, 348159038600, 32821770873, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

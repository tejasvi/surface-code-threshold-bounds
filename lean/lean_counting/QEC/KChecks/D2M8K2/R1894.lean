import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7576 = true := by
  decide +kernel

theorem tot7576 : totK PD2M8K2 D2M8K2.t7576 = [0, 0, 190081865690, 481782630416, 218343380654, 11056080877, 0, 0] := by
  decide +kernel

theorem rows7577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7577 = true := by
  decide +kernel

theorem tot7577 : totK PD2M8K2 D2M8K2.t7577 = [0, 0, 187268731162, 464131259726, 212342261907, 13144444366, 0, 0] := by
  decide +kernel

theorem rows7578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7578 = true := by
  decide +kernel

theorem tot7578 : totK PD2M8K2 D2M8K2.t7578 = [0, 0, 0, 322017132674, 462952676941, 73858919952, 1021600638, 0] := by
  decide +kernel

theorem rows7579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7579 = true := by
  decide +kernel

theorem tot7579 : totK PD2M8K2 D2M8K2.t7579 = [0, 0, 84568401081, 343763127051, 329440992583, 77397063712, 3552795014, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6704 = true := by
  decide +kernel

theorem tot6704 : totK PD2M8K2 D2M8K2.t6704 = [0, 0, 197911177528, 481577489038, 179870700323, 11780292382, 0, 0] := by
  decide +kernel

theorem rows6705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6705 = true := by
  decide +kernel

theorem tot6705 : totK PD2M8K2 D2M8K2.t6705 = [0, 169146838046, 448189478931, 258810647716, 23318574769, 0, 0, 0] := by
  decide +kernel

theorem rows6706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6706 = true := by
  decide +kernel

theorem tot6706 : totK PD2M8K2 D2M8K2.t6706 = [0, 179380481753, 468950389885, 237088690513, 14812093816, 0, 0, 0] := by
  decide +kernel

theorem rows6707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6707 = true := by
  decide +kernel

theorem tot6707 : totK PD2M8K2 D2M8K2.t6707 = [0, 51150016082, 302760876839, 421494337121, 85398910418, 1162740214, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

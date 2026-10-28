import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1300 = true := by
  decide +kernel

theorem tot1300 : totK PD2M8K2 D2M8K2.t1300 = [0, 136198339934, 440699532230, 284813824272, 20023055003, 0, 0, 0] := by
  decide +kernel

theorem rows1301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1301 = true := by
  decide +kernel

theorem tot1301 : totK PD2M8K2 D2M8K2.t1301 = [0, 0, 291248838256, 483628121113, 84286303403, 1239866073, 0, 0] := by
  decide +kernel

theorem rows1302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1302 = true := by
  decide +kernel

theorem tot1302 : totK PD2M8K2 D2M8K2.t1302 = [0, 160257584809, 432582843976, 290711899112, 32535457529, 0, 0, 0] := by
  decide +kernel

theorem rows1303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1303 = true := by
  decide +kernel

theorem tot1303 : totK PD2M8K2 D2M8K2.t1303 = [0, 206803920418, 481741193037, 209076579571, 11276447401, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1316 = true := by
  decide +kernel

theorem tot1316 : totK PD2M8K2 D2M8K2.t1316 = [0, 277049114955, 507928998894, 113000422790, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows1317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1317 = true := by
  decide +kernel

theorem tot1317 : totK PD2M8K2 D2M8K2.t1317 = [92456189417, 384455442889, 388757678611, 53697204301, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1318 = true := by
  decide +kernel

theorem tot1318 : totK PD2M8K2 D2M8K2.t1318 = [172285619028, 444018467100, 260363420690, 18997677889, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1319 = true := by
  decide +kernel

theorem tot1319 : totK PD2M8K2 D2M8K2.t1319 = [143011170461, 444579723479, 290072410601, 34490637066, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

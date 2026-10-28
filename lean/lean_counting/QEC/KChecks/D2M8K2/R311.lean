import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1244 = true := by
  decide +kernel

theorem tot1244 : totK PD2M8K2 D2M8K2.t1244 = [201490616930, 484503291632, 207692021458, 9852138406, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1245 = true := by
  decide +kernel

theorem tot1245 : totK PD2M8K2 D2M8K2.t1245 = [186479544730, 465450417467, 218187518554, 13765815827, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1246 = true := by
  decide +kernel

theorem tot1246 : totK PD2M8K2 D2M8K2.t1246 = [0, 279909853815, 502637716908, 110475381995, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows1247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1247 = true := by
  decide +kernel

theorem tot1247 : totK PD2M8K2 D2M8K2.t1247 = [91193102611, 378347868754, 387591990992, 55029587856, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

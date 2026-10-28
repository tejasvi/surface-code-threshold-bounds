import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12348 = true := by
  decide +kernel

theorem tot12348 : totK PD2M8K2 D2M8K2.t12348 = [0, 36086856404, 309413137677, 440411985168, 98559503717, 1369150432, 0, 0] := by
  decide +kernel

theorem rows12349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12349 = true := by
  decide +kernel

theorem tot12349 : totK PD2M8K2 D2M8K2.t12349 = [0, 65449163745, 358013072808, 427910707023, 52905997056, 0, 0, 0] := by
  decide +kernel

theorem rows12350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12350 = true := by
  decide +kernel

theorem tot12350 : totK PD2M8K2 D2M8K2.t12350 = [0, 177728297793, 475019727182, 243229118366, 13574233288, 0, 0, 0] := by
  decide +kernel

theorem rows12351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12351 = true := by
  decide +kernel

theorem tot12351 : totK PD2M8K2 D2M8K2.t12351 = [0, 162383651500, 451854814197, 248670566768, 15117888121, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

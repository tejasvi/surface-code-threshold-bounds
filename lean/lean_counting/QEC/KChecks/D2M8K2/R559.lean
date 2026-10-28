import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2236 = true := by
  decide +kernel

theorem tot2236 : totK PD2M8K2 D2M8K2.t2236 = [0, 110938415940, 424475841770, 320381622357, 31219907994, 0, 0, 0] := by
  decide +kernel

theorem rows2237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2237 = true := by
  decide +kernel

theorem tot2237 : totK PD2M8K2 D2M8K2.t2237 = [0, 0, 274772896556, 508215865893, 111817413086, 1369150432, 0, 0] := by
  decide +kernel

theorem rows2238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2238 = true := by
  decide +kernel

theorem tot2238 : totK PD2M8K2 D2M8K2.t2238 = [0, 177828434186, 421993892904, 280458944228, 34744435935, 0, 0, 0] := by
  decide +kernel

theorem rows2239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2239 = true := by
  decide +kernel

theorem tot2239 : totK PD2M8K2 D2M8K2.t2239 = [0, 174869889529, 454347903673, 245528722227, 18045717838, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

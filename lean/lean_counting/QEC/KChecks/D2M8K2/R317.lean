import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1268 = true := by
  decide +kernel

theorem tot1268 : totK PD2M8K2 D2M8K2.t1268 = [0, 182733705096, 482929147981, 235235013021, 12857772461, 0, 0, 0] := by
  decide +kernel

theorem rows1269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1269 = true := by
  decide +kernel

theorem tot1269 : totK PD2M8K2 D2M8K2.t1269 = [0, 193923232459, 467984322037, 213917085593, 12835581599, 0, 0, 0] := by
  decide +kernel

theorem rows1270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1270 = true := by
  decide +kernel

theorem tot1270 : totK PD2M8K2 D2M8K2.t1270 = [0, 172001413122, 449567985325, 264529007027, 23282239808, 0, 0, 0] := by
  decide +kernel

theorem rows1271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1271 = true := by
  decide +kernel

theorem tot1271 : totK PD2M8K2 D2M8K2.t1271 = [0, 92677389713, 412968114260, 329655750272, 42024899653, 1162935789, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

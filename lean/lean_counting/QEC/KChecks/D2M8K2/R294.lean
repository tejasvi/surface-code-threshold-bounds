import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1176 = true := by
  decide +kernel

theorem tot1176 : totK PD2M8K2 D2M8K2.t1176 = [0, 0, 178707584483, 474634391273, 222987557952, 15558513014, 0, 0] := by
  decide +kernel

theorem rows1177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1177 = true := by
  decide +kernel

theorem tot1177 : totK PD2M8K2 D2M8K2.t1177 = [0, 0, 0, 288359658958, 467191391018, 89950871824, 1095107716, 0] := by
  decide +kernel

theorem rows1178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1178 = true := by
  decide +kernel

theorem tot1178 : totK PD2M8K2 D2M8K2.t1178 = [92089433884, 200600565354, 67651063830, 140356815743, 283656239901, 100767384229, 3882006667, 0] := by
  decide +kernel

theorem rows1179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1179 = true := by
  decide +kernel

theorem tot1179 : totK PD2M8K2 D2M8K2.t1179 = [174081179172, 463938626759, 242642402555, 17115888737, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

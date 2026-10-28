import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10708 = true := by
  decide +kernel

theorem tot10708 : totK PD2M8K2 D2M8K2.t10708 = [0, 0, 12125719119, 309364495898, 496660921340, 62595215467, 1310166938, 0] := by
  decide +kernel

theorem rows10709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10709 = true := by
  decide +kernel

theorem tot10709 : totK PD2M8K2 D2M8K2.t10709 = [0, 0, 167600822007, 452253601943, 274110017566, 30470231449, 0, 0] := by
  decide +kernel

theorem rows10710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10710 = true := by
  decide +kernel

theorem tot10710 : totK PD2M8K2 D2M8K2.t10710 = [0, 0, 294911209665, 511988652186, 116794279596, 2795992786, 0, 0] := by
  decide +kernel

theorem rows10711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10711 = true := by
  decide +kernel

theorem tot10711 : totK PD2M8K2 D2M8K2.t10711 = [0, 0, 185864067230, 475039212238, 239444380883, 13896352198, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

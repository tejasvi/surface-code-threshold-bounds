import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3496 = true := by
  decide +kernel

theorem tot3496 : totK PD2M8K2 D2M8K2.t3496 = [0, 191634715650, 468235820123, 229452513403, 16104584588, 0, 0, 0] := by
  decide +kernel

theorem rows3497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3497 = true := by
  decide +kernel

theorem tot3497 : totK PD2M8K2 D2M8K2.t3497 = [0, 187814230645, 473425017033, 217971217941, 12183533023, 0, 0, 0] := by
  decide +kernel

theorem rows3498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3498 = true := by
  decide +kernel

theorem tot3498 : totK PD2M8K2 D2M8K2.t3498 = [0, 19230754378, 316560552266, 447907044558, 86107102407, 1162935789, 0, 0] := by
  decide +kernel

theorem rows3499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3499 = true := by
  decide +kernel

theorem tot3499 : totK PD2M8K2 D2M8K2.t3499 = [0, 0, 191695765624, 453757111413, 188887255145, 11853261585, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

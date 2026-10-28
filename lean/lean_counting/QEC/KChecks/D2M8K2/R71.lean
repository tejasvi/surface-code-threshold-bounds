import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t284 = true := by
  decide +kernel

theorem tot284 : totK PD2M8K2 D2M8K2.t284 = [169587715501, 466173049963, 238423836913, 17044607505, 0, 0, 0, 0] := by
  decide +kernel

theorem rows285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t285 = true := by
  decide +kernel

theorem tot285 : totK PD2M8K2 D2M8K2.t285 = [87762578873, 334577470919, 384882513364, 91308781315, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t286 = true := by
  decide +kernel

theorem tot286 : totK PD2M8K2 D2M8K2.t286 = [3757117624, 323928369955, 519994132255, 68149439601, 0, 0, 0, 0] := by
  decide +kernel

theorem rows287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t287 = true := by
  decide +kernel

theorem tot287 : totK PD2M8K2 D2M8K2.t287 = [196111917264, 466319282871, 229213565365, 19698721062, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10568 = true := by
  decide +kernel

theorem tot10568 : totK PD2M8K2 D2M8K2.t10568 = [0, 0, 279734057922, 507606879766, 101850141056, 1369150432, 0, 0] := by
  decide +kernel

theorem rows10569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10569 = true := by
  decide +kernel

theorem tot10569 : totK PD2M8K2 D2M8K2.t10569 = [0, 118279383133, 387225886368, 363813832362, 46689612120, 0, 0, 0] := by
  decide +kernel

theorem rows10570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10570 = true := by
  decide +kernel

theorem tot10570 : totK PD2M8K2 D2M8K2.t10570 = [0, 196164842085, 470866737591, 226927294458, 15615587506, 0, 0, 0] := by
  decide +kernel

theorem rows10571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10571 = true := by
  decide +kernel

theorem tot10571 : totK PD2M8K2 D2M8K2.t10571 = [0, 88962580889, 404004930234, 356624819007, 68034305243, 5921339170, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

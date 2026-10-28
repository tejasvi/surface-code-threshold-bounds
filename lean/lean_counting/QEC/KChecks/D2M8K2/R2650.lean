import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10600 = true := by
  decide +kernel

theorem tot10600 : totK PD2M8K2 D2M8K2.t10600 = [0, 0, 196485078903, 506340336108, 199671178944, 5430665091, 0, 0] := by
  decide +kernel

theorem rows10601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10601 = true := by
  decide +kernel

theorem tot10601 : totK PD2M8K2 D2M8K2.t10601 = [0, 175298174919, 410223763059, 229090912837, 89492767597, 5357615002, 0, 0] := by
  decide +kernel

theorem rows10602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10602 = true := by
  decide +kernel

theorem tot10602 : totK PD2M8K2 D2M8K2.t10602 = [0, 181087757825, 456935284247, 258212616471, 18340413387, 0, 0, 0] := by
  decide +kernel

theorem rows10603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10603 = true := by
  decide +kernel

theorem tot10603 : totK PD2M8K2 D2M8K2.t10603 = [0, 84801560820, 352996405475, 382380330595, 77605130883, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

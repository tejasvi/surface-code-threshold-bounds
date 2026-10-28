import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14128 = true := by
  decide +kernel

theorem tot14128 : totK PD2M8K2 D2M8K2.t14128 = [78750054095, 277371707210, 385712292637, 127402778674, 5883432551, 0, 0, 0] := by
  decide +kernel

theorem rows14129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14129 = true := by
  decide +kernel

theorem tot14129 : totK PD2M8K2 D2M8K2.t14129 = [161688051648, 478587281265, 238854203626, 11076864138, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14130 = true := by
  decide +kernel

theorem tot14130 : totK PD2M8K2 D2M8K2.t14130 = [84779694899, 340449314415, 387598787736, 80672651230, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows14131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14131 = true := by
  decide +kernel

theorem tot14131 : totK PD2M8K2 D2M8K2.t14131 = [0, 199778720855, 466416831070, 191834677329, 12052611869, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

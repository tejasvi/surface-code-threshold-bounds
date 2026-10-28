import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14084 = true := by
  decide +kernel

theorem tot14084 : totK PD2M8K2 D2M8K2.t14084 = [0, 0, 92050989887, 412043800387, 338483521921, 35889602169, 0, 0] := by
  decide +kernel

theorem rows14085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14085 = true := by
  decide +kernel

theorem tot14085 : totK PD2M8K2 D2M8K2.t14085 = [0, 18716352131, 8049921169, 276717177731, 465264975923, 107258613820, 1429815836, 0] := by
  decide +kernel

theorem rows14086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14086 = true := by
  decide +kernel

theorem tot14086 : totK PD2M8K2 D2M8K2.t14086 = [0, 202780988817, 499069440527, 196783987265, 5389245608, 0, 0, 0] := by
  decide +kernel

theorem rows14087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14087 = true := by
  decide +kernel

theorem tot14087 : totK PD2M8K2 D2M8K2.t14087 = [0, 121338005395, 432558543262, 326058784655, 25922447474, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

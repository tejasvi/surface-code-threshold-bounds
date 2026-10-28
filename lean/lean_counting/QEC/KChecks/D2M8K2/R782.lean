import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3128 = true := by
  decide +kernel

theorem tot3128 : totK PD2M8K2 D2M8K2.t3128 = [0, 205867437035, 480937874640, 210438425386, 12208674056, 0, 0, 0] := by
  decide +kernel

theorem rows3129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3129 = true := by
  decide +kernel

theorem tot3129 : totK PD2M8K2 D2M8K2.t3129 = [64441704225, 235608329082, 415715871862, 190483482131, 8214505460, 0, 0, 0] := by
  decide +kernel

theorem rows3130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3130 = true := by
  decide +kernel

theorem tot3130 : totK PD2M8K2 D2M8K2.t3130 = [164845409836, 443409960555, 283330698169, 30384465093, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3131 = true := by
  decide +kernel

theorem tot3131 : totK PD2M8K2 D2M8K2.t3131 = [117630249627, 434906652137, 334955222526, 36028880743, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

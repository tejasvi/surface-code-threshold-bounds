import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10456 = true := by
  decide +kernel

theorem tot10456 : totK PD2M8K2 D2M8K2.t10456 = [0, 0, 214332392419, 492811047932, 197045423798, 10959267139, 0, 0] := by
  decide +kernel

theorem rows10457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10457 = true := by
  decide +kernel

theorem tot10457 : totK PD2M8K2 D2M8K2.t10457 = [0, 0, 69665160969, 355989666115, 369974631929, 112861783244, 8332571741, 0] := by
  decide +kernel

theorem rows10458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10458 = true := by
  decide +kernel

theorem tot10458 : totK PD2M8K2 D2M8K2.t10458 = [0, 0, 0, 251073829343, 497723323416, 150113587474, 4002076922, 0] := by
  decide +kernel

theorem rows10459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10459 = true := by
  decide +kernel

theorem tot10459 : totK PD2M8K2 D2M8K2.t10459 = [0, 0, 162798423720, 432479350460, 254211463121, 52882438900, 1409560813, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

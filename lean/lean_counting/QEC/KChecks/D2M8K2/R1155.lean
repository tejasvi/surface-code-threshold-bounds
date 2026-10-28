import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4620 = true := by
  decide +kernel

theorem tot4620 : totK PD2M8K2 D2M8K2.t4620 = [0, 0, 175097542693, 476926667129, 235306049421, 13892541144, 0, 0] := by
  decide +kernel

theorem rows4621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4621 = true := by
  decide +kernel

theorem tot4621 : totK PD2M8K2 D2M8K2.t4621 = [0, 0, 0, 276124718453, 513897850540, 100682341152, 1096505104, 0] := by
  decide +kernel

theorem rows4622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4622 = true := by
  decide +kernel

theorem tot4622 : totK PD2M8K2 D2M8K2.t4622 = [0, 0, 0, 220339702183, 496062566443, 161837514796, 5253830308, 0] := by
  decide +kernel

theorem rows4623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4623 = true := by
  decide +kernel

theorem tot4623 : totK PD2M8K2 D2M8K2.t4623 = [0, 0, 0, 232246214022, 468257175851, 159784153398, 4411932323, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

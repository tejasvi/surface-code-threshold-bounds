import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15508 = true := by
  decide +kernel

theorem tot15508 : totK PD2M8K2 D2M8K2.t15508 = [0, 175831994962, 464989109741, 231879363602, 14970842807, 0, 0, 0] := by
  decide +kernel

theorem rows15509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15509 = true := by
  decide +kernel

theorem tot15509 : totK PD2M8K2 D2M8K2.t15509 = [0, 87312756727, 333637278204, 390757757690, 86937844550, 1164319620, 0, 0] := by
  decide +kernel

theorem rows15510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15510 = true := by
  decide +kernel

theorem tot15510 : totK PD2M8K2 D2M8K2.t15510 = [0, 0, 223671786802, 478578221450, 166378022677, 9404247146, 0, 0] := by
  decide +kernel

theorem rows15511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15511 = true := by
  decide +kernel

theorem tot15511 : totK PD2M8K2 D2M8K2.t15511 = [0, 158739087997, 415159617393, 268475065816, 53478759070, 2481160468, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

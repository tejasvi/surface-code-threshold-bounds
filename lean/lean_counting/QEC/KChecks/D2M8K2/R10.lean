import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows40 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t40 = true := by
  decide +kernel

theorem tot40 : totK PD2M8K2 D2M8K2.t40 = [86934566719, 278523224904, 353748565501, 168368011039, 8200183796, 0, 0, 0] := by
  decide +kernel

theorem rows41 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t41 = true := by
  decide +kernel

theorem tot41 : totK PD2M8K2 D2M8K2.t41 = [177383499198, 458928978611, 262639437245, 25569020375, 0, 0, 0, 0] := by
  decide +kernel

theorem rows42 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t42 = true := by
  decide +kernel

theorem tot42 : totK PD2M8K2 D2M8K2.t42 = [175199088287, 470839733739, 246943168761, 12723413330, 0, 0, 0, 0] := by
  decide +kernel

theorem rows43 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t43 = true := by
  decide +kernel

theorem tot43 : totK PD2M8K2 D2M8K2.t43 = [0, 261413474801, 516688155602, 121490613044, 1164319620, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

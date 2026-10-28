import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3080 = true := by
  decide +kernel

theorem tot3080 : totK PD2M8K2 D2M8K2.t3080 = [0, 205348107480, 465532496278, 211088517943, 14070418698, 0, 0, 0] := by
  decide +kernel

theorem rows3081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3081 = true := by
  decide +kernel

theorem tot3081 : totK PD2M8K2 D2M8K2.t3081 = [0, 0, 286983537994, 491062507183, 100854869317, 1369150432, 0, 0] := by
  decide +kernel

theorem rows3082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3082 = true := by
  decide +kernel

theorem tot3082 : totK PD2M8K2 D2M8K2.t3082 = [0, 92930711933, 382461954587, 398190702896, 52034975108, 0, 0, 0] := by
  decide +kernel

theorem rows3083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3083 = true := by
  decide +kernel

theorem tot3083 : totK PD2M8K2 D2M8K2.t3083 = [0, 168224478426, 450881629626, 269681306648, 19743537694, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

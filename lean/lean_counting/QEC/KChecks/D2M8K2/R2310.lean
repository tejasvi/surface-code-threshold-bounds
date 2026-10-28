import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9240 = true := by
  decide +kernel

theorem tot9240 : totK PD2M8K2 D2M8K2.t9240 = [0, 185132913947, 463712851626, 207399797402, 10735115630, 0, 0, 0] := by
  decide +kernel

theorem rows9241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9241 = true := by
  decide +kernel

theorem tot9241 : totK PD2M8K2 D2M8K2.t9241 = [0, 67220493622, 337225722055, 374950268698, 69871818269, 1206465782, 0, 0] := by
  decide +kernel

theorem rows9242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9242 = true := by
  decide +kernel

theorem tot9242 : totK PD2M8K2 D2M8K2.t9242 = [0, 74326172861, 381719617584, 383228982428, 38217878931, 0, 0, 0] := by
  decide +kernel

theorem rows9243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9243 = true := by
  decide +kernel

theorem tot9243 : totK PD2M8K2 D2M8K2.t9243 = [0, 175055214907, 441709615973, 268413773656, 29185162439, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

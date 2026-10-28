import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11192 = true := by
  decide +kernel

theorem tot11192 : totK PD2M8K2 D2M8K2.t11192 = [0, 0, 256152849325, 492550084001, 140515094089, 8404294179, 0, 0] := by
  decide +kernel

theorem rows11193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11193 = true := by
  decide +kernel

theorem tot11193 : totK PD2M8K2 D2M8K2.t11193 = [0, 142048566188, 370360793098, 294796681609, 75718242399, 3581949829, 0, 0] := by
  decide +kernel

theorem rows11194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11194 = true := by
  decide +kernel

theorem tot11194 : totK PD2M8K2 D2M8K2.t11194 = [0, 175054441229, 443605393942, 269380427909, 27599670954, 0, 0, 0] := by
  decide +kernel

theorem rows11195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11195 = true := by
  decide +kernel

theorem tot11195 : totK PD2M8K2 D2M8K2.t11195 = [0, 121331409557, 441556062281, 311653372466, 26503335942, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

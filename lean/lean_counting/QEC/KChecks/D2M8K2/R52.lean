import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t208 = true := by
  decide +kernel

theorem tot208 : totK PD2M8K2 D2M8K2.t208 = [0, 170547707277, 456630458271, 242130797954, 15124186524, 0, 0, 0] := by
  decide +kernel

theorem rows209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t209 = true := by
  decide +kernel

theorem tot209 : totK PD2M8K2 D2M8K2.t209 = [0, 0, 275120660193, 500455439598, 111717760391, 1369150432, 0, 0] := by
  decide +kernel

theorem rows210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t210 = true := by
  decide +kernel

theorem tot210 : totK PD2M8K2 D2M8K2.t210 = [0, 84457201172, 365248286599, 406823894286, 54993028473, 0, 0, 0] := by
  decide +kernel

theorem rows211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t211 = true := by
  decide +kernel

theorem tot211 : totK PD2M8K2 D2M8K2.t211 = [0, 187076699610, 477815974131, 220350114283, 12287346641, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

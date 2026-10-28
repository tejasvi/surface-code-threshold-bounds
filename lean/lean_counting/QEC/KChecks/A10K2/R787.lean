import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3148 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3148 = true := by
  decide +kernel

theorem tot3148 : totK PA10K2 A10K2.t3148 = [0, 0, 510380714468, 1873778932059, 2006718455466, 589740967223, 24424400320, 0, 0, 0] := by
  decide +kernel

theorem rows3149 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3149 = true := by
  decide +kernel

theorem tot3149 : totK PA10K2 A10K2.t3149 = [0, 0, 0, 601860879843, 1993536435136, 1782807588598, 386966830983, 12696458652, 0, 0] := by
  decide +kernel

theorem rows3150 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3150 = true := by
  decide +kernel

theorem tot3150 : totK PA10K2 A10K2.t3150 = [0, 0, 371048058949, 1446707065278, 1998564752949, 1041773046115, 113534911110, 0, 0, 0] := by
  decide +kernel

theorem rows3151 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3151 = true := by
  decide +kernel

theorem tot3151 : totK PA10K2 A10K2.t3151 = [0, 0, 324403451983, 1611713058906, 2143512502727, 790106163230, 51598899319, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

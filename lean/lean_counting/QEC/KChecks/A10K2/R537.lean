import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2148 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2148 = true := by
  decide +kernel

theorem tot2148 : totK PA10K2 A10K2.t2148 = [0, 349232232612, 1701280816376, 2114744365963, 619587779905, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2149 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2149 = true := by
  decide +kernel

theorem tot2149 : totK PA10K2 A10K2.t2149 = [0, 15638348816, 443914959881, 1776561808638, 1883865668010, 494742093143, 30818366867, 0, 0, 0] := by
  decide +kernel

theorem rows2150 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2150 = true := by
  decide +kernel

theorem tot2150 : totK PA10K2 A10K2.t2150 = [0, 525732102641, 1756154564934, 1794883488378, 592889735402, 51464731716, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2151 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2151 = true := by
  decide +kernel

theorem tot2151 : totK PA10K2 A10K2.t2151 = [0, 195423599008, 1383485720939, 2184169611486, 883730439488, 66528807994, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

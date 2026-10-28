import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6316 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6316 = true := by
  decide +kernel

theorem tot6316 : totK PA10K2 A10K2.t6316 = [0, 512663351037, 1707305638716, 1762362871272, 572025408700, 57314907261, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6317 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6317 = true := by
  decide +kernel

theorem tot6317 : totK PA10K2 A10K2.t6317 = [0, 170294200681, 1279430691098, 2142156278869, 906775970099, 57588849937, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6318 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6318 = true := by
  decide +kernel

theorem tot6318 : totK PA10K2 A10K2.t6318 = [0, 477186712153, 1531421345574, 1773816629636, 945094021696, 170007653542, 6239673734, 0, 0, 0] := by
  decide +kernel

theorem rows6319 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6319 = true := by
  decide +kernel

theorem tot6319 : totK PA10K2 A10K2.t6319 = [0, 310203719009, 1537084042318, 2221839382035, 872826600493, 50664170179, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

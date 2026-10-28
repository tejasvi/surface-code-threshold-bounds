import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4732 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4732 = true := by
  decide +kernel

theorem tot4732 : totK PA10K2 A10K2.t4732 = [0, 471427080793, 1732518520348, 1951962203877, 645759808731, 51794973690, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4733 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4733 = true := by
  decide +kernel

theorem tot4733 : totK PA10K2 A10K2.t4733 = [0, 196642455102, 1377686684566, 2253558017231, 926716585818, 66908530098, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4734 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4734 = true := by
  decide +kernel

theorem tot4734 : totK PA10K2 A10K2.t4734 = [0, 0, 555839155400, 1951435711834, 1745580555198, 436794466026, 26630104451, 0, 0, 0] := by
  decide +kernel

theorem rows4735 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4735 = true := by
  decide +kernel

theorem tot4735 : totK PA10K2 A10K2.t4735 = [0, 0, 498735959325, 1856404977815, 2002487128925, 497290475104, 17742097974, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

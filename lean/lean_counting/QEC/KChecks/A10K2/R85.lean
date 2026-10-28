import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows340 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t340 = true := by
  decide +kernel

theorem tot340 : totK PA10K2 A10K2.t340 = [0, 0, 293929698888, 1153592718598, 1920650442023, 1313575828325, 244845776545, 6853348008, 0, 0] := by
  decide +kernel

theorem rows341 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t341 = true := by
  decide +kernel

theorem tot341 : totK PA10K2 A10K2.t341 = [0, 0, 470832198529, 1810531336460, 1915287099486, 546448905274, 32846095359, 0, 0, 0] := by
  decide +kernel

theorem rows342 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t342 = true := by
  decide +kernel

theorem tot342 : totK PA10K2 A10K2.t342 = [0, 0, 457163289862, 1711105926749, 1901622857177, 559873218362, 36819311980, 0, 0, 0] := by
  decide +kernel

theorem rows343 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t343 = true := by
  decide +kernel

theorem tot343 : totK PA10K2 A10K2.t343 = [0, 0, 76775629829, 1179409565145, 2325391594678, 1015586004935, 81424914102, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

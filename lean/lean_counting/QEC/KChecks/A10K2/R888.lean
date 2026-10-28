import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3552 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3552 = true := by
  decide +kernel

theorem tot3552 : totK PA10K2 A10K2.t3552 = [0, 0, 0, 502759651733, 1838382712380, 1965190290590, 686811234215, 60273215816, 0, 0] := by
  decide +kernel

theorem rows3553 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3553 = true := by
  decide +kernel

theorem tot3553 : totK PA10K2 A10K2.t3553 = [0, 0, 0, 477374279115, 1817643913167, 2015053208343, 587634725425, 22985814360, 0, 0] := by
  decide +kernel

theorem rows3554 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3554 = true := by
  decide +kernel

theorem tot3554 : totK PA10K2 A10K2.t3554 = [0, 0, 0, 0, 774276524087, 2241411891667, 1623618728350, 274358574682, 7047025452, 0] := by
  decide +kernel

theorem rows3555 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3555 = true := by
  decide +kernel

theorem tot3555 : totK PA10K2 A10K2.t3555 = [0, 0, 0, 539312721908, 1877843166362, 1914174874879, 662700586756, 56316064646, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

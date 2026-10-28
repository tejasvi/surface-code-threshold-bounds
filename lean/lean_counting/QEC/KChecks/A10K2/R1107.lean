import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4428 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4428 = true := by
  decide +kernel

theorem tot4428 : totK PA10K2 A10K2.t4428 = [0, 0, 397662082205, 1646227186191, 2050545572027, 767017633130, 69440933453, 0, 0, 0] := by
  decide +kernel

theorem rows4429 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4429 = true := by
  decide +kernel

theorem tot4429 : totK PA10K2 A10K2.t4429 = [0, 0, 525321569206, 1909320032220, 1902549284649, 466693645471, 17742097974, 0, 0, 0] := by
  decide +kernel

theorem rows4430 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4430 = true := by
  decide +kernel

theorem tot4430 : totK PA10K2 A10K2.t4430 = [0, 0, 0, 648404650958, 2027867234717, 1594667324416, 378615558626, 25239774317, 0, 0] := by
  decide +kernel

theorem rows4431 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4431 = true := by
  decide +kernel

theorem tot4431 : totK PA10K2 A10K2.t4431 = [0, 0, 289478139766, 1313458794094, 1909383664045, 1055252215623, 173424058326, 5410721913, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

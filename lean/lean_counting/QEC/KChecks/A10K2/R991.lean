import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3964 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3964 = true := by
  decide +kernel

theorem tot3964 : totK PA10K2 A10K2.t3964 = [0, 0, 320479959089, 1095842431830, 1563915726007, 1388317769715, 522144482857, 48886019071, 0, 0] := by
  decide +kernel

theorem rows3965 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3965 = true := by
  decide +kernel

theorem tot3965 : totK PA10K2 A10K2.t3965 = [0, 0, 456759784504, 1766226929987, 1969225367543, 570884751827, 32731286466, 0, 0, 0] := by
  decide +kernel

theorem rows3966 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3966 = true := by
  decide +kernel

theorem tot3966 : totK PA10K2 A10K2.t3966 = [0, 0, 84169918459, 866708160872, 2053582234294, 1536787175211, 363272824737, 25734533292, 0, 0] := by
  decide +kernel

theorem rows3967 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3967 = true := by
  decide +kernel

theorem tot3967 : totK PA10K2 A10K2.t3967 = [0, 0, 85721494493, 846228314334, 2061184837903, 1517772190264, 257061089258, 6034215561, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

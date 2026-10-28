import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4036 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4036 = true := by
  decide +kernel

theorem tot4036 : totK PA10K2 A10K2.t4036 = [0, 0, 119103332128, 924450961698, 2138376454301, 1519431442207, 253504727630, 7047025452, 0, 0] := by
  decide +kernel

theorem rows4037 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4037 = true := by
  decide +kernel

theorem tot4037 : totK PA10K2 A10K2.t4037 = [0, 0, 277872468536, 1467965796816, 2156304339756, 941121925610, 91752704065, 0, 0, 0] := by
  decide +kernel

theorem rows4038 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4038 = true := by
  decide +kernel

theorem tot4038 : totK PA10K2 A10K2.t4038 = [0, 0, 614163989865, 2029890255400, 1921639388329, 446174032769, 11925330097, 0, 0, 0] := by
  decide +kernel

theorem rows4039 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4039 = true := by
  decide +kernel

theorem tot4039 : totK PA10K2 A10K2.t4039 = [0, 0, 0, 748050558842, 2215564882359, 1666500016228, 256641719044, 6066958478, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

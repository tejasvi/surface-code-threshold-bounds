import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4800 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4800 = true := by
  decide +kernel

theorem tot4800 : totK PA10K2 A10K2.t4800 = [0, 0, 453041834173, 1609541500841, 1941365827242, 783478934804, 75643137603, 0, 0, 0] := by
  decide +kernel

theorem rows4801 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4801 = true := by
  decide +kernel

theorem tot4801 : totK PA10K2 A10K2.t4801 = [0, 0, 389569462447, 1724543580445, 2089845843164, 652594840958, 40353100526, 0, 0, 0] := by
  decide +kernel

theorem rows4802 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4802 = true := by
  decide +kernel

theorem tot4802 : totK PA10K2 A10K2.t4802 = [0, 0, 0, 494043518915, 1868123566341, 1761806613172, 423183790501, 25565504801, 0, 0] := by
  decide +kernel

theorem rows4803 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4803 = true := by
  decide +kernel

theorem tot4803 : totK PA10K2 A10K2.t4803 = [0, 0, 401404787705, 1586676587695, 1919716866374, 824376088764, 138122309559, 5517381808, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3804 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3804 = true := by
  decide +kernel

theorem tot3804 : totK PA10K2 A10K2.t3804 = [0, 0, 0, 795149397344, 2424337849868, 1749993135272, 230392006638, 0, 0, 0] := by
  decide +kernel

theorem rows3805 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3805 = true := by
  decide +kernel

theorem tot3805 : totK PA10K2 A10K2.t3805 = [0, 0, 0, 516293566528, 1845210300321, 1996344958710, 652052733097, 42874818239, 0, 0] := by
  decide +kernel

theorem rows3806 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3806 = true := by
  decide +kernel

theorem tot3806 : totK PA10K2 A10K2.t3806 = [0, 0, 0, 572474305319, 1908854637601, 1929640947273, 526838346948, 31712524204, 0, 0] := by
  decide +kernel

theorem rows3807 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3807 = true := by
  decide +kernel

theorem tot3807 : totK PA10K2 A10K2.t3807 = [0, 0, 0, 31645740394, 980038182921, 2279913988246, 1424030390066, 246069329280, 7047025452, 0] := by
  decide +kernel

end QECKChecks.A10K2

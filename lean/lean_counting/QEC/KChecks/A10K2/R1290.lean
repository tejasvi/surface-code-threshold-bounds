import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5160 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5160 = true := by
  decide +kernel

theorem tot5160 : totK PA10K2 A10K2.t5160 = [0, 0, 484250775997, 1588576555869, 1687923252420, 826123220014, 148006544155, 5718040558, 0, 0] := by
  decide +kernel

theorem rows5161 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5161 = true := by
  decide +kernel

theorem tot5161 : totK PA10K2 A10K2.t5161 = [0, 0, 295075171265, 1585887426408, 2108606670966, 685595372491, 52620953014, 0, 0, 0] := by
  decide +kernel

theorem rows5162 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5162 = true := by
  decide +kernel

theorem tot5162 : totK PA10K2 A10K2.t5162 = [0, 0, 112562677656, 800359112292, 2058040324609, 1440001485542, 248025820968, 6354482628, 0, 0] := by
  decide +kernel

theorem rows5163 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5163 = true := by
  decide +kernel

theorem tot5163 : totK PA10K2 A10K2.t5163 = [0, 0, 490143787262, 1846308075675, 2004177947621, 583109900192, 32873769222, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1624 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1624 = true := by
  decide +kernel

theorem tot1624 : totK PA10K2 A10K2.t1624 = [0, 0, 440716416725, 1839884117991, 2161225143489, 647236212309, 33001472292, 0, 0, 0] := by
  decide +kernel

theorem rows1625 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1625 = true := by
  decide +kernel

theorem tot1625 : totK PA10K2 A10K2.t1625 = [0, 0, 110501856496, 818609614426, 2110294547603, 1740250728244, 308066617695, 6962742351, 0, 0] := by
  decide +kernel

theorem rows1626 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1626 = true := by
  decide +kernel

theorem tot1626 : totK PA10K2 A10K2.t1626 = [0, 0, 449431065226, 1823820363474, 1981794582593, 500445894899, 32040661968, 0, 0, 0] := by
  decide +kernel

theorem rows1627 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1627 = true := by
  decide +kernel

theorem tot1627 : totK PA10K2 A10K2.t1627 = [0, 0, 214052912247, 1070688383535, 1974759381742, 1233819618717, 186592021359, 5460492893, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6744 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6744 = true := by
  decide +kernel

theorem tot6744 : totK PA10K2 A10K2.t6744 = [0, 437626163529, 1703688109587, 2096421581316, 747451763528, 56143165367, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6745 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6745 = true := by
  decide +kernel

theorem tot6745 : totK PA10K2 A10K2.t6745 = [0, 476571136429, 1878907129535, 2064015755335, 590590282507, 31433748018, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6746 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6746 = true := by
  decide +kernel

theorem tot6746 : totK PA10K2 A10K2.t6746 = [0, 0, 704592386071, 2204216145473, 1748256898670, 296025711726, 6904928264, 0, 0, 0] := by
  decide +kernel

theorem rows6747 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6747 = true := by
  decide +kernel

theorem tot6747 : totK PA10K2 A10K2.t6747 = [0, 526229009387, 1836941395753, 1876455766771, 545311275341, 45945795436, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

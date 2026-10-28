import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows756 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t756 = true := by
  decide +kernel

theorem tot756 : totK PA10K2 A10K2.t756 = [0, 526951148883, 1972136936453, 1988416703077, 463554782479, 13816090359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows757 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t757 = true := by
  decide +kernel

theorem tot757 : totK PA10K2 A10K2.t757 = [0, 529073677447, 1860256897479, 1957932490478, 623226010135, 49180423016, 0, 0, 0, 0] := by
  decide +kernel

theorem rows758 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t758 = true := by
  decide +kernel

theorem tot758 : totK PA10K2 A10K2.t758 = [0, 494118494401, 1799769905149, 1968039017066, 614133829699, 37876052273, 0, 0, 0, 0] := by
  decide +kernel

theorem rows759 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t759 = true := by
  decide +kernel

theorem tot759 : totK PA10K2 A10K2.t759 = [0, 0, 768763336553, 2218428916970, 1586107347686, 273120838901, 6904928264, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

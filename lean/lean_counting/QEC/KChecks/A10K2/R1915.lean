import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7660 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7660 = true := by
  decide +kernel

theorem tot7660 : totK PA10K2 A10K2.t7660 = [0, 0, 511028321977, 1801567555135, 1848181531981, 616528682188, 255591728650, 98306063394, 6354482628, 0] := by
  decide +kernel

theorem rows7661 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7661 = true := by
  decide +kernel

theorem tot7661 : totK PA10K2 A10K2.t7661 = [0, 0, 202041260899, 1091803402079, 2090439984044, 1460056213163, 263601591762, 7237400819, 0, 0] := by
  decide +kernel

theorem rows7662 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7662 = true := by
  decide +kernel

theorem tot7662 : totK PA10K2 A10K2.t7662 = [0, 0, 526633700582, 1874957049684, 1989952867957, 553038031861, 32780555804, 0, 0, 0] := by
  decide +kernel

theorem rows7663 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7663 = true := by
  decide +kernel

theorem tot7663 : totK PA10K2 A10K2.t7663 = [0, 0, 84539485306, 893857761407, 2066185654525, 1538411384124, 360146086194, 20328650499, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

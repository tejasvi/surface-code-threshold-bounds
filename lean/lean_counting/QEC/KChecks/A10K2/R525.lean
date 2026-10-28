import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2100 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2100 = true := by
  decide +kernel

theorem tot2100 : totK PA10K2 A10K2.t2100 = [0, 0, 574550352975, 1890944001169, 1757545436325, 441288855955, 30953568651, 0, 0, 0] := by
  decide +kernel

theorem rows2101 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2101 = true := by
  decide +kernel

theorem tot2101 : totK PA10K2 A10K2.t2101 = [0, 0, 0, 1060978491181, 2397528556365, 957427796626, 69709429330, 0, 0, 0] := by
  decide +kernel

theorem rows2102 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2102 = true := by
  decide +kernel

theorem tot2102 : totK PA10K2 A10K2.t2102 = [0, 476537513919, 1557695401991, 1471675861025, 705547852415, 559887475687, 144939828619, 6239673734, 0, 0] := by
  decide +kernel

theorem rows2103 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2103 = true := by
  decide +kernel

theorem tot2103 : totK PA10K2 A10K2.t2103 = [0, 126820056085, 983246746046, 2172900178610, 1520133473105, 268231336042, 7007974415, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

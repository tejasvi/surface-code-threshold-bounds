import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2712 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2712 = true := by
  decide +kernel

theorem tot2712 : totK PA10K2 A10K2.t2712 = [0, 218175288971, 1389349386855, 2381257044861, 1048083013416, 89766322223, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2713 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2713 = true := by
  decide +kernel

theorem tot2713 : totK PA10K2 A10K2.t2713 = [0, 0, 525769247266, 1987024251773, 2028728716888, 453983968679, 12926121504, 0, 0, 0] := by
  decide +kernel

theorem rows2714 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2714 = true := by
  decide +kernel

theorem tot2714 : totK PA10K2 A10K2.t2714 = [0, 0, 502246750619, 1838263290042, 1915487422252, 525850542625, 32523532663, 0, 0, 0] := by
  decide +kernel

theorem rows2715 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2715 = true := by
  decide +kernel

theorem tot2715 : totK PA10K2 A10K2.t2715 = [0, 0, 0, 743380078168, 2129262939162, 1440915936847, 310041162211, 25130442608, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

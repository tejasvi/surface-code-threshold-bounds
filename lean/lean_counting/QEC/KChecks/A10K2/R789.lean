import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3156 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3156 = true := by
  decide +kernel

theorem tot3156 : totK PA10K2 A10K2.t3156 = [0, 0, 0, 115836153831, 1010569170071, 2186918316870, 1353113602044, 206264911768, 6860445330, 0] := by
  decide +kernel

theorem rows3157 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3157 = true := by
  decide +kernel

theorem tot3157 : totK PA10K2 A10K2.t3157 = [0, 0, 0, 691558974931, 1976080581914, 1721375162136, 496197301437, 35686968434, 0, 0] := by
  decide +kernel

theorem rows3158 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3158 = true := by
  decide +kernel

theorem tot3158 : totK PA10K2 A10K2.t3158 = [0, 0, 0, 485275095432, 1919091344561, 2072521916419, 501757066539, 18214947114, 0, 0] := by
  decide +kernel

theorem rows3159 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3159 = true := by
  decide +kernel

theorem tot3159 : totK PA10K2 A10K2.t3159 = [0, 0, 289498769530, 1052329725235, 1564401097100, 1336013856158, 542160605960, 50432252117, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

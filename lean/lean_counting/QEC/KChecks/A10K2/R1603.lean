import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6412 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6412 = true := by
  decide +kernel

theorem tot6412 : totK PA10K2 A10K2.t6412 = [319364795913, 1480072971157, 2210009948077, 1088427510077, 118614283813, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6413 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6413 = true := by
  decide +kernel

theorem tot6413 : totK PA10K2 A10K2.t6413 = [0, 613592017148, 2068528802762, 1962110119801, 436250239101, 13814447077, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6414 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6414 = true := by
  decide +kernel

theorem tot6414 : totK PA10K2 A10K2.t6414 = [0, 342927725388, 1519537993896, 2074026088271, 852518608825, 75643137603, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6415 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6415 = true := by
  decide +kernel

theorem tot6415 : totK PA10K2 A10K2.t6415 = [0, 494875039619, 1852625631894, 2005885911320, 509202695767, 12917769548, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

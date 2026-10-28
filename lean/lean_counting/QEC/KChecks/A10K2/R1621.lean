import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6484 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6484 = true := by
  decide +kernel

theorem tot6484 : totK PA10K2 A10K2.t6484 = [0, 545065850185, 1844592479327, 1908579850738, 666354822804, 120349994436, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows6485 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6485 = true := by
  decide +kernel

theorem tot6485 : totK PA10K2 A10K2.t6485 = [0, 226651756384, 1306943159186, 2130144399597, 1256483383131, 191568153613, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6486 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6486 = true := by
  decide +kernel

theorem tot6486 : totK PA10K2 A10K2.t6486 = [0, 0, 536623895348, 1990362423248, 2012632986509, 462672503988, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows6487 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6487 = true := by
  decide +kernel

theorem tot6487 : totK PA10K2 A10K2.t6487 = [0, 0, 501691475976, 1715304082807, 1878787976834, 697052614480, 67056365660, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

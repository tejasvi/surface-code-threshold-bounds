import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7508 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7508 = true := by
  decide +kernel

theorem tot7508 : totK PA10K2 A10K2.t7508 = [0, 403451872644, 1744451973999, 2009946952526, 585161070732, 32877822373, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7509 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7509 = true := by
  decide +kernel

theorem tot7509 : totK PA10K2 A10K2.t7509 = [0, 0, 709621574010, 2202563504765, 1554138495061, 199370766224, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7510 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7510 = true := by
  decide +kernel

theorem tot7510 : totK PA10K2 A10K2.t7510 = [0, 595155796918, 1969031640994, 1880370696634, 579322942200, 94343156554, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows7511 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7511 = true := by
  decide +kernel

theorem tot7511 : totK PA10K2 A10K2.t7511 = [0, 0, 755461098979, 2258751877023, 1750595897652, 306698759773, 6962742351, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

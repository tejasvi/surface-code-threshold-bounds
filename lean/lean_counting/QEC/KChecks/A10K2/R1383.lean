import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5532 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5532 = true := by
  decide +kernel

theorem tot5532 : totK PA10K2 A10K2.t5532 = [0, 455158572719, 1775292990650, 2069835669244, 627078400533, 42110881917, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5533 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5533 = true := by
  decide +kernel

theorem tot5533 : totK PA10K2 A10K2.t5533 = [0, 187646630977, 1178761720478, 2108692968560, 1290193798133, 230122121219, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows5534 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5534 = true := by
  decide +kernel

theorem tot5534 : totK PA10K2 A10K2.t5534 = [0, 0, 611149302810, 2127270354765, 1965254019696, 369831824166, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows5535 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5535 = true := by
  decide +kernel

theorem tot5535 : totK PA10K2 A10K2.t5535 = [0, 0, 473212109838, 1701213857094, 2007240073744, 777954032463, 62559603274, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

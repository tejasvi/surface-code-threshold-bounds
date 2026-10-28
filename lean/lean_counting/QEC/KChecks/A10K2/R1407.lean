import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5628 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5628 = true := by
  decide +kernel

theorem tot5628 : totK PA10K2 A10K2.t5628 = [0, 0, 504696478891, 1876073182285, 1910128947178, 512427435441, 31301336365, 0, 0, 0] := by
  decide +kernel

theorem rows5629 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5629 = true := by
  decide +kernel

theorem tot5629 : totK PA10K2 A10K2.t5629 = [0, 0, 220190920212, 1195754709812, 2049620342144, 1208227758975, 233551585601, 20058242317, 0, 0] := by
  decide +kernel

theorem rows5630 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5630 = true := by
  decide +kernel

theorem tot5630 : totK PA10K2 A10K2.t5630 = [0, 0, 285186515726, 1333984379845, 2112496743772, 1109023800957, 134864564742, 0, 0, 0] := by
  decide +kernel

theorem rows5631 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5631 = true := by
  decide +kernel

theorem tot5631 : totK PA10K2 A10K2.t5631 = [0, 0, 307561790502, 1499444007051, 2216980835894, 944503866106, 71412904379, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

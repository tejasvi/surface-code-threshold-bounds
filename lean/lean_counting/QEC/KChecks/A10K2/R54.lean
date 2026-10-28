import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows216 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t216 = true := by
  decide +kernel

theorem tot216 : totK PA10K2 A10K2.t216 = [0, 0, 559025985880, 1984161033082, 1977435707356, 518643151754, 18198467119, 0, 0, 0] := by
  decide +kernel

theorem rows217 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t217 = true := by
  decide +kernel

theorem tot217 : totK PA10K2 A10K2.t217 = [0, 0, 0, 827137754326, 2282917916699, 1589094794156, 232470799105, 6439430839, 0, 0] := by
  decide +kernel

theorem rows218 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t218 = true := by
  decide +kernel

theorem tot218 : totK PA10K2 A10K2.t218 = [0, 0, 539587503116, 1818666718145, 1818565011919, 626728826828, 60816768629, 0, 0, 0] := by
  decide +kernel

theorem rows219 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t219 = true := by
  decide +kernel

theorem tot219 : totK PA10K2 A10K2.t219 = [0, 0, 328159929781, 1499760500019, 2118253632516, 863310149738, 62012163500, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5372 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5372 = true := by
  decide +kernel

theorem tot5372 : totK PA10K2 A10K2.t5372 = [0, 0, 658458918821, 2023033593939, 1724814644536, 413579418720, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows5373 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5373 = true := by
  decide +kernel

theorem tot5373 : totK PA10K2 A10K2.t5373 = [0, 229738294190, 1001836022454, 1855265625992, 1356740371961, 234752325660, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows5374 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5374 = true := by
  decide +kernel

theorem tot5374 : totK PA10K2 A10K2.t5374 = [0, 492150731016, 1877245441445, 1901810218450, 488512848742, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5375 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5375 = true := by
  decide +kernel

theorem tot5375 : totK PA10K2 A10K2.t5375 = [0, 0, 806030724121, 2290083025374, 1382577171345, 148254171953, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

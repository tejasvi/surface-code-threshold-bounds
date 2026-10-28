import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2412 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2412 = true := by
  decide +kernel

theorem tot2412 : totK PA10K2 A10K2.t2412 = [0, 0, 495483244363, 1638911545818, 1789976999842, 847767882648, 150824534761, 5885702948, 0, 0] := by
  decide +kernel

theorem rows2413 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2413 = true := by
  decide +kernel

theorem tot2413 : totK PA10K2 A10K2.t2413 = [0, 143089868794, 643339068984, 1526838408096, 1856963786488, 761823463512, 61190578067, 0, 0, 0] := by
  decide +kernel

theorem rows2414 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2414 = true := by
  decide +kernel

theorem tot2414 : totK PA10K2 A10K2.t2414 = [0, 482646624243, 1860993631413, 2079700766294, 639658896054, 33206769304, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2415 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2415 = true := by
  decide +kernel

theorem tot2415 : totK PA10K2 A10K2.t2415 = [0, 0, 728395474769, 2194342857018, 1679797100287, 347338120397, 12473006693, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

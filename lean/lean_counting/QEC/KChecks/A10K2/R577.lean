import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2308 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2308 = true := by
  decide +kernel

theorem tot2308 : totK PA10K2 A10K2.t2308 = [0, 0, 0, 277817397023, 1512077690807, 2065131482460, 637386625579, 38414300562, 0, 0] := by
  decide +kernel

theorem rows2309 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2309 = true := by
  decide +kernel

theorem tot2309 : totK PA10K2 A10K2.t2309 = [0, 0, 0, 285605113691, 1095122555375, 1859834847868, 1156756707732, 185540164104, 5685526223, 0] := by
  decide +kernel

theorem rows2310 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2310 = true := by
  decide +kernel

theorem tot2310 : totK PA10K2 A10K2.t2310 = [0, 0, 0, 486425137730, 1935937065354, 2021131163668, 503153342525, 27915140041, 0, 0] := by
  decide +kernel

theorem rows2311 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2311 = true := by
  decide +kernel

theorem tot2311 : totK PA10K2 A10K2.t2311 = [0, 0, 424355675811, 1693050385446, 1819218787828, 509867235506, 91540144124, 17004268500, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

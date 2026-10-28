import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7212 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7212 = true := by
  decide +kernel

theorem tot7212 : totK PA10K2 A10K2.t7212 = [0, 0, 0, 0, 940570356962, 2332394115119, 1154348357189, 111250938472, 0, 0] := by
  decide +kernel

theorem rows7213 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7213 = true := by
  decide +kernel

theorem tot7213 : totK PA10K2 A10K2.t7213 = [0, 540022072669, 1785216125395, 1640850763636, 420119961539, 64223457255, 178849729860, 84131068563, 6354482628, 0] := by
  decide +kernel

theorem rows7214 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7214 = true := by
  decide +kernel

theorem tot7214 : totK PA10K2 A10K2.t7214 = [0, 295901161011, 1477048257111, 2184995435559, 912983815293, 77492261240, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7215 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7215 = true := by
  decide +kernel

theorem tot7215 : totK PA10K2 A10K2.t7215 = [0, 0, 480837786936, 1793302830121, 1824871574865, 489652173363, 30831673886, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

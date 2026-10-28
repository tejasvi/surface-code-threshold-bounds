import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3424 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3424 = true := by
  decide +kernel

theorem tot3424 : totK PA10K2 A10K2.t3424 = [0, 0, 0, 565289455867, 1913179321030, 1887117277682, 502376265621, 31747192500, 0, 0] := by
  decide +kernel

theorem rows3425 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3425 = true := by
  decide +kernel

theorem tot3425 : totK PA10K2 A10K2.t3425 = [0, 0, 513159322381, 1773266666534, 1967310649877, 722003323767, 72652998273, 0, 0, 0] := by
  decide +kernel

theorem rows3426 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3426 = true := by
  decide +kernel

theorem tot3426 : totK PA10K2 A10K2.t3426 = [0, 0, 321746006324, 1505813589585, 2165505834909, 944411382374, 78493704171, 0, 0, 0] := by
  decide +kernel

theorem rows3427 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3427 = true := by
  decide +kernel

theorem tot3427 : totK PA10K2 A10K2.t3427 = [0, 0, 0, 609483417768, 2085440033923, 1938737509105, 394090515791, 6962742351, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

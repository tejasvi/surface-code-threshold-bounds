import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2292 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2292 = true := by
  decide +kernel

theorem tot2292 : totK PA10K2 A10K2.t2292 = [0, 0, 206470702158, 1030674092934, 1960237111478, 1440796383014, 254156890261, 7047025452, 0, 0] := by
  decide +kernel

theorem rows2293 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2293 = true := by
  decide +kernel

theorem tot2293 : totK PA10K2 A10K2.t2293 = [0, 0, 507552894052, 1900387821630, 2015191708746, 535051181525, 18791677882, 0, 0, 0] := by
  decide +kernel

theorem rows2294 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2294 = true := by
  decide +kernel

theorem tot2294 : totK PA10K2 A10K2.t2294 = [0, 0, 122137344176, 1098319048786, 2272120716140, 1332938692322, 154649353069, 0, 0, 0] := by
  decide +kernel

theorem rows2295 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2295 = true := by
  decide +kernel

theorem tot2295 : totK PA10K2 A10K2.t2295 = [0, 0, 0, 454493504964, 1822159851163, 2034471388179, 577708287083, 17649229841, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

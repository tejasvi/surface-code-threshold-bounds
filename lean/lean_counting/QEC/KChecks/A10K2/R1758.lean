import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7032 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7032 = true := by
  decide +kernel

theorem tot7032 : totK PA10K2 A10K2.t7032 = [0, 0, 652204661509, 2044218239335, 1657918969512, 378675351175, 17500500512, 0, 0, 0] := by
  decide +kernel

theorem rows7033 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7033 = true := by
  decide +kernel

theorem tot7033 : totK PA10K2 A10K2.t7033 = [0, 298738363490, 1319509088444, 1944153303787, 1121621529195, 162122562517, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7034 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7034 = true := by
  decide +kernel

theorem tot7034 : totK PA10K2 A10K2.t7034 = [0, 467024804561, 1802408482397, 2089433789121, 690294327203, 31393628378, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7035 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7035 = true := by
  decide +kernel

theorem tot7035 : totK PA10K2 A10K2.t7035 = [0, 0, 577803079976, 1928352119197, 1801490589824, 451409609278, 17754888877, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

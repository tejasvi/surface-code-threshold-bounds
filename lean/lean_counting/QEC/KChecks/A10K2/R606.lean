import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2424 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2424 = true := by
  decide +kernel

theorem tot2424 : totK PA10K2 A10K2.t2424 = [0, 0, 302214352193, 1292027113526, 1956634028098, 1185544750973, 206325551405, 6632180018, 0, 0] := by
  decide +kernel

theorem rows2425 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2425 = true := by
  decide +kernel

theorem tot2425 : totK PA10K2 A10K2.t2425 = [0, 0, 481019115815, 1831668670595, 1981879992401, 598135069072, 37655512727, 0, 0, 0] := by
  decide +kernel

theorem rows2426 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2426 = true := by
  decide +kernel

theorem tot2426 : totK PA10K2 A10K2.t2426 = [0, 0, 0, 777921360787, 2224413802385, 1636626961130, 277142603587, 7047025452, 0, 0] := by
  decide +kernel

theorem rows2427 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2427 = true := by
  decide +kernel

theorem tot2427 : totK PA10K2 A10K2.t2427 = [0, 0, 542492176839, 1784533045943, 1803683168900, 688290115651, 62018355555, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

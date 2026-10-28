import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2368 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2368 = true := by
  decide +kernel

theorem tot2368 : totK PA10K2 A10K2.t2368 = [0, 0, 495048406196, 1822653338914, 1904081266790, 477576515978, 16735867423, 0, 0, 0] := by
  decide +kernel

theorem rows2369 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2369 = true := by
  decide +kernel

theorem tot2369 : totK PA10K2 A10K2.t2369 = [0, 0, 0, 760666106290, 2331398140990, 1364409411132, 129534905205, 0, 0, 0] := by
  decide +kernel

theorem rows2370 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2370 = true := by
  decide +kernel

theorem tot2370 : totK PA10K2 A10K2.t2370 = [0, 0, 585590977693, 1868171754730, 1678374841908, 565419674668, 110740127019, 6354482628, 0, 0] := by
  decide +kernel

theorem rows2371 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2371 = true := by
  decide +kernel

theorem tot2371 : totK PA10K2 A10K2.t2371 = [0, 0, 258566662976, 1430400711035, 2242912924921, 877035479695, 57524599902, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

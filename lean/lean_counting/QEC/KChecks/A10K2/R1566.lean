import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6264 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6264 = true := by
  decide +kernel

theorem tot6264 : totK PA10K2 A10K2.t6264 = [0, 0, 378133059829, 1643896644559, 2125416796687, 855637134054, 69102974393, 0, 0, 0] := by
  decide +kernel

theorem rows6265 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6265 = true := by
  decide +kernel

theorem tot6265 : totK PA10K2 A10K2.t6265 = [0, 0, 306286378039, 1461060037713, 2192540424637, 1024498808179, 91754584206, 0, 0, 0] := by
  decide +kernel

theorem rows6266 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6266 = true := by
  decide +kernel

theorem tot6266 : totK PA10K2 A10K2.t6266 = [0, 0, 281494735478, 1293043930432, 1947635079677, 1228496721788, 200626967083, 6766355402, 0, 0] := by
  decide +kernel

theorem rows6267 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6267 = true := by
  decide +kernel

theorem tot6267 : totK PA10K2 A10K2.t6267 = [0, 0, 599285222365, 2006527670902, 1932992114763, 436887143669, 11637581167, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2844 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2844 = true := by
  decide +kernel

theorem tot2844 : totK PA10K2 A10K2.t2844 = [327742824672, 1563560327871, 2141489233211, 862185951217, 72955418728, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2845 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2845 = true := by
  decide +kernel

theorem tot2845 : totK PA10K2 A10K2.t2845 = [0, 492228105364, 1983464109449, 2055533231982, 470541447345, 13816090359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2846 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2846 = true := by
  decide +kernel

theorem tot2846 : totK PA10K2 A10K2.t2846 = [0, 414830177729, 1619398662557, 2086365637442, 796630824592, 68716214336, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2847 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2847 = true := by
  decide +kernel

theorem tot2847 : totK PA10K2 A10K2.t2847 = [0, 262218582829, 1311565651099, 2098152867145, 1150711641887, 140364119516, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

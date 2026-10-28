import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2376 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2376 = true := by
  decide +kernel

theorem tot2376 : totK PA10K2 A10K2.t2376 = [0, 0, 293470976355, 1585450243639, 2277388098910, 853448941073, 61781313640, 0, 0, 0] := by
  decide +kernel

theorem rows2377 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2377 = true := by
  decide +kernel

theorem tot2377 : totK PA10K2 A10K2.t2377 = [0, 0, 239518536471, 1151774258258, 1978295078441, 1324657970794, 245158689487, 6962742351, 0, 0] := by
  decide +kernel

theorem rows2378 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2378 = true := by
  decide +kernel

theorem tot2378 : totK PA10K2 A10K2.t2378 = [0, 0, 342670879708, 1561882031315, 2038159321272, 656274080884, 46328001600, 0, 0, 0] := by
  decide +kernel

theorem rows2379 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2379 = true := by
  decide +kernel

theorem tot2379 : totK PA10K2 A10K2.t2379 = [0, 0, 299445560447, 1194263384461, 1883482287027, 1075598029204, 165593577684, 5460492893, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

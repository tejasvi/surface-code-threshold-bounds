import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3088 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3088 = true := by
  decide +kernel

theorem tot3088 : totK PA10K2 A10K2.t3088 = [0, 0, 0, 591100695908, 2058241370595, 1913595854486, 389008960410, 12692412833, 0, 0] := by
  decide +kernel

theorem rows3089 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3089 = true := by
  decide +kernel

theorem tot3089 : totK PA10K2 A10K2.t3089 = [0, 0, 533568215722, 1847338018099, 1907078129015, 549411923328, 49431090885, 0, 0, 0] := by
  decide +kernel

theorem rows3090 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3090 = true := by
  decide +kernel

theorem tot3090 : totK PA10K2 A10K2.t3090 = [0, 0, 327251851251, 1560569276433, 2154105450372, 859184643369, 63006839103, 0, 0, 0] := by
  decide +kernel

theorem rows3091 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3091 = true := by
  decide +kernel

theorem tot3091 : totK PA10K2 A10K2.t3091 = [0, 0, 0, 525707035384, 1981887723455, 2035413115216, 431608379962, 13244237517, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6992 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6992 = true := by
  decide +kernel

theorem tot6992 : totK PA10K2 A10K2.t6992 = [0, 0, 457327470340, 1822776441778, 2013147455980, 546831533412, 32846095359, 0, 0, 0] := by
  decide +kernel

theorem rows6993 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6993 = true := by
  decide +kernel

theorem tot6993 : totK PA10K2 A10K2.t6993 = [0, 0, 451957561089, 1717459201585, 2048921678247, 672225500346, 38869989096, 0, 0, 0] := by
  decide +kernel

theorem rows6994 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6994 = true := by
  decide +kernel

theorem tot6994 : totK PA10K2 A10K2.t6994 = [0, 0, 109259794108, 1146043086263, 2290768030736, 1068317630699, 97301885821, 0, 0, 0] := by
  decide +kernel

theorem rows6995 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6995 = true := by
  decide +kernel

theorem tot6995 : totK PA10K2 A10K2.t6995 = [0, 0, 588716830688, 1906189715264, 1736708690911, 616927485135, 131456749726, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

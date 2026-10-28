import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows296 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t296 = true := by
  decide +kernel

theorem tot296 : totK PA10K2 A10K2.t296 = [0, 28112166549, 17287837956, 537425783210, 1917359280526, 1987231387487, 561462504356, 35503361870, 0, 0] := by
  decide +kernel

theorem rows297 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t297 = true := by
  decide +kernel

theorem tot297 : totK PA10K2 A10K2.t297 = [0, 540361050570, 1970749482893, 1855989451404, 441520064881, 25686058060, 0, 0, 0, 0] := by
  decide +kernel

theorem rows298 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t298 = true := by
  decide +kernel

theorem tot298 : totK PA10K2 A10K2.t298 = [0, 257580387599, 1394615325420, 2184118890953, 937826329801, 72975993186, 0, 0, 0, 0] := by
  decide +kernel

theorem rows299 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t299 = true := by
  decide +kernel

theorem tot299 : totK PA10K2 A10K2.t299 = [0, 0, 479404905712, 1836674337691, 1877635888232, 485037423643, 30831673886, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

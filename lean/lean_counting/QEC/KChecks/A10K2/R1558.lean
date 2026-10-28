import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6232 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6232 = true := by
  decide +kernel

theorem tot6232 : totK PA10K2 A10K2.t6232 = [0, 520503246358, 1822248915681, 1800972620414, 569697447063, 57769988582, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6233 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6233 = true := by
  decide +kernel

theorem tot6233 : totK PA10K2 A10K2.t6233 = [0, 151156996732, 915076720733, 2002874265867, 1294331762201, 194804211921, 5976421810, 0, 0, 0] := by
  decide +kernel

theorem rows6234 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6234 = true := by
  decide +kernel

theorem tot6234 : totK PA10K2 A10K2.t6234 = [0, 548250049781, 1942781982957, 2024713608149, 588135774016, 37716629692, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6235 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6235 = true := by
  decide +kernel

theorem tot6235 : totK PA10K2 A10K2.t6235 = [0, 121142009141, 1013668638857, 2172447007020, 1449454954752, 254809132385, 6853348008, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

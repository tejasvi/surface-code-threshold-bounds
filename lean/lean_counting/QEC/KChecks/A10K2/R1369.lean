import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5476 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5476 = true := by
  decide +kernel

theorem tot5476 : totK PA10K2 A10K2.t5476 = [0, 0, 657062302497, 2027993408367, 1673773879417, 403466865457, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows5477 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5477 = true := by
  decide +kernel

theorem tot5477 : totK PA10K2 A10K2.t5477 = [0, 303780122938, 1179322170758, 1781135067752, 1229735386827, 224675716167, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows5478 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5478 = true := by
  decide +kernel

theorem tot5478 : totK PA10K2 A10K2.t5478 = [0, 519455835492, 1935035299530, 1862441296492, 466121140939, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5479 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5479 = true := by
  decide +kernel

theorem tot5479 : totK PA10K2 A10K2.t5479 = [0, 0, 943790380416, 2385839337166, 1268825934384, 113943173993, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

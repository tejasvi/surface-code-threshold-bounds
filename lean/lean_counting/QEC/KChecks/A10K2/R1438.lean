import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5752 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5752 = true := by
  decide +kernel

theorem tot5752 : totK PA10K2 A10K2.t5752 = [0, 0, 38524389794, 779992847211, 1978383785530, 1498228280179, 335694366938, 25734533292, 0, 0] := by
  decide +kernel

theorem rows5753 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5753 = true := by
  decide +kernel

theorem tot5753 : totK PA10K2 A10K2.t5753 = [0, 0, 201652469469, 1053102796015, 1942626890974, 1297631121266, 204824022915, 5718040558, 0, 0] := by
  decide +kernel

theorem rows5754 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5754 = true := by
  decide +kernel

theorem tot5754 : totK PA10K2 A10K2.t5754 = [0, 0, 583313821732, 1821061459559, 1790948097980, 560613701458, 37254374173, 0, 0, 0] := by
  decide +kernel

theorem rows5755 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5755 = true := by
  decide +kernel

theorem tot5755 : totK PA10K2 A10K2.t5755 = [0, 0, 0, 1075567148894, 2429609322325, 1141885050124, 100354690308, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

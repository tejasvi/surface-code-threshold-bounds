import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7684 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7684 = true := by
  decide +kernel

theorem tot7684 : totK PA10K2 A10K2.t7684 = [0, 0, 0, 0, 535960473387, 1822689355229, 1814785645244, 500191682301, 32523532663, 0] := by
  decide +kernel

theorem rows7685 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7685 = true := by
  decide +kernel

theorem tot7685 : totK PA10K2 A10K2.t7685 = [0, 0, 0, 0, 0, 845193722083, 2220001285249, 1500361051966, 276816579543, 8047840951] := by
  decide +kernel

theorem rows7686 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7686 = true := by
  decide +kernel

theorem tot7686 : totK PA10K2 A10K2.t7686 = [0, 0, 0, 0, 406660325636, 1610936063742, 1963502536534, 683618085122, 42527733730, 0] := by
  decide +kernel

theorem rows7687 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7687 = true := by
  decide +kernel

theorem tot7687 : totK PA10K2 A10K2.t7687 = [0, 0, 0, 0, 740203785504, 2188008200233, 1588344344589, 240644299715, 12145248191, 0] := by
  decide +kernel

end QECKChecks.A10K2

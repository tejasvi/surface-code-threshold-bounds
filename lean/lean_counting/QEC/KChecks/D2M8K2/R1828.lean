import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7312 = true := by
  decide +kernel

theorem tot7312 : totK PD2M8K2 D2M8K2.t7312 = [0, 142042799940, 365626889933, 303014080572, 82793359616, 3434488093, 0, 0] := by
  decide +kernel

theorem rows7313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7313 = true := by
  decide +kernel

theorem tot7313 : totK PD2M8K2 D2M8K2.t7313 = [0, 167986126851, 429631292334, 282162178276, 30524589717, 0, 0, 0] := by
  decide +kernel

theorem rows7314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7314 = true := by
  decide +kernel

theorem tot7314 : totK PD2M8K2 D2M8K2.t7314 = [0, 90498161130, 395218828635, 348068901796, 48694762788, 0, 0, 0] := by
  decide +kernel

theorem rows7315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7315 = true := by
  decide +kernel

theorem tot7315 : totK PD2M8K2 D2M8K2.t7315 = [0, 0, 248985538751, 492251007900, 152014882439, 6860571838, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

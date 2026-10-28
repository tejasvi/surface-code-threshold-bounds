import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3016 = true := by
  decide +kernel

theorem tot3016 : totK PD2M8K2 D2M8K2.t3016 = [0, 146499304292, 406531200816, 344542505115, 39947287535, 0, 0, 0] := by
  decide +kernel

theorem rows3017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3017 = true := by
  decide +kernel

theorem tot3017 : totK PD2M8K2 D2M8K2.t3017 = [0, 191922100521, 482548273206, 224274118294, 12873581184, 0, 0, 0] := by
  decide +kernel

theorem rows3018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3018 = true := by
  decide +kernel

theorem tot3018 : totK PD2M8K2 D2M8K2.t3018 = [0, 87893730914, 395092134740, 373033968376, 54219290804, 0, 0, 0] := by
  decide +kernel

theorem rows3019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3019 = true := by
  decide +kernel

theorem tot3019 : totK PD2M8K2 D2M8K2.t3019 = [0, 0, 198065146458, 458821738840, 232825328220, 18567029682, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

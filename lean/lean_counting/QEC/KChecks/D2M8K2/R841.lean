import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3364 = true := by
  decide +kernel

theorem tot3364 : totK PD2M8K2 D2M8K2.t3364 = [0, 170911852185, 392772462595, 245163974474, 69866803466, 3462014130, 0, 0] := by
  decide +kernel

theorem rows3365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3365 = true := by
  decide +kernel

theorem tot3365 : totK PD2M8K2 D2M8K2.t3365 = [0, 180894072074, 444422026950, 263825342373, 20670625853, 0, 0, 0] := by
  decide +kernel

theorem rows3366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3366 = true := by
  decide +kernel

theorem tot3366 : totK PD2M8K2 D2M8K2.t3366 = [0, 71795413511, 347820035781, 375934909239, 75813393043, 1198073392, 0, 0] := by
  decide +kernel

theorem rows3367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3367 = true := by
  decide +kernel

theorem tot3367 : totK PD2M8K2 D2M8K2.t3367 = [0, 0, 246916076225, 495955453487, 152659901896, 8470662040, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14308 = true := by
  decide +kernel

theorem tot14308 : totK PD2M8K2 D2M8K2.t14308 = [0, 157570664889, 385894604491, 271364203155, 81141934178, 3820764243, 0, 0] := by
  decide +kernel

theorem rows14309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14309 = true := by
  decide +kernel

theorem tot14309 : totK PD2M8K2 D2M8K2.t14309 = [0, 166044043548, 440429311996, 272756326910, 20026845258, 0, 0, 0] := by
  decide +kernel

theorem rows14310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14310 = true := by
  decide +kernel

theorem tot14310 : totK PD2M8K2 D2M8K2.t14310 = [0, 92168731024, 348366114693, 376743429220, 80441187910, 1268739303, 0, 0] := by
  decide +kernel

theorem rows14311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14311 = true := by
  decide +kernel

theorem tot14311 : totK PD2M8K2 D2M8K2.t14311 = [0, 0, 262052263741, 497379788989, 130428041547, 3699256714, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

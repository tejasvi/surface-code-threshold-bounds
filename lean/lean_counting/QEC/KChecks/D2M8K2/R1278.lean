import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5112 = true := by
  decide +kernel

theorem tot5112 : totK PD2M8K2 D2M8K2.t5112 = [0, 0, 85581283184, 402606309019, 366765724428, 36823226034, 0, 0] := by
  decide +kernel

theorem rows5113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5113 = true := by
  decide +kernel

theorem tot5113 : totK PD2M8K2 D2M8K2.t5113 = [0, 0, 193885138561, 458379594357, 246188202005, 17124873119, 0, 0] := by
  decide +kernel

theorem rows5114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5114 = true := by
  decide +kernel

theorem tot5114 : totK PD2M8K2 D2M8K2.t5114 = [0, 0, 119567109088, 427669407881, 317929283878, 23751111587, 0, 0] := by
  decide +kernel

theorem rows5115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5115 = true := by
  decide +kernel

theorem tot5115 : totK PD2M8K2 D2M8K2.t5115 = [0, 0, 0, 303783062770, 505763973457, 80441096884, 1198073392, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

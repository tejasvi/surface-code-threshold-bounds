import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15792 = true := by
  decide +kernel

theorem tot15792 : totK PD2M8K2 D2M8K2.t15792 = [0, 140134488124, 433363230224, 303142696759, 35888653513, 0, 0, 0] := by
  decide +kernel

theorem rows15793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15793 = true := by
  decide +kernel

theorem tot15793 : totK PD2M8K2 D2M8K2.t15793 = [0, 199039016686, 443387613837, 221427022308, 18510921421, 0, 0, 0] := by
  decide +kernel

theorem rows15794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15794 = true := by
  decide +kernel

theorem tot15794 : totK PD2M8K2 D2M8K2.t15794 = [0, 37477818724, 334746277660, 429352596346, 77408704131, 1096505104, 0, 0] := by
  decide +kernel

theorem rows15795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15795 = true := by
  decide +kernel

theorem tot15795 : totK PD2M8K2 D2M8K2.t15795 = [0, 68459858781, 305504038919, 404029971425, 104103671257, 3884009855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

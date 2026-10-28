import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15816 = true := by
  decide +kernel

theorem tot15816 : totK PD2M8K2 D2M8K2.t15816 = [0, 42579362153, 224150813302, 444006055773, 196364849460, 8214505460, 0, 0] := by
  decide +kernel

theorem rows15817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15817 = true := by
  decide +kernel

theorem tot15817 : totK PD2M8K2 D2M8K2.t15817 = [0, 171966238378, 445389862437, 279776442249, 29105839948, 0, 0, 0] := by
  decide +kernel

theorem rows15818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15818 = true := by
  decide +kernel

theorem tot15818 : totK PD2M8K2 D2M8K2.t15818 = [0, 117142903938, 435218572713, 339076137604, 40326756910, 0, 0, 0] := by
  decide +kernel

theorem rows15819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15819 = true := by
  decide +kernel

theorem tot15819 : totK PD2M8K2 D2M8K2.t15819 = [0, 0, 228700280479, 494902383232, 170384486471, 8302875791, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15504 = true := by
  decide +kernel

theorem tot15504 : totK PD2M8K2 D2M8K2.t15504 = [0, 183938888662, 448557616172, 230193143059, 17115888737, 0, 0, 0] := by
  decide +kernel

theorem rows15505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15505 = true := by
  decide +kernel

theorem tot15505 : totK PD2M8K2 D2M8K2.t15505 = [0, 87762578873, 409507173141, 358589825860, 39835146298, 0, 0, 0] := by
  decide +kernel

theorem rows15506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15506 = true := by
  decide +kernel

theorem tot15506 : totK PD2M8K2 D2M8K2.t15506 = [0, 0, 283175503026, 511040621932, 101002138354, 1369150432, 0, 0] := by
  decide +kernel

theorem rows15507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15507 = true := by
  decide +kernel

theorem tot15507 : totK PD2M8K2 D2M8K2.t15507 = [0, 160124191442, 446418544256, 282035948919, 29446467512, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

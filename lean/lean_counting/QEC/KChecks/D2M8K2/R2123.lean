import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8492 = true := by
  decide +kernel

theorem tot8492 : totK PD2M8K2 D2M8K2.t8492 = [48724726441, 284440880192, 386895846968, 178434195226, 21400436502, 0, 0, 0] := by
  decide +kernel

theorem rows8493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8493 = true := by
  decide +kernel

theorem tot8493 : totK PD2M8K2 D2M8K2.t8493 = [0, 209739359795, 481770058813, 208086370388, 7994456143, 0, 0, 0] := by
  decide +kernel

theorem rows8494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8494 = true := by
  decide +kernel

theorem tot8494 : totK PD2M8K2 D2M8K2.t8494 = [51340655322, 235287065111, 412615813170, 187619800398, 8214505460, 0, 0, 0] := by
  decide +kernel

theorem rows8495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8495 = true := by
  decide +kernel

theorem tot8495 : totK PD2M8K2 D2M8K2.t8495 = [181695580645, 452604144360, 267186873544, 27955297403, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

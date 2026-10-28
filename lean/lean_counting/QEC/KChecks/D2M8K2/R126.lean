import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t504 = true := by
  decide +kernel

theorem tot504 : totK PD2M8K2 D2M8K2.t504 = [0, 55259466049, 347685726372, 451448891175, 48974580800, 0, 0, 0] := by
  decide +kernel

theorem rows505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t505 = true := by
  decide +kernel

theorem tot505 : totK PD2M8K2 D2M8K2.t505 = [0, 161863271666, 446554505126, 284081839128, 30337698200, 0, 0, 0] := by
  decide +kernel

theorem rows506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t506 = true := by
  decide +kernel

theorem tot506 : totK PD2M8K2 D2M8K2.t506 = [0, 186139194019, 485239299671, 213256145981, 6545772547, 0, 0, 0] := by
  decide +kernel

theorem rows507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t507 = true := by
  decide +kernel

theorem tot507 : totK PD2M8K2 D2M8K2.t507 = [0, 0, 215562442101, 477542344909, 198120280901, 14593677817, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

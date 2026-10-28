import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t436 = true := by
  decide +kernel

theorem tot436 : totK PD2M8K2 D2M8K2.t436 = [0, 258378137808, 494954584923, 145958941446, 3699256714, 0, 0, 0] := by
  decide +kernel

theorem rows437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t437 = true := by
  decide +kernel

theorem tot437 : totK PD2M8K2 D2M8K2.t437 = [0, 183144593740, 461795136171, 227422436142, 17080783126, 0, 0, 0] := by
  decide +kernel

theorem rows438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t438 = true := by
  decide +kernel

theorem tot438 : totK PD2M8K2 D2M8K2.t438 = [0, 164279129513, 480507085416, 234738464569, 7984731767, 0, 0, 0] := by
  decide +kernel

theorem rows439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t439 = true := by
  decide +kernel

theorem tot439 : totK PD2M8K2 D2M8K2.t439 = [0, 155290787624, 453695782120, 263799504477, 18770886774, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

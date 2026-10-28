import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14292 = true := by
  decide +kernel

theorem tot14292 : totK PD2M8K2 D2M8K2.t14292 = [0, 0, 221996894126, 482139220816, 158180264736, 4811815119, 0, 0] := by
  decide +kernel

theorem rows14293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14293 = true := by
  decide +kernel

theorem tot14293 : totK PD2M8K2 D2M8K2.t14293 = [0, 37283609705, 206821086792, 412808341407, 206373643942, 16939352947, 0, 0] := by
  decide +kernel

theorem rows14294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14294 = true := by
  decide +kernel

theorem tot14294 : totK PD2M8K2 D2M8K2.t14294 = [0, 202144173102, 482763776315, 208218772138, 9852138406, 0, 0, 0] := by
  decide +kernel

theorem rows14295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14295 = true := by
  decide +kernel

theorem tot14295 : totK PD2M8K2 D2M8K2.t14295 = [0, 193458087476, 461964128795, 209785935962, 12413541223, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

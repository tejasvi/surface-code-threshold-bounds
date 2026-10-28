import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4848 = true := by
  decide +kernel

theorem tot4848 : totK PD2M8K2 D2M8K2.t4848 = [0, 0, 177550997700, 471213954804, 235009854708, 15568047967, 0, 0] := by
  decide +kernel

theorem rows4849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4849 = true := by
  decide +kernel

theorem tot4849 : totK PD2M8K2 D2M8K2.t4849 = [0, 0, 0, 331810228203, 515610152390, 68521029370, 0, 0] := by
  decide +kernel

theorem rows4850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4850 = true := by
  decide +kernel

theorem tot4850 : totK PD2M8K2 D2M8K2.t4850 = [0, 0, 143904637236, 365469343570, 299305267377, 88112878093, 2585032425, 0] := by
  decide +kernel

theorem rows4851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4851 = true := by
  decide +kernel

theorem tot4851 : totK PD2M8K2 D2M8K2.t4851 = [0, 0, 175473196090, 455019422398, 267740215993, 27345626671, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

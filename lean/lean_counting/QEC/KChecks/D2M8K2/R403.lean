import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1612 = true := by
  decide +kernel

theorem tot1612 : totK PD2M8K2 D2M8K2.t1612 = [0, 0, 215926042908, 487185455112, 184182835717, 5295475062, 0, 0] := by
  decide +kernel

theorem rows1613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1613 = true := by
  decide +kernel

theorem tot1613 : totK PD2M8K2 D2M8K2.t1613 = [0, 85167078157, 255330633397, 380169521228, 157424371295, 5430665091, 0, 0] := by
  decide +kernel

theorem rows1614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1614 = true := by
  decide +kernel

theorem tot1614 : totK PD2M8K2 D2M8K2.t1614 = [0, 169783732469, 456928195356, 248823994193, 21003892541, 0, 0, 0] := by
  decide +kernel

theorem rows1615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1615 = true := by
  decide +kernel

theorem tot1615 : totK PD2M8K2 D2M8K2.t1615 = [0, 156197801301, 451301775135, 262329910022, 22109868542, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

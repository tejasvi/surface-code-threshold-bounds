import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2588 = true := by
  decide +kernel

theorem tot2588 : totK PD2M8K2 D2M8K2.t2588 = [0, 174606954558, 443860659681, 259215499595, 25359931193, 0, 0, 0] := by
  decide +kernel

theorem rows2589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2589 = true := by
  decide +kernel

theorem tot2589 : totK PD2M8K2 D2M8K2.t2589 = [0, 180924024847, 495114956519, 223506545470, 6610549359, 0, 0, 0] := by
  decide +kernel

theorem rows2590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2590 = true := by
  decide +kernel

theorem tot2590 : totK PD2M8K2 D2M8K2.t2590 = [165400824333, 417913763116, 246971163075, 68326740101, 5618966238, 0, 0, 0] := by
  decide +kernel

theorem rows2591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2591 = true := by
  decide +kernel

theorem tot2591 : totK PD2M8K2 D2M8K2.t2591 = [195559355116, 457392963316, 229704607033, 16615742754, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

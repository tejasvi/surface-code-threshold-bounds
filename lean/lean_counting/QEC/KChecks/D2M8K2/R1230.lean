import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4920 = true := by
  decide +kernel

theorem tot4920 : totK PD2M8K2 D2M8K2.t4920 = [0, 0, 179905492135, 450907156403, 268990667175, 27410702197, 0, 0] := by
  decide +kernel

theorem rows4921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4921 = true := by
  decide +kernel

theorem tot4921 : totK PD2M8K2 D2M8K2.t4921 = [0, 0, 159421186084, 482340077610, 264260882102, 13434149270, 0, 0] := by
  decide +kernel

theorem rows4922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4922 = true := by
  decide +kernel

theorem tot4922 : totK PD2M8K2 D2M8K2.t4922 = [0, 0, 0, 196065105725, 458787152790, 228258971308, 20729648156, 0] := by
  decide +kernel

theorem rows4923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4923 = true := by
  decide +kernel

theorem tot4923 : totK PD2M8K2 D2M8K2.t4923 = [0, 0, 0, 208567165271, 495981021343, 190529633892, 5290448418, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9228 = true := by
  decide +kernel

theorem tot9228 : totK PD2M8K2 D2M8K2.t9228 = [161044031498, 477367492796, 258490099652, 15130184731, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9229 = true := by
  decide +kernel

theorem tot9229 : totK PD2M8K2 D2M8K2.t9229 = [0, 195757825875, 453335062204, 238462769476, 24245300989, 0, 0, 0] := by
  decide +kernel

theorem rows9230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9230 = true := by
  decide +kernel

theorem tot9230 : totK PD2M8K2 D2M8K2.t9230 = [0, 192922983078, 481560353194, 220293026276, 6540674557, 0, 0, 0] := by
  decide +kernel

theorem rows9231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9231 = true := by
  decide +kernel

theorem tot9231 : totK PD2M8K2 D2M8K2.t9231 = [172392954269, 392640517887, 238136460806, 93435328613, 6778563787, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

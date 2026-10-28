import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7592 = true := by
  decide +kernel

theorem tot7592 : totK PD2M8K2 D2M8K2.t7592 = [0, 72493291087, 341593210413, 393187095752, 85319928124, 1164319620, 0, 0] := by
  decide +kernel

theorem rows7593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7593 = true := by
  decide +kernel

theorem tot7593 : totK PD2M8K2 D2M8K2.t7593 = [0, 0, 228152767514, 490302977719, 162878845778, 9404247146, 0, 0] := by
  decide +kernel

theorem rows7594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7594 = true := by
  decide +kernel

theorem tot7594 : totK PD2M8K2 D2M8K2.t7594 = [0, 163721061462, 407600979727, 258028856202, 56866112714, 2481160468, 0, 0] := by
  decide +kernel

theorem rows7595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7595 = true := by
  decide +kernel

theorem tot7595 : totK PD2M8K2 D2M8K2.t7595 = [0, 159900448456, 474505200211, 254790091293, 14963133681, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

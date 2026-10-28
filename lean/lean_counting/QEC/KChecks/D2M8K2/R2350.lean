import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9400 = true := by
  decide +kernel

theorem tot9400 : totK PD2M8K2 D2M8K2.t9400 = [0, 159421166364, 437151847510, 277579556629, 25435570800, 0, 0, 0] := by
  decide +kernel

theorem rows9401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9401 = true := by
  decide +kernel

theorem tot9401 : totK PD2M8K2 D2M8K2.t9401 = [0, 91626568394, 355784713174, 360009032557, 72640256773, 1096505104, 0, 0] := by
  decide +kernel

theorem rows9402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9402 = true := by
  decide +kernel

theorem tot9402 : totK PD2M8K2 D2M8K2.t9402 = [0, 0, 309065031443, 513081860252, 87984400165, 1069412848, 0, 0] := by
  decide +kernel

theorem rows9403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9403 = true := by
  decide +kernel

theorem tot9403 : totK PD2M8K2 D2M8K2.t9403 = [0, 166751405801, 411606847237, 263305993505, 60898560722, 2814597007, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

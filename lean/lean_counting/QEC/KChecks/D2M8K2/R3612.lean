import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14448 = true := by
  decide +kernel

theorem tot14448 : totK PD2M8K2 D2M8K2.t14448 = [0, 190291148038, 464701907103, 220938483845, 16781273960, 0, 0, 0] := by
  decide +kernel

theorem rows14449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14449 = true := by
  decide +kernel

theorem tot14449 : totK PD2M8K2 D2M8K2.t14449 = [0, 206566007585, 468039066493, 204168400619, 12593797338, 0, 0, 0] := by
  decide +kernel

theorem rows14450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14450 = true := by
  decide +kernel

theorem tot14450 : totK PD2M8K2 D2M8K2.t14450 = [0, 179236780492, 492657249097, 229969684174, 6677188808, 0, 0, 0] := by
  decide +kernel

theorem rows14451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14451 = true := by
  decide +kernel

theorem tot14451 : totK PD2M8K2 D2M8K2.t14451 = [0, 170630596799, 454968749945, 233979661453, 13426997696, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

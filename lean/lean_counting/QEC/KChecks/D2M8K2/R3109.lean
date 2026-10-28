import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12436 = true := by
  decide +kernel

theorem tot12436 : totK PD2M8K2 D2M8K2.t12436 = [0, 93159147314, 382271899535, 394754805148, 45235598834, 0, 0, 0] := by
  decide +kernel

theorem rows12437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12437 = true := by
  decide +kernel

theorem tot12437 : totK PD2M8K2 D2M8K2.t12437 = [0, 173242359395, 444494324249, 260814970918, 21096718504, 0, 0, 0] := by
  decide +kernel

theorem rows12438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12438 = true := by
  decide +kernel

theorem tot12438 : totK PD2M8K2 D2M8K2.t12438 = [0, 158068269428, 475920605516, 269018529349, 14391233660, 0, 0, 0] := by
  decide +kernel

theorem rows12439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12439 = true := by
  decide +kernel

theorem tot12439 : totK PD2M8K2 D2M8K2.t12439 = [0, 0, 178804503512, 464412435433, 229769660902, 18317572719, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

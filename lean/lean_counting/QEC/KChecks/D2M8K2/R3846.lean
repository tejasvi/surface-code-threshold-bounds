import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15384 = true := by
  decide +kernel

theorem tot15384 : totK PD2M8K2 D2M8K2.t15384 = [0, 0, 350956682706, 497855231126, 65141556670, 0, 0, 0] := by
  decide +kernel

theorem rows15385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15385 = true := by
  decide +kernel

theorem tot15385 : totK PD2M8K2 D2M8K2.t15385 = [0, 116789802826, 357056106552, 330467496169, 87506177215, 3884009855, 0, 0] := by
  decide +kernel

theorem rows15386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15386 = true := by
  decide +kernel

theorem tot15386 : totK PD2M8K2 D2M8K2.t15386 = [0, 172325149810, 445140211437, 274795762694, 30247476123, 0, 0, 0] := by
  decide +kernel

theorem rows15387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15387 = true := by
  decide +kernel

theorem tot15387 : totK PD2M8K2 D2M8K2.t15387 = [0, 129469574848, 432157336913, 319363859006, 27674516655, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

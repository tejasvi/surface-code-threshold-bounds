import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5624 = true := by
  decide +kernel

theorem tot5624 : totK PD2M8K2 D2M8K2.t5624 = [0, 140046100198, 458651607421, 263228544722, 18656300070, 0, 0, 0] := by
  decide +kernel

theorem rows5625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5625 = true := by
  decide +kernel

theorem tot5625 : totK PD2M8K2 D2M8K2.t5625 = [0, 0, 325243695948, 454266589700, 74189987438, 1138244013, 0, 0] := by
  decide +kernel

theorem rows5626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5626 = true := by
  decide +kernel

theorem tot5626 : totK PD2M8K2 D2M8K2.t5626 = [0, 180253396623, 446202434651, 264511697743, 29076528255, 0, 0, 0] := by
  decide +kernel

theorem rows5627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5627 = true := by
  decide +kernel

theorem tot5627 : totK PD2M8K2 D2M8K2.t5627 = [0, 216610940250, 484812067051, 187357232774, 10179897161, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

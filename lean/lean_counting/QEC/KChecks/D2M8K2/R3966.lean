import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15864 = true := by
  decide +kernel

theorem tot15864 : totK PD2M8K2 D2M8K2.t15864 = [0, 193212958034, 436592369878, 247107973398, 25019583705, 0, 0, 0] := by
  decide +kernel

theorem rows15865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15865 = true := by
  decide +kernel

theorem tot15865 : totK PD2M8K2 D2M8K2.t15865 = [0, 123799385224, 451984095731, 294462314379, 21540847763, 0, 0, 0] := by
  decide +kernel

theorem rows15866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15866 = true := by
  decide +kernel

theorem tot15866 : totK PD2M8K2 D2M8K2.t15866 = [0, 0, 274326121303, 524657662284, 98759120209, 1096505104, 0, 0] := by
  decide +kernel

theorem rows15867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15867 = true := by
  decide +kernel

theorem tot15867 : totK PD2M8K2 D2M8K2.t15867 = [0, 157581518143, 378348882994, 267055085754, 75669748557, 3884009855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

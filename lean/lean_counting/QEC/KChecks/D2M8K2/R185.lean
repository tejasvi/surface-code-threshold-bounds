import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t740 = true := by
  decide +kernel

theorem tot740 : totK PD2M8K2 D2M8K2.t740 = [0, 220111161689, 492012811572, 166342617473, 4967996017, 0, 0, 0] := by
  decide +kernel

theorem rows741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t741 = true := by
  decide +kernel

theorem tot741 : totK PD2M8K2 D2M8K2.t741 = [0, 181091003179, 476340502741, 220414879820, 11307310893, 0, 0, 0] := by
  decide +kernel

theorem rows742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t742 = true := by
  decide +kernel

theorem tot742 : totK PD2M8K2 D2M8K2.t742 = [0, 204688121337, 481725037053, 198191170978, 11109542248, 0, 0, 0] := by
  decide +kernel

theorem rows743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t743 = true := by
  decide +kernel

theorem tot743 : totK PD2M8K2 D2M8K2.t743 = [0, 201153292439, 490727623187, 190149058991, 5098257138, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

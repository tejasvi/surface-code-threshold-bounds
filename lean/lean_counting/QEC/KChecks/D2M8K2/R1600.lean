import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6400 = true := by
  decide +kernel

theorem tot6400 : totK PD2M8K2 D2M8K2.t6400 = [0, 199016960195, 473269796110, 218315307817, 11232467588, 0, 0, 0] := by
  decide +kernel

theorem rows6401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6401 = true := by
  decide +kernel

theorem tot6401 : totK PD2M8K2 D2M8K2.t6401 = [0, 98332099094, 393255825841, 328616262556, 46647804326, 1104198603, 0, 0] := by
  decide +kernel

theorem rows6402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6402 = true := by
  decide +kernel

theorem tot6402 : totK PD2M8K2 D2M8K2.t6402 = [0, 11292364526, 247086289125, 496504471296, 127896741506, 3581949829, 0, 0] := by
  decide +kernel

theorem rows6403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6403 = true := by
  decide +kernel

theorem tot6403 : totK PD2M8K2 D2M8K2.t6403 = [0, 176592110121, 463352674468, 246627001283, 22720214443, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1688 = true := by
  decide +kernel

theorem tot1688 : totK PD2M8K2 D2M8K2.t1688 = [0, 0, 153643884644, 427757250617, 272288943699, 26222421095, 0, 0] := by
  decide +kernel

theorem rows1689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1689 = true := by
  decide +kernel

theorem tot1689 : totK PD2M8K2 D2M8K2.t1689 = [0, 0, 167777288063, 434961700390, 246936359969, 18510921421, 0, 0] := by
  decide +kernel

theorem rows1690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1690 = true := by
  decide +kernel

theorem tot1690 : totK PD2M8K2 D2M8K2.t1690 = [0, 0, 90582212958, 367347203523, 357062369778, 62708809440, 1096505104, 0] := by
  decide +kernel

theorem rows1691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1691 = true := by
  decide +kernel

theorem tot1691 : totK PD2M8K2 D2M8K2.t1691 = [0, 0, 0, 272416142906, 495800879084, 97037213315, 1069412848, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

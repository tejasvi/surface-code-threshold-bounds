import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14936 = true := by
  decide +kernel

theorem tot14936 : totK PD2M8K2 D2M8K2.t14936 = [0, 0, 196202562287, 468905970019, 193802937976, 9840474482, 0, 0] := by
  decide +kernel

theorem rows14937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14937 = true := by
  decide +kernel

theorem tot14937 : totK PD2M8K2 D2M8K2.t14937 = [0, 0, 214680647895, 510157355874, 173609528346, 2753995038, 0, 0] := by
  decide +kernel

theorem rows14938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14938 = true := by
  decide +kernel

theorem tot14938 : totK PD2M8K2 D2M8K2.t14938 = [0, 0, 163426135342, 467978443879, 220943795023, 8966096369, 0, 0] := by
  decide +kernel

theorem rows14939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14939 = true := by
  decide +kernel

theorem tot14939 : totK PD2M8K2 D2M8K2.t14939 = [0, 0, 198740694217, 480446039105, 174770693748, 7472928540, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

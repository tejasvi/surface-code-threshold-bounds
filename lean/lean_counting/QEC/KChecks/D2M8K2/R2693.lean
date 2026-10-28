import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10772 = true := by
  decide +kernel

theorem tot10772 : totK PD2M8K2 D2M8K2.t10772 = [0, 116078642089, 409028360867, 346391540022, 35460394392, 0, 0, 0] := by
  decide +kernel

theorem rows10773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10773 = true := by
  decide +kernel

theorem tot10773 : totK PD2M8K2 D2M8K2.t10773 = [0, 174948321201, 446201950431, 242924087419, 25655084758, 0, 0, 0] := by
  decide +kernel

theorem rows10774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10774 = true := by
  decide +kernel

theorem tot10774 : totK PD2M8K2 D2M8K2.t10774 = [0, 87208453540, 356019805889, 372428714327, 70643155140, 1164319620, 0, 0] := by
  decide +kernel

theorem rows10775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10775 = true := by
  decide +kernel

theorem tot10775 : totK PD2M8K2 D2M8K2.t10775 = [0, 0, 258487781707, 499478918415, 132813473723, 4234510686, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

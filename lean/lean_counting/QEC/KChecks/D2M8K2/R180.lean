import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t720 = true := by
  decide +kernel

theorem tot720 : totK PD2M8K2 D2M8K2.t720 = [0, 92498175148, 367903271158, 343384407248, 65350093653, 1095107716, 0, 0] := by
  decide +kernel

theorem rows721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t721 = true := by
  decide +kernel

theorem tot721 : totK PD2M8K2 D2M8K2.t721 = [0, 0, 318294222030, 468971395114, 82109342826, 1067409660, 0, 0] := by
  decide +kernel

theorem rows722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t722 = true := by
  decide +kernel

theorem tot722 : totK PD2M8K2 D2M8K2.t722 = [168683899851, 414810552513, 181446495047, 73399078842, 45879004154, 2814597007, 0, 0] := by
  decide +kernel

theorem rows723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t723 = true := by
  decide +kernel

theorem tot723 : totK PD2M8K2 D2M8K2.t723 = [200597199500, 466820676878, 216710314321, 12526078277, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15256 = true := by
  decide +kernel

theorem tot15256 : totK PD2M8K2 D2M8K2.t15256 = [0, 0, 0, 235636772523, 512271076146, 123943802150, 2330587781, 0] := by
  decide +kernel

theorem rows15257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15257 = true := by
  decide +kernel

theorem tot15257 : totK PD2M8K2 D2M8K2.t15257 = [0, 0, 0, 225436510267, 518974450410, 148801613753, 2448800629, 0] := by
  decide +kernel

theorem rows15258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15258 = true := by
  decide +kernel

theorem tot15258 : totK PD2M8K2 D2M8K2.t15258 = [0, 0, 0, 208103634744, 476077467207, 175727490139, 7785776211, 0] := by
  decide +kernel

theorem rows15259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15259 = true := by
  decide +kernel

theorem tot15259 : totK PD2M8K2 D2M8K2.t15259 = [0, 0, 179595312347, 374809282031, 226380458962, 109788158832, 13269537371, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

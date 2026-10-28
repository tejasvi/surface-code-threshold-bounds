import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10000 = true := by
  decide +kernel

theorem tot10000 : totK PD2M8K2 D2M8K2.t10000 = [0, 0, 178830837160, 439141209534, 254150771336, 22640330759, 0, 0] := by
  decide +kernel

theorem rows10001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10001 = true := by
  decide +kernel

theorem tot10001 : totK PD2M8K2 D2M8K2.t10001 = [0, 0, 110354327943, 446615942741, 314959283305, 26503335942, 0, 0] := by
  decide +kernel

theorem rows10002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10002 = true := by
  decide +kernel

theorem tot10002 : totK PD2M8K2 D2M8K2.t10002 = [0, 0, 0, 290620236059, 518342564642, 84691846752, 1096505104, 0] := by
  decide +kernel

theorem rows10003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10003 = true := by
  decide +kernel

theorem tot10003 : totK PD2M8K2 D2M8K2.t10003 = [0, 0, 155536724975, 371850699637, 279955869374, 81485200354, 3884009855, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3668 = true := by
  decide +kernel

theorem tot3668 : totK PD2M8K2 D2M8K2.t3668 = [0, 0, 272703393349, 507374339928, 99886894221, 1128973710, 0, 0] := by
  decide +kernel

theorem rows3669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3669 = true := by
  decide +kernel

theorem tot3669 : totK PD2M8K2 D2M8K2.t3669 = [0, 49782501411, 224889792839, 410275526177, 166534425599, 11780292382, 0, 0] := by
  decide +kernel

theorem rows3670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3670 = true := by
  decide +kernel

theorem tot3670 : totK PD2M8K2 D2M8K2.t3670 = [0, 179896710259, 454058820537, 248100591077, 22731460158, 0, 0, 0] := by
  decide +kernel

theorem rows3671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3671 = true := by
  decide +kernel

theorem tot3671 : totK PD2M8K2 D2M8K2.t3671 = [0, 183132222034, 482094804482, 222681336748, 12523541424, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

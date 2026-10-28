import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3896 = true := by
  decide +kernel

theorem tot3896 : totK PD2M8K2 D2M8K2.t3896 = [0, 0, 172256363354, 492635618207, 221655341878, 7908366594, 0, 0] := by
  decide +kernel

theorem rows3897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3897 = true := by
  decide +kernel

theorem tot3897 : totK PD2M8K2 D2M8K2.t3897 = [0, 112537107697, 322501742527, 319604830028, 140509321417, 8191853852, 0, 0] := by
  decide +kernel

theorem rows3898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3898 = true := by
  decide +kernel

theorem tot3898 : totK PD2M8K2 D2M8K2.t3898 = [0, 166350530156, 441550876547, 277736511701, 30470443108, 0, 0, 0] := by
  decide +kernel

theorem rows3899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3899 = true := by
  decide +kernel

theorem tot3899 : totK PD2M8K2 D2M8K2.t3899 = [0, 136067881118, 448313653447, 290002762585, 25021039385, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

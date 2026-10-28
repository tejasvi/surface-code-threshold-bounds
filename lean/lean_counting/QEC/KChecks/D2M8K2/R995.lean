import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3980 = true := by
  decide +kernel

theorem tot3980 : totK PD2M8K2 D2M8K2.t3980 = [0, 93348984190, 367799045254, 408497949659, 46358151300, 0, 0, 0] := by
  decide +kernel

theorem rows3981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3981 = true := by
  decide +kernel

theorem tot3981 : totK PD2M8K2 D2M8K2.t3981 = [0, 155888890441, 441348936384, 282076240220, 29900658212, 0, 0, 0] := by
  decide +kernel

theorem rows3982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3982 = true := by
  decide +kernel

theorem tot3982 : totK PD2M8K2 D2M8K2.t3982 = [0, 175058849830, 490531236598, 244817673466, 10610441670, 0, 0, 0] := by
  decide +kernel

theorem rows3983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3983 = true := by
  decide +kernel

theorem tot3983 : totK PD2M8K2 D2M8K2.t3983 = [0, 0, 217229359137, 461753590138, 208661300314, 18724171075, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

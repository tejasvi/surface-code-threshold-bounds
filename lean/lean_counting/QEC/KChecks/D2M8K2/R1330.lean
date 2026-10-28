import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5320 = true := by
  decide +kernel

theorem tot5320 : totK PD2M8K2 D2M8K2.t5320 = [0, 0, 195282234398, 476319346661, 193737890457, 12052611869, 0, 0] := by
  decide +kernel

theorem rows5321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5321 = true := by
  decide +kernel

theorem tot5321 : totK PD2M8K2 D2M8K2.t5321 = [0, 152574673325, 438163462470, 291950689118, 42093899789, 0, 0, 0] := by
  decide +kernel

theorem rows5322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5322 = true := by
  decide +kernel

theorem tot5322 : totK PD2M8K2 D2M8K2.t5322 = [0, 174773797690, 468971675867, 250154769173, 15405658917, 0, 0, 0] := by
  decide +kernel

theorem rows5323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5323 = true := by
  decide +kernel

theorem tot5323 : totK PD2M8K2 D2M8K2.t5323 = [0, 0, 324202351721, 520536105815, 74999799004, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

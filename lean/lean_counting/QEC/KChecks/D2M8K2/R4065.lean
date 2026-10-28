import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16260 = true := by
  decide +kernel

theorem tot16260 : totK PD2M8K2 D2M8K2.t16260 = [0, 0, 0, 170789101544, 492896023879, 192469988681, 6506332950, 0] := by
  decide +kernel

theorem rows16261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16261 = true := by
  decide +kernel

theorem tot16261 : totK PD2M8K2 D2M8K2.t16261 = [0, 0, 0, 204301338891, 480920334674, 200412494511, 10132347792, 0] := by
  decide +kernel

theorem rows16262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16262 = true := by
  decide +kernel

theorem tot16262 : totK PD2M8K2 D2M8K2.t16262 = [0, 0, 0, 205794599808, 489757594860, 175113661207, 5464186513, 0] := by
  decide +kernel

theorem rows16263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16263 = true := by
  decide +kernel

theorem tot16263 : totK PD2M8K2 D2M8K2.t16263 = [0, 0, 0, 173570828744, 481960398250, 202798403964, 10133036384, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

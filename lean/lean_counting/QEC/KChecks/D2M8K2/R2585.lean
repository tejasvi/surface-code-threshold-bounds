import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10340 = true := by
  decide +kernel

theorem tot10340 : totK PD2M8K2 D2M8K2.t10340 = [0, 0, 216766687654, 501746217548, 192637870942, 5424570950, 0, 0] := by
  decide +kernel

theorem rows10341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10341 = true := by
  decide +kernel

theorem tot10341 : totK PD2M8K2 D2M8K2.t10341 = [0, 164773433953, 375728409934, 245588979780, 104683910284, 6804944647, 0, 0] := by
  decide +kernel

theorem rows10342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10342 = true := by
  decide +kernel

theorem tot10342 : totK PD2M8K2 D2M8K2.t10342 = [0, 161825429135, 456202676055, 282985775819, 19327413851, 0, 0, 0] := by
  decide +kernel

theorem rows10343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10343 = true := by
  decide +kernel

theorem tot10343 : totK PD2M8K2 D2M8K2.t10343 = [0, 0, 244064226978, 505096928083, 135410473340, 2309606161, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

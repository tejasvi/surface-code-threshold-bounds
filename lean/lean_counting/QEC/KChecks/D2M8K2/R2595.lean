import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10380 = true := by
  decide +kernel

theorem tot10380 : totK PD2M8K2 D2M8K2.t10380 = [0, 0, 125781128085, 357381518210, 311176903746, 82396569291, 3521263076, 0] := by
  decide +kernel

theorem rows10381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10381 = true := by
  decide +kernel

theorem tot10381 : totK PD2M8K2 D2M8K2.t10381 = [0, 0, 187041338033, 453403194490, 214047669686, 14663123310, 0, 0] := by
  decide +kernel

theorem rows10382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10382 = true := by
  decide +kernel

theorem tot10382 : totK PD2M8K2 D2M8K2.t10382 = [0, 0, 90564426449, 389801559779, 347583751779, 49611662236, 1096505104, 0] := by
  decide +kernel

theorem rows10383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10383 = true := by
  decide +kernel

theorem tot10383 : totK PD2M8K2 D2M8K2.t10383 = [0, 0, 0, 315947941126, 503329436759, 66951249832, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

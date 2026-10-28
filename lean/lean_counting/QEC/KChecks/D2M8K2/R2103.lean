import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8412 = true := by
  decide +kernel

theorem tot8412 : totK PD2M8K2 D2M8K2.t8412 = [0, 0, 201771804388, 472673731077, 185610775281, 12158747742, 0, 0] := by
  decide +kernel

theorem rows8413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8413 = true := by
  decide +kernel

theorem tot8413 : totK PD2M8K2 D2M8K2.t8413 = [0, 0, 201896852228, 474772199455, 186244552559, 10059780603, 0, 0] := by
  decide +kernel

theorem rows8414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8414 = true := by
  decide +kernel

theorem tot8414 : totK PD2M8K2 D2M8K2.t8414 = [0, 0, 187621844498, 453058273434, 196026577435, 16632323428, 0, 0] := by
  decide +kernel

theorem rows8415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8415 = true := by
  decide +kernel

theorem tot8415 : totK PD2M8K2 D2M8K2.t8415 = [0, 0, 210938728725, 503920308802, 174181619702, 5219851397, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

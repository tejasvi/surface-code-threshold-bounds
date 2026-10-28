import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4252 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4252 = true := by
  decide +kernel

theorem tot4252 : totK PA10K2 A10K2.t4252 = [0, 470378782284, 1850831178798, 2031351147341, 576987579418, 23620721234, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4253 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4253 = true := by
  decide +kernel

theorem tot4253 : totK PA10K2 A10K2.t4253 = [0, 328730752589, 1484389285035, 2173168076941, 937751141669, 69396441685, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4254 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4254 = true := by
  decide +kernel

theorem tot4254 : totK PA10K2 A10K2.t4254 = [0, 0, 578069034154, 2017776460577, 1942983338035, 398215087269, 12224107035, 0, 0, 0] := by
  decide +kernel

theorem rows4255 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4255 = true := by
  decide +kernel

theorem tot4255 : totK PA10K2 A10K2.t4255 = [0, 315335427872, 1107061063856, 1559055999756, 1308274623202, 520784406965, 48886019071, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

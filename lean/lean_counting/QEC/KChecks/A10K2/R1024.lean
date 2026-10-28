import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4096 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4096 = true := by
  decide +kernel

theorem tot4096 : totK PA10K2 A10K2.t4096 = [0, 297273774964, 1217007335069, 1900516380578, 1080966864241, 174361211873, 5546304973, 0, 0, 0] := by
  decide +kernel

theorem rows4097 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4097 = true := by
  decide +kernel

theorem tot4097 : totK PA10K2 A10K2.t4097 = [0, 441740864220, 1807240032450, 2081344396683, 560688700134, 17270578304, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4098 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4098 = true := by
  decide +kernel

theorem tot4098 : totK PA10K2 A10K2.t4098 = [582906374285, 1850617130310, 1652566489465, 533542122111, 223033191757, 37646807062, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4099 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4099 = true := by
  decide +kernel

theorem tot4099 : totK PA10K2 A10K2.t4099 = [214361781333, 1364646321089, 2294968076638, 1002037945343, 79341492360, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

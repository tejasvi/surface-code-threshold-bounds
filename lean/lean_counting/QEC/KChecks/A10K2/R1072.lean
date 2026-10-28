import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4288 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4288 = true := by
  decide +kernel

theorem tot4288 : totK PA10K2 A10K2.t4288 = [0, 321069671350, 1396271594597, 1981455465550, 1012507522749, 160460278124, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows4289 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4289 = true := by
  decide +kernel

theorem tot4289 : totK PA10K2 A10K2.t4289 = [0, 403256408763, 1628491658591, 1869081671059, 592727240497, 38180250037, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4290 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4290 = true := by
  decide +kernel

theorem tot4290 : totK PA10K2 A10K2.t4290 = [0, 113824625706, 854206648175, 2006966757930, 1360123554839, 207512986682, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows4291 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4291 = true := by
  decide +kernel

theorem tot4291 : totK PA10K2 A10K2.t4291 = [0, 581951428808, 1968732416146, 1883708862501, 488359928902, 25584519718, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

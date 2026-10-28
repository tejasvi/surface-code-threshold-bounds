import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4624 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4624 = true := by
  decide +kernel

theorem tot4624 : totK PA10K2 A10K2.t4624 = [0, 316661823121, 1111023662847, 1563007412852, 1389891667127, 522441368230, 48886019071, 0, 0, 0] := by
  decide +kernel

theorem rows4625 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4625 = true := by
  decide +kernel

theorem tot4625 : totK PA10K2 A10K2.t4625 = [0, 528909875718, 1836934419710, 1868915553976, 514515480146, 32207422962, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4626 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4626 = true := by
  decide +kernel

theorem tot4626 : totK PA10K2 A10K2.t4626 = [0, 0, 721537313672, 2107305918839, 1680769676248, 396610345279, 25680132735, 0, 0, 0] := by
  decide +kernel

theorem rows4627 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4627 = true := by
  decide +kernel

theorem tot4627 : totK PA10K2 A10K2.t4627 = [0, 251280892394, 1100940419623, 1900686156025, 1336115628421, 226622414750, 5626791703, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

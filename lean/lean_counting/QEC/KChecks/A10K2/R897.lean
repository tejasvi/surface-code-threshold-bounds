import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3588 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3588 = true := by
  decide +kernel

theorem tot3588 : totK PA10K2 A10K2.t3588 = [0, 0, 175023090004, 918389938929, 1930250715419, 1399438474346, 275750984080, 10760911071, 0, 0] := by
  decide +kernel

theorem rows3589 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3589 = true := by
  decide +kernel

theorem tot3589 : totK PA10K2 A10K2.t3589 = [0, 0, 524864841738, 1812181057254, 1838087882981, 516930762975, 31614405859, 0, 0, 0] := by
  decide +kernel

theorem rows3590 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3590 = true := by
  decide +kernel

theorem tot3590 : totK PA10K2 A10K2.t3590 = [0, 0, 39814905974, 1121278517666, 2339094526070, 1060684931813, 77248038420, 0, 0, 0] := by
  decide +kernel

theorem rows3591 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3591 = true := by
  decide +kernel

theorem tot3591 : totK PA10K2 A10K2.t3591 = [0, 0, 403089147566, 1419878414633, 1864317439540, 948616880645, 154481227852, 5705019915, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

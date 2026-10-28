import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1592 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1592 = true := by
  decide +kernel

theorem tot1592 : totK PA10K2 A10K2.t1592 = [0, 0, 580615297523, 1976219147029, 1793903286208, 419959332735, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows1593 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1593 = true := by
  decide +kernel

theorem tot1593 : totK PA10K2 A10K2.t1593 = [0, 345065522154, 1250261750425, 1787513618220, 1149801247185, 219284954381, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows1594 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1594 = true := by
  decide +kernel

theorem tot1594 : totK PA10K2 A10K2.t1594 = [0, 401413542662, 1750248072766, 1990583291857, 585840984758, 32877822373, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1595 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1595 = true := by
  decide +kernel

theorem tot1595 : totK PA10K2 A10K2.t1595 = [0, 0, 705616323467, 2217155019818, 1542779936465, 192419220631, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

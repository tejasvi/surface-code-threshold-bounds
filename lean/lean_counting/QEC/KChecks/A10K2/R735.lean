import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2940 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2940 = true := by
  decide +kernel

theorem tot2940 : totK PA10K2 A10K2.t2940 = [0, 0, 147677840622, 910928309918, 2034251297083, 1387615594666, 247739911599, 7007974415, 0, 0] := by
  decide +kernel

theorem rows2941 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2941 = true := by
  decide +kernel

theorem tot2941 : totK PA10K2 A10K2.t2941 = [0, 0, 537463049062, 2003397529134, 1926778482429, 427354145331, 17376508239, 0, 0, 0] := by
  decide +kernel

theorem rows2942 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2942 = true := by
  decide +kernel

theorem tot2942 : totK PA10K2 A10K2.t2942 = [0, 86476191967, 531689351414, 1681016795803, 2069934640349, 736651266024, 56820615133, 0, 0, 0] := by
  decide +kernel

theorem rows2943 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2943 = true := by
  decide +kernel

theorem tot2943 : totK PA10K2 A10K2.t2943 = [0, 438765155777, 1785074002075, 1959923054804, 519681221775, 26491486257, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

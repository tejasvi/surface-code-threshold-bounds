import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3752 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3752 = true := by
  decide +kernel

theorem tot3752 : totK PA10K2 A10K2.t3752 = [0, 0, 547635066067, 1644510865447, 1710938931684, 852260542708, 156776395770, 6354482628, 0, 0] := by
  decide +kernel

theorem rows3753 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3753 = true := by
  decide +kernel

theorem tot3753 : totK PA10K2 A10K2.t3753 = [0, 0, 45768258037, 923878308245, 2248725746146, 1597670213125, 266528207740, 6853348008, 0, 0] := by
  decide +kernel

theorem rows3754 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3754 = true := by
  decide +kernel

theorem tot3754 : totK PA10K2 A10K2.t3754 = [0, 0, 0, 500287578175, 1918715197593, 2015880244670, 518257222516, 31559907735, 0, 0] := by
  decide +kernel

theorem rows3755 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3755 = true := by
  decide +kernel

theorem tot3755 : totK PA10K2 A10K2.t3755 = [0, 0, 0, 598718041995, 2012539911268, 1891115636434, 401951438888, 12350643961, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3792 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3792 = true := by
  decide +kernel

theorem tot3792 : totK PA10K2 A10K2.t3792 = [0, 0, 425698745373, 1651966467538, 1925985527635, 632497110698, 52232171148, 0, 0, 0] := by
  decide +kernel

theorem rows3793 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3793 = true := by
  decide +kernel

theorem tot3793 : totK PA10K2 A10K2.t3793 = [0, 0, 276249092272, 1491582199603, 2039126827588, 766489542497, 54200973352, 0, 0, 0] := by
  decide +kernel

theorem rows3794 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3794 = true := by
  decide +kernel

theorem tot3794 : totK PA10K2 A10K2.t3794 = [0, 0, 0, 645934132202, 2129212827734, 1622841937543, 263743477462, 6354482628, 0, 0] := by
  decide +kernel

theorem rows3795 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3795 = true := by
  decide +kernel

theorem tot3795 : totK PA10K2 A10K2.t3795 = [0, 0, 0, 581321856993, 1971086358181, 1811682877118, 352795876070, 11740596405, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

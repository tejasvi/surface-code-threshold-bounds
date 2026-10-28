import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4100 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4100 = true := by
  decide +kernel

theorem tot4100 : totK PA10K2 A10K2.t4100 = [0, 486850035393, 1823185845087, 1886157774761, 487050250815, 30831673886, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4101 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4101 = true := by
  decide +kernel

theorem tot4101 : totK PA10K2 A10K2.t4101 = [469591264720, 1780539120748, 1898530584963, 607611035830, 59027763682, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4102 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4102 = true := by
  decide +kernel

theorem tot4102 : totK PA10K2 A10K2.t4102 = [109458229214, 648429608158, 1736341314250, 1678298066807, 468516693774, 31768748853, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4103 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4103 = true := by
  decide +kernel

theorem tot4103 : totK PA10K2 A10K2.t4103 = [481243211120, 1707614349644, 1861597207272, 638323985269, 52232171148, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

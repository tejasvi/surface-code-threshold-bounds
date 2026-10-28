import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7852 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7852 = true := by
  decide +kernel

theorem tot7852 : totK PA10K2 A10K2.t7852 = [0, 171753838140, 685492733443, 1628285740366, 1762409559681, 488996415002, 31889781550, 0, 0, 0] := by
  decide +kernel

theorem rows7853 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7853 = true := by
  decide +kernel

theorem tot7853 : totK PA10K2 A10K2.t7853 = [0, 416962992548, 1777290143936, 2181858911660, 712739373361, 32076087000, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7854 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7854 = true := by
  decide +kernel

theorem tot7854 : totK PA10K2 A10K2.t7854 = [0, 116150967364, 782906568356, 1983823392665, 1705224649787, 392338844875, 18342047509, 0, 0, 0] := by
  decide +kernel

theorem rows7855 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7855 = true := by
  decide +kernel

theorem tot7855 : totK PA10K2 A10K2.t7855 = [0, 494064620316, 1824522444239, 1954842977479, 545919735361, 32780555804, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

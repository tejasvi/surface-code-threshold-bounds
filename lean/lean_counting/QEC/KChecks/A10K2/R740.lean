import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2960 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2960 = true := by
  decide +kernel

theorem tot2960 : totK PA10K2 A10K2.t2960 = [0, 0, 583957149951, 1986456219742, 1851137717083, 400341550292, 12219140272, 0, 0, 0] := by
  decide +kernel

theorem rows2961 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2961 = true := by
  decide +kernel

theorem tot2961 : totK PA10K2 A10K2.t2961 = [0, 424089518694, 1564149442315, 2018482505245, 866693888924, 79347299132, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2962 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2962 = true := by
  decide +kernel

theorem tot2962 : totK PA10K2 A10K2.t2962 = [0, 467252897767, 1815560010584, 2081801313263, 670472617393, 30616275043, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2963 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2963 = true := by
  decide +kernel

theorem tot2963 : totK PA10K2 A10K2.t2963 = [0, 0, 665411090236, 2139157216573, 1823938150229, 326690386223, 6772895877, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t756 = true := by
  decide +kernel

theorem tot756 : totK PD2M8K2 D2M8K2.t756 = [0, 181693712562, 468414023296, 251221084845, 15284653421, 0, 0, 0] := by
  decide +kernel

theorem rows757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t757 = true := by
  decide +kernel

theorem tot757 : totK PD2M8K2 D2M8K2.t757 = [0, 0, 278212666714, 494786847840, 107852321722, 1242138600, 0, 0] := by
  decide +kernel

theorem rows758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t758 = true := by
  decide +kernel

theorem tot758 : totK PD2M8K2 D2M8K2.t758 = [0, 0, 177435023298, 470763340127, 201937694916, 8407946489, 0, 0] := by
  decide +kernel

theorem rows759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t759 = true := by
  decide +kernel

theorem tot759 : totK PD2M8K2 D2M8K2.t759 = [0, 175374446566, 426065420964, 204571318481, 74473555881, 12101082977, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

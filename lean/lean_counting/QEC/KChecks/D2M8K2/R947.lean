import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3788 = true := by
  decide +kernel

theorem tot3788 : totK PD2M8K2 D2M8K2.t3788 = [0, 188833719260, 465611451657, 246015077913, 18252358503, 0, 0, 0] := by
  decide +kernel

theorem rows3789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3789 = true := by
  decide +kernel

theorem tot3789 : totK PD2M8K2 D2M8K2.t3789 = [0, 33307713132, 350903911585, 418230158265, 67200751159, 1021600638, 0, 0] := by
  decide +kernel

theorem rows3790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3790 = true := by
  decide +kernel

theorem tot3790 : totK PD2M8K2 D2M8K2.t3790 = [0, 102701530919, 343030469022, 326350121739, 78464313329, 3552795014, 0, 0] := by
  decide +kernel

theorem rows3791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3791 = true := by
  decide +kernel

theorem tot3791 : totK PD2M8K2 D2M8K2.t3791 = [0, 177854461560, 450404177495, 257395634818, 25454216038, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

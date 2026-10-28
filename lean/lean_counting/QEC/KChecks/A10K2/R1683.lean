import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6732 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6732 = true := by
  decide +kernel

theorem tot6732 : totK PA10K2 A10K2.t6732 = [0, 947127149617, 2349133663092, 1311490283806, 142456931035, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6733 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6733 = true := by
  decide +kernel

theorem tot6733 : totK PA10K2 A10K2.t6733 = [0, 542065771667, 1865689845980, 1848929419039, 514476875153, 32470817489, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6734 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6734 = true := by
  decide +kernel

theorem tot6734 : totK PA10K2 A10K2.t6734 = [0, 496962462929, 1838481754027, 2044886788849, 561757291037, 32857666713, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6735 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6735 = true := by
  decide +kernel

theorem tot6735 : totK PA10K2 A10K2.t6735 = [0, 281368877072, 1491651306160, 2160737141048, 744463404431, 52333014080, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

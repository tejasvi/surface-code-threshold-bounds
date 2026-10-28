import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4444 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4444 = true := by
  decide +kernel

theorem tot4444 : totK PA10K2 A10K2.t4444 = [0, 0, 0, 687633310227, 2195805139927, 1656171216198, 284255735120, 6904928264, 0, 0] := by
  decide +kernel

theorem rows4445 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4445 = true := by
  decide +kernel

theorem tot4445 : totK PA10K2 A10K2.t4445 = [0, 0, 592981215928, 1949498450504, 1874822209818, 599160770305, 51460186275, 0, 0, 0] := by
  decide +kernel

theorem rows4446 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4446 = true := by
  decide +kernel

theorem tot4446 : totK PA10K2 A10K2.t4446 = [0, 0, 0, 817468785127, 2323505753485, 1649940016316, 230367304934, 6766355402, 0, 0] := by
  decide +kernel

theorem rows4447 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4447 = true := by
  decide +kernel

theorem tot4447 : totK PA10K2 A10K2.t4447 = [0, 0, 537487968785, 1837764576072, 1895300466989, 657878124637, 53316719757, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

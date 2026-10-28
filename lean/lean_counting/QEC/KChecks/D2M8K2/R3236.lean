import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12944 = true := by
  decide +kernel

theorem tot12944 : totK PD2M8K2 D2M8K2.t12944 = [0, 0, 0, 224215238870, 489936431959, 159077005850, 5159868635, 0] := by
  decide +kernel

theorem rows12945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12945 = true := by
  decide +kernel

theorem tot12945 : totK PD2M8K2 D2M8K2.t12945 = [0, 0, 177605389916, 453712630097, 277612995286, 30220848452, 0, 0] := by
  decide +kernel

theorem rows12946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12946 = true := by
  decide +kernel

theorem tot12946 : totK PD2M8K2 D2M8K2.t12946 = [0, 0, 184821240045, 464061950694, 239667741605, 16401272855, 0, 0] := by
  decide +kernel

theorem rows12947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12947 = true := by
  decide +kernel

theorem tot12947 : totK PD2M8K2 D2M8K2.t12947 = [0, 0, 189694427563, 457780258829, 241670159721, 22808743471, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

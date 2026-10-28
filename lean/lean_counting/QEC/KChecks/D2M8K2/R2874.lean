import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11496 = true := by
  decide +kernel

theorem tot11496 : totK PD2M8K2 D2M8K2.t11496 = [0, 122488084803, 333512713233, 291578948324, 138760757740, 11758933175, 0, 0] := by
  decide +kernel

theorem rows11497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11497 = true := by
  decide +kernel

theorem tot11497 : totK PD2M8K2 D2M8K2.t11497 = [0, 192294655536, 456016021181, 222008166195, 16983243438, 0, 0, 0] := by
  decide +kernel

theorem rows11498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11498 = true := by
  decide +kernel

theorem tot11498 : totK PD2M8K2 D2M8K2.t11498 = [0, 21840262052, 333065369605, 448267913685, 74250403852, 1209030869, 0, 0] := by
  decide +kernel

theorem rows11499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11499 = true := by
  decide +kernel

theorem tot11499 : totK PD2M8K2 D2M8K2.t11499 = [0, 104170550470, 382179944535, 384898881660, 50642630931, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

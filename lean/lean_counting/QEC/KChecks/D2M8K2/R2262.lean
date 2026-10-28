import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9048 = true := by
  decide +kernel

theorem tot9048 : totK PD2M8K2 D2M8K2.t9048 = [0, 0, 201489861184, 487861448347, 206006556391, 6521599928, 0, 0] := by
  decide +kernel

theorem rows9049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9049 = true := by
  decide +kernel

theorem tot9049 : totK PD2M8K2 D2M8K2.t9049 = [0, 109069041747, 312824761485, 364520644141, 134022431072, 6761411919, 0, 0] := by
  decide +kernel

theorem rows9050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9050 = true := by
  decide +kernel

theorem tot9050 : totK PD2M8K2 D2M8K2.t9050 = [0, 211242989466, 483137979191, 193461844622, 9932205546, 0, 0, 0] := by
  decide +kernel

theorem rows9051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9051 = true := by
  decide +kernel

theorem tot9051 : totK PD2M8K2 D2M8K2.t9051 = [0, 4187750769, 298552717144, 474954749230, 124127491872, 4143089693, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

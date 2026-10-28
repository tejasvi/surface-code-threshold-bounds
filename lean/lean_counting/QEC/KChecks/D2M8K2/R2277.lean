import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9108 = true := by
  decide +kernel

theorem tot9108 : totK PD2M8K2 D2M8K2.t9108 = [0, 79041962302, 289374277251, 391173201701, 136624863111, 2535105584, 0, 0] := by
  decide +kernel

theorem rows9109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9109 = true := by
  decide +kernel

theorem tot9109 : totK PD2M8K2 D2M8K2.t9109 = [0, 156324341247, 466511083190, 263388387380, 17226819813, 0, 0, 0] := by
  decide +kernel

theorem rows9110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9110 = true := by
  decide +kernel

theorem tot9110 : totK PD2M8K2 D2M8K2.t9110 = [0, 87580328350, 350828263336, 366985127337, 67088225823, 1070790515, 0, 0] := by
  decide +kernel

theorem rows9111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9111 = true := by
  decide +kernel

theorem tot9111 : totK PD2M8K2 D2M8K2.t9111 = [0, 84295801958, 300778661458, 397107714640, 96011642972, 3462014130, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

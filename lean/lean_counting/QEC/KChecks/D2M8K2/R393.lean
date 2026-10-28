import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1572 = true := by
  decide +kernel

theorem tot1572 : totK PD2M8K2 D2M8K2.t1572 = [0, 177577601885, 465069398866, 241919076474, 17111997474, 0, 0, 0] := by
  decide +kernel

theorem rows1573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1573 = true := by
  decide +kernel

theorem tot1573 : totK PD2M8K2 D2M8K2.t1573 = [0, 153942210003, 454506801698, 269130004663, 18952409942, 0, 0, 0] := by
  decide +kernel

theorem rows1574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1574 = true := by
  decide +kernel

theorem tot1574 : totK PD2M8K2 D2M8K2.t1574 = [0, 0, 270448053142, 508988477132, 112126844263, 1369150432, 0, 0] := by
  decide +kernel

theorem rows1575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1575 = true := by
  decide +kernel

theorem tot1575 : totK PD2M8K2 D2M8K2.t1575 = [0, 162528288142, 427643783772, 306100640134, 30659429742, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

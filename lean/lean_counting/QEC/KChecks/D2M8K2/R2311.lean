import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9244 = true := by
  decide +kernel

theorem tot9244 : totK PD2M8K2 D2M8K2.t9244 = [0, 156402402365, 481435096661, 260002437943, 11797910977, 0, 0, 0] := by
  decide +kernel

theorem rows9245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9245 = true := by
  decide +kernel

theorem tot9245 : totK PD2M8K2 D2M8K2.t9245 = [0, 189097790349, 451995795717, 228106615419, 21431496195, 0, 0, 0] := by
  decide +kernel

theorem rows9246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9246 = true := by
  decide +kernel

theorem tot9246 : totK PD2M8K2 D2M8K2.t9246 = [0, 196845952906, 474985391080, 213121358559, 12183533023, 0, 0, 0] := by
  decide +kernel

theorem rows9247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9247 = true := by
  decide +kernel

theorem tot9247 : totK PD2M8K2 D2M8K2.t9247 = [0, 37651867065, 323110031673, 422077366673, 84814258277, 1162935789, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

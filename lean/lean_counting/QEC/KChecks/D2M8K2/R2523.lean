import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10092 = true := by
  decide +kernel

theorem tot10092 : totK PD2M8K2 D2M8K2.t10092 = [0, 162263604823, 454606576877, 277602246109, 21937312222, 0, 0, 0] := by
  decide +kernel

theorem rows10093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10093 = true := by
  decide +kernel

theorem tot10093 : totK PD2M8K2 D2M8K2.t10093 = [0, 171427883566, 468256669792, 253661425535, 17102514199, 0, 0, 0] := by
  decide +kernel

theorem rows10094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10094 = true := by
  decide +kernel

theorem tot10094 : totK PD2M8K2 D2M8K2.t10094 = [0, 0, 179520402512, 443898882777, 256423538873, 25364689049, 0, 0] := by
  decide +kernel

theorem rows10095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10095 = true := by
  decide +kernel

theorem tot10095 : totK PD2M8K2 D2M8K2.t10095 = [0, 0, 210487535541, 489857616197, 194433577150, 5430665091, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

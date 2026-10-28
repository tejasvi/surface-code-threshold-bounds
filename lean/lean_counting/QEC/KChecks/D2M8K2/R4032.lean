import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16128 = true := by
  decide +kernel

theorem tot16128 : totK PD2M8K2 D2M8K2.t16128 = [0, 90035073316, 223834760401, 171796839476, 256372471264, 133026716877, 8063697217, 0] := by
  decide +kernel

theorem rows16129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16129 = true := by
  decide +kernel

theorem tot16129 : totK PD2M8K2 D2M8K2.t16129 = [0, 201053963721, 456353454786, 221030235840, 15260096069, 0, 0, 0] := by
  decide +kernel

theorem rows16130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16130 = true := by
  decide +kernel

theorem tot16130 : totK PD2M8K2 D2M8K2.t16130 = [0, 116092385875, 419909828296, 310771652453, 29299576977, 0, 0, 0] := by
  decide +kernel

theorem rows16131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16131 = true := by
  decide +kernel

theorem tot16131 : totK PD2M8K2 D2M8K2.t16131 = [0, 0, 278863488221, 506978209991, 104674904210, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

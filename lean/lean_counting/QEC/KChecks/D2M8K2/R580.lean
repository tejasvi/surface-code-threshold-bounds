import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2320 = true := by
  decide +kernel

theorem tot2320 : totK PD2M8K2 D2M8K2.t2320 = [0, 0, 211833702319, 471486368739, 212216279233, 12089498654, 0, 0] := by
  decide +kernel

theorem rows2321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2321 = true := by
  decide +kernel

theorem tot2321 : totK PD2M8K2 D2M8K2.t2321 = [0, 0, 159025326867, 443480126210, 276184144635, 28781449804, 0, 0] := by
  decide +kernel

theorem rows2322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2322 = true := by
  decide +kernel

theorem tot2322 : totK PD2M8K2 D2M8K2.t2322 = [0, 0, 87395272022, 436693759777, 354805645641, 27677924158, 0, 0] := by
  decide +kernel

theorem rows2323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2323 = true := by
  decide +kernel

theorem tot2323 : totK PD2M8K2 D2M8K2.t2323 = [0, 0, 49445055852, 308530140744, 435743594470, 97742679409, 1547833102, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

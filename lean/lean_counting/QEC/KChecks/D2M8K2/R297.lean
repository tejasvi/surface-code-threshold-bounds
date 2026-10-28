import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1188 = true := by
  decide +kernel

theorem tot1188 : totK PD2M8K2 D2M8K2.t1188 = [124502080051, 438357872463, 313303520499, 26205595598, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1189 = true := by
  decide +kernel

theorem tot1189 : totK PD2M8K2 D2M8K2.t1189 = [0, 200714186196, 482349801990, 190092619287, 9668735432, 0, 0, 0] := by
  decide +kernel

theorem rows1190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1190 = true := by
  decide +kernel

theorem tot1190 : totK PD2M8K2 D2M8K2.t1190 = [87343538873, 328687384025, 363411111312, 103104036020, 3581949829, 0, 0, 0] := by
  decide +kernel

theorem rows1191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1191 = true := by
  decide +kernel

theorem tot1191 : totK PD2M8K2 D2M8K2.t1191 = [173450039620, 460609850031, 243996574897, 17104814242, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

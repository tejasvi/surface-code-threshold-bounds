import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1936 = true := by
  decide +kernel

theorem tot1936 : totK PD2M8K2 D2M8K2.t1936 = [0, 0, 179200246743, 480970334900, 241636031522, 11458389563, 0, 0] := by
  decide +kernel

theorem rows1937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1937 = true := by
  decide +kernel

theorem tot1937 : totK PD2M8K2 D2M8K2.t1937 = [0, 0, 201205687851, 484099115142, 213352082414, 10519017088, 0, 0] := by
  decide +kernel

theorem rows1938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1938 = true := by
  decide +kernel

theorem tot1938 : totK PD2M8K2 D2M8K2.t1938 = [0, 0, 174365377444, 446685432155, 263640625393, 20643165170, 0, 0] := by
  decide +kernel

theorem rows1939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1939 = true := by
  decide +kernel

theorem tot1939 : totK PD2M8K2 D2M8K2.t1939 = [0, 0, 122783542105, 447150713692, 309478557745, 24833991578, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

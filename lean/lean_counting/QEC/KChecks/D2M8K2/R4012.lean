import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16048 = true := by
  decide +kernel

theorem tot16048 : totK PD2M8K2 D2M8K2.t16048 = [0, 0, 0, 233304848243, 508715947540, 141189672728, 5172807878, 0] := by
  decide +kernel

theorem rows16049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16049 = true := by
  decide +kernel

theorem tot16049 : totK PD2M8K2 D2M8K2.t16049 = [0, 0, 171310374970, 456687716178, 255430741008, 24166939424, 0, 0] := by
  decide +kernel

theorem rows16050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16050 = true := by
  decide +kernel

theorem tot16050 : totK PD2M8K2 D2M8K2.t16050 = [0, 0, 161625269971, 423949756221, 279998763917, 30789805341, 0, 0] := by
  decide +kernel

theorem rows16051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16051 = true := by
  decide +kernel

theorem tot16051 : totK PD2M8K2 D2M8K2.t16051 = [0, 0, 89753051296, 367688189257, 366148092551, 66339803231, 1198073392, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13404 = true := by
  decide +kernel

theorem tot13404 : totK PD2M8K2 D2M8K2.t13404 = [0, 0, 0, 284350978755, 499883566702, 101023027768, 1096505104, 0] := by
  decide +kernel

theorem rows13405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13405 = true := by
  decide +kernel

theorem tot13405 : totK PD2M8K2 D2M8K2.t13405 = [0, 0, 167878671790, 374138520051, 259449584891, 82590118924, 3884009855, 0] := by
  decide +kernel

theorem rows13406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13406 = true := by
  decide +kernel

theorem tot13406 : totK PD2M8K2 D2M8K2.t13406 = [0, 0, 153433715120, 486398921492, 232929309058, 9406285386, 0, 0] := by
  decide +kernel

theorem rows13407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13407 = true := by
  decide +kernel

theorem tot13407 : totK PD2M8K2 D2M8K2.t13407 = [0, 0, 0, 337259257958, 464416218121, 65675325312, 1268739303, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

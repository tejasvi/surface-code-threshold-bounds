import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9404 = true := by
  decide +kernel

theorem tot9404 : totK PD2M8K2 D2M8K2.t9404 = [0, 178217708811, 465024640143, 261468392079, 19361031963, 0, 0, 0] := by
  decide +kernel

theorem rows9405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9405 = true := by
  decide +kernel

theorem tot9405 : totK PD2M8K2 D2M8K2.t9405 = [0, 0, 261976143434, 509572766478, 119436940540, 1210106048, 0, 0] := by
  decide +kernel

theorem rows9406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9406 = true := by
  decide +kernel

theorem tot9406 : totK PD2M8K2 D2M8K2.t9406 = [0, 140820495039, 381452781358, 298238851739, 75474762672, 3724448267, 0, 0] := by
  decide +kernel

theorem rows9407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9407 = true := by
  decide +kernel

theorem tot9407 : totK PD2M8K2 D2M8K2.t9407 = [0, 179399476729, 444573205822, 233589497255, 17115888737, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

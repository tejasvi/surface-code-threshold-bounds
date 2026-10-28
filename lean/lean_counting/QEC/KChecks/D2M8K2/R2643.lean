import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10572 = true := by
  decide +kernel

theorem tot10572 : totK PD2M8K2 D2M8K2.t10572 = [0, 0, 218596033028, 487363342501, 202008912039, 7987396625, 0, 0] := by
  decide +kernel

theorem rows10573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10573 = true := by
  decide +kernel

theorem tot10573 : totK PD2M8K2 D2M8K2.t10573 = [0, 122840566998, 351814668555, 337585375169, 89560062405, 1409560813, 0, 0] := by
  decide +kernel

theorem rows10574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10574 = true := by
  decide +kernel

theorem tot10574 : totK PD2M8K2 D2M8K2.t10574 = [0, 163921375510, 447789065515, 273975548726, 29874439746, 0, 0, 0] := by
  decide +kernel

theorem rows10575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10575 = true := by
  decide +kernel

theorem tot10575 : totK PD2M8K2 D2M8K2.t10575 = [0, 135154574949, 446606129073, 297011779057, 21704798952, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

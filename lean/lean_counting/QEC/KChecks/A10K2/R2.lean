import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8 = true := by
  decide +kernel

theorem tot8 : totK PA10K2 A10K2.t8 = [0, 454199877451, 1728584823613, 2052725889315, 704904599382, 54582742957, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t9 = true := by
  decide +kernel

theorem tot9 : totK PA10K2 A10K2.t9 = [0, 450637712680, 1790206600483, 1949397619461, 508539538633, 31222411477, 0, 0, 0, 0] := by
  decide +kernel

theorem rows10 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t10 = true := by
  decide +kernel

theorem tot10 : totK PA10K2 A10K2.t10 = [0, 264049595504, 1368799928106, 2125345331844, 1071651820076, 131310609976, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t11 = true := by
  decide +kernel

theorem tot11 : totK PA10K2 A10K2.t11 = [0, 112706332773, 682702095233, 1797547955328, 1557965335156, 418492310864, 30650496230, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
